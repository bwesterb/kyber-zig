const std = @import("std");

const testing = std.testing;
const assert = std.debug.assert;
const RndGen = std.rand.DefaultPrng;
const sha3 = std.crypto.hash.sha3;

// Q is the parameter q ≡ 3329 = 2¹¹ + 2¹⁰ + 2⁸ + 1.
const Q: i16 = 3329;

// Montgomery R
const R: i32 = 1 << 16;

// Parameter n, degree of polynomials.
const N: i32 = 256;

const Params = struct {
    // Width and height of the matrix A.
    k: u8,

    // Size of "small" vectors used in noise vector for encryption.
    eta1: u8,

    // How many bits to retain of u, the private-key independent part
    // of the ciphertext.
    du: u8,

    // How many bits to retain of v, the private-key dependent part
    // of the ciphertext.
    dv: u8,
};

const Kyber512: Params = .{
    .k = 2,
    .eta1 = 3,
    .du = 10,
    .dv = 4,
};

const Kyber768: Params = .{
    .k = 3,
    .eta1 = 2,
    .du = 10,
    .dv = 4,
};

const Kyber1024: Params = .{
    .k = 4,
    .eta1 = 2,
    .du = 11,
    .dv = 5,
};

// R mod q
const RModQ: i32 = @rem(@as(i32, R), Q);

// R² mod q
const R2ModQ: i32 = @rem(RModQ * RModQ, Q);

// ζ is the degree 256 primitive root of unity used for the NTT.
const zeta: i16 = 17;

// (128)⁻¹ R². Used in inverse NTT.
const R2over128: i32 = @mod(invertMod(128, Q) * R2ModQ, Q);

// zetas lists precomputed powers of the primitive root of unity in
// Montgomery representation used for the NTT:
//
//  zetas[i] = ζᵇʳᵛ⁽ⁱ⁾ R mod q
//
// where ζ = 17, brv(i) is the bitreversal of a 7-bit number and R=2¹⁶ mod q.
const zetas: [128]i16 = computeZetas();

// invNTTReductions keeps track of which coefficients to apply Barrett
// reduction to in Poly.invNTT().
//
// Generated lazily: once a butterfly is computed which is about to
// overflow the i16, the largest coefficient is reduced.  If that is
// not enough, the other coefficient is reduced as well.
//
// This is actually optimal, as proven in https://eprint.iacr.org/2020/1377.pdf
var invNTTReductions = [_]i16{
    -1, // after layer 1
    -1, // after layer 2
    16,
    17,
    48,
    49,
    80,
    81,
    112,
    113,
    144,
    145,
    176,
    177,
    208,
    209,
    240, 241, -1, // after layer 3
    0,   1,   32,
    33,  34,  35,
    64,  65,  96,
    97,  98,  99,
    128, 129,
    160, 161, 162, 163, 192, 193, 224, 225, 226, 227, -1, // after layer 4
    2,   3,   66,  67,  68,  69,  70,  71,  130, 131, 194,
    195, 196, 197,
    198, 199, -1, // after layer 5
    4,   5,   6,
    7,   132, 133,
    134, 135, 136,
    137, 138, 139,
    140, 141,
    142, 143, -1, // after layer 6
    -1, //  after layer 7
};

test "invNTTReductions bounds" {
    // Checks whether the reductions proposed by invNTTReductions
    // don't overflow during invNTT().
    var xs: [256]i32 = undefined;
    var i: usize = 0;
    while (i < N) : (i += 1) {
        xs[i] = 1; // start at |x| ≤ q
    }

    var r: usize = 0;
    var layer: u6 = 1;
    while (layer < 8) : (layer += 1) {
        var w: usize = @as(usize, 1) << layer;
        i = 0;

        while (i + w < 256) {
            xs[i] = xs[i] + xs[i + w];
            try testing.expect(xs[i] <= 9); // we can't exceed 9q
            xs[i + w] = 1;
            i += 1;
            if (@mod(i, w) == 0) {
                i += w;
            }
        }

        while (true) {
            var j: i16 = invNTTReductions[r];
            r += 1;
            if (j < 0) {
                break;
            }
            xs[@intCast(usize, j)] = 1;
        }
    }
}

// Extended euclidean algorithm.
//
// For a, b finds x, y such that  x a + y b = gcd(a, b). Used to compute
// modular inverse.
fn eea(a: anytype, b: @TypeOf(a)) eeaResult(@TypeOf(a)) {
    if (a == 0) {
        return .{ .gcd = b, .x = 0, .y = 1 };
    }
    const r = eea(@rem(b, a), a);
    return .{ .gcd = r.gcd, .x = r.y - @divTrunc(b, a) * r.x, .y = r.x };
}

fn eeaResult(comptime T: type) type {
    return struct { gcd: T, x: T, y: T };
}

// Returns least common multiple of a and b.
fn lcm(a: anytype, b: @TypeOf(a)) @TypeOf(a) {
    const r = eea(a, b);
    return a * b / r.gcd;
}

// Invert modulo p.
fn invertMod(a: anytype, p: @TypeOf(a)) @TypeOf(a) {
    const r = eea(a, p);
    assert(r.gcd == 1);
    return r.x;
}

// Reduce mod q for testing.
fn modQ32(x: i32) i16 {
    var y: i16 = @intCast(i16, @rem(x, @as(i32, Q)));
    if (y < 0) {
        y += Q;
    }
    return y;
}

// Given -2¹⁵ q ≤ x < 2¹⁵ q, returns -q < y < q with x 2⁻¹⁶ = y (mod q).
fn montReduce(x: i32) i16 {
    const qInv = comptime invertMod(@as(i32, Q), R);
    // This is Montgomery reduction with R=2¹⁶.
    //
    // Note gcd(2¹⁶, q) = 1 as q is prime.  Write q' := 62209 = q⁻¹ mod R.
    // First we compute
    //
    //	m := ((x mod R) q') mod R
    //         = x q' mod R
    //	   = int16(x q')
    //	   = int16(int32(x) * int32(q'))
    //
    // Note that x q' might be as big as 2³² and could overflow the int32
    // multiplication in the last line.  However for any int32s a and b,
    // we have int32(int64(a)*int64(b)) = int32(a*b) and so the result is ok.
    const m: i16 = @truncate(i16, @truncate(i32, x *% qInv));

    // Note that x - m q is divisable by R; indeed modulo R we have
    //
    //  x - m q ≡ x - x q' q ≡ x - x q⁻¹ q ≡ x - x = 0.
    //
    // We return y := (x - m q) / R.  Note that y is indeed correct as
    // modulo q we have
    //
    //  y ≡ x R⁻¹ - m q R⁻¹ = x R⁻¹
    //
    // and as both 2¹⁵ q ≤ m q, x < 2¹⁵ q, we have
    // 2¹⁶ q ≤ x - m q < 2¹⁶ and so q ≤ (x - m q) / R < q as desired.
    const yR = x - @as(i32, m) * @as(i32, Q);
    return @bitCast(i16, @truncate(u16, @bitCast(u32, yR) >> 16));
}

test "Test montReduce" {
    var rnd = RndGen.init(0);
    var i: i32 = 0;
    while (i <= 1000) : (i += 1) {
        const bound: i32 = comptime @as(i32, Q) * (1 << 15);
        const x: i32 = rnd.random().intRangeLessThan(i32, -bound, bound);
        const y: i16 = montReduce(x);
        try testing.expect(-Q < y and y < Q);
        try testing.expectEqual(modQ32(x), modQ32(@as(i32, y) * R));
    }
}

// Given any x, return x R mod q where R=2¹⁶.
fn feToMont(x: i16) i16 {
    // Note |1353 x| ≤ 1353 2¹⁵ ≤ 13318 q ≤ 2¹⁵ q and so we're within
    // the bounds of montReduce.
    return montReduce(@as(i32, x) * R2ModQ);
}

test "Test feToMont" {
    var x: i32 = -(1 << 15);
    while (x < 1 << 15) : (x += 1) {
        const y: i16 = feToMont(@intCast(i16, x));
        try testing.expectEqual(modQ32(@as(i32, y)), modQ32(x * RModQ));
    }
}

// Given any x, compute 0 ≤ y ≤ q with x = y (mod q).
//
// Beware: we might have feBarrettReduce(x) = q ≠ 0 for some x.  In fact,
// this happens if and only if x = -nq for some positive integer n.
fn feBarrettReduce(x: i16) i16 {
    // This is standard Barrett reduction.
    //
    // For any x we have x mod q = x - ⌊x/q⌋ q.  We will use 20159/2²⁶ as
    // an approximation of 1/q. Note that  0 ≤ 20159/2²⁶ - 1/q ≤ 0.135/2²⁶
    // and so | x 20156/2²⁶ - x/q | ≤ 2⁻¹⁰ for |x| ≤ 2¹⁶.  For all x
    // not a multiple of q, the number x/q is further than 1/q from any integer
    // and so ⌊x 20156/2²⁶⌋ = ⌊x/q⌋.  If x is a multiple of q and x is positive,
    // then x 20156/2²⁶ is larger than x/q so ⌊x 20156/2²⁶⌋ = ⌊x/q⌋ as well.
    // Finally, if x is negative multiple of q, then ⌊x 20156/2²⁶⌋ = ⌊x/q⌋-1.
    // Thus
    //                        [ q        if x=-nq for pos. integer n
    //  x - ⌊x 20156/2²⁶⌋ q = [
    //                        [ x mod q  otherwise
    //
    // To actually compute this, note that
    //
    //  ⌊x 20156/2²⁶⌋ = (20159 x) >> 26.
    return x -% @intCast(i16, (@as(i32, x) * 20159) >> 26) *% Q;
}

test "Test Barrett reduction" {
    var x: i32 = -(1 << 15);
    while (x < 1 << 15) : (x += 1) {
        var y1: i16 = feBarrettReduce(@intCast(i16, x));
        var y2: i16 = @mod(@intCast(i16, x), Q);
        if (x < 0 and @rem(-x, Q) == 0) {
            y1 -= Q;
        }
        try testing.expectEqual(y1, y2);
    }
}

// Returns x if x < q and x - q otherwise.  Assumes x ≥ -29439.
fn csubq(x: i16) i16 {
    var r = x;
    r -= Q;
    r += (r >> 15) & Q;
    return r;
}

test "Test csubq" {
    var x: i32 = -29439;
    while (x < 1 << 15) : (x += 1) {
        var y1: i16 = csubq(@intCast(i16, x));
        var y2: i16 = @intCast(i16, x);
        if (@intCast(i16, x) >= Q) {
            y2 -= Q;
        }
        try testing.expectEqual(y1, y2);
    }
}

// Bitreversal.
fn brv(a: anytype, comptime n: i8) @TypeOf(a) {
    var b = a;
    var ret: @TypeOf(a) = 0;
    comptime var i = 0;
    inline while (i < n) : (i += 1) {
        ret = (ret << 1) | (b & 1);
        b >>= 1;
    }
    return ret;
}

// Compute a^s mod p.
fn mpow(a: anytype, s: @TypeOf(a), p: @TypeOf(a)) @TypeOf(a) {
    var ret: @TypeOf(a) = 1;
    var s2 = s;
    var a2 = a;

    while (true) {
        if (s2 & 1 == 1) {
            ret = @mod(ret * a2, p);
        }
        s2 >>= 1;
        if (s2 == 0) {
            return ret;
        }
        a2 = @mod(a2 * a2, p);
    }
}

// Computes zetas table used by ntt and invNTT.
fn computeZetas() [128]i16 {
    @setEvalBranchQuota(10000);
    var ret: [128]i16 = undefined;
    var i: i32 = 0;
    while (i < 128) : (i += 1) {
        const t = @intCast(i16, mpow(@as(i32, zeta), brv(i, 7), Q));
        ret[@intCast(usize, i)] = csubq(feBarrettReduce(feToMont(t)));
    }
    return ret;
}

// An element of our base ring R which are polynomials over ℤ_q
// modulo the equation Xᴺ = -1, where q=3329 and N=256.
//
// This type is also used to store NTT-transformed polynomials,
// see Poly.NTT().
//
// Coefficients aren't always reduced.  See Normalize().
const Poly = struct {
    cs: [N]i16,

    fn add(a: Poly, b: Poly) Poly {
        var ret: Poly = undefined;
        var i = 0;
        while (i < N) : (i += 1) {
            ret.cs[i] = a.cs[i] + b.cs[i];
        }
        return ret;
    }

    fn sub(a: Poly, b: Poly) Poly {
        var ret: Poly = undefined;
        var i = 0;
        while (i < N) : (i += 1) {
            ret.cs[i] = a.cs[i] - b.cs[i];
        }
        return ret;
    }

    // For testing, generates a random polynomial with for each
    // coefficient |x| ≤ q.
    fn randAbsLeqQ(rnd: anytype) Poly {
        var ret: Poly = undefined;
        var i: usize = 0;
        while (i < N) : (i += 1) {
            ret.cs[i] = rnd.random().intRangeAtMost(i16, -Q, Q);
        }
        return ret;
    }

    // For testing, generates a random normalized polynomial.
    fn randNormalized(rnd: anytype) Poly {
        var ret: Poly = undefined;
        var i: usize = 0;
        while (i < N) : (i += 1) {
            ret.cs[i] = rnd.random().intRangeLessThan(i16, 0, Q);
        }
        return ret;
    }

    // Executes a forward "NTT" on p.
    //
    // Assumes the coefficients are in absolute value ≤q.  The resulting
    // coefficients are in absolute value ≤7q.  If the input is in Montgomery
    // form, then the result is in Montgomery form and so (by linearity of the NTT)
    // if the input is in regular form, then the result is also in regular form.
    fn ntt(a: Poly) Poly {
        // Note that ℤ_q does not have a primitive 512ᵗʰ root of unity (as 512
        // does not divide into q-1) and so we cannot do a regular NTT.  ℤ_q
        // does have a primitive 256ᵗʰ root of unity, the smallest of which
        // is ζ := 17.
        //
        // Recall that our base ring R := ℤ_q[x] / (x²⁵⁶ + 1).  The polynomial
        // x²⁵⁶+1 will not split completely (as its roots would be 512ᵗʰ roots
        // of unity.)  However, it does split almost (using ζ¹²⁸ = -1):
        //
        // x²⁵⁶ + 1 = (x²)¹²⁸ - ζ¹²⁸
        //          = ((x²)⁶⁴ - ζ⁶⁴)((x²)⁶⁴ + ζ⁶⁴)
        //          = ((x²)³² - ζ³²)((x²)³² + ζ³²)((x²)³² - ζ⁹⁶)((x²)³² + ζ⁹⁶)
        //          ⋮
        //          = (x² - ζ)(x² + ζ)(x² - ζ⁶⁵)(x² + ζ⁶⁵) … (x² + ζ¹²⁷)
        //
        // Note that the powers of ζ that appear (from the second line down) are
        // in binary
        //
        // 0100000 1100000
        // 0010000 1010000 0110000 1110000
        // 0001000 1001000 0101000 1101000 0011000 1011000 0111000 1111000
        //         …
        //
        // That is: brv(2), brv(3), brv(4), …, where brv(x) denotes the 7-bit
        // bitreversal of x.  These powers of ζ are given by the Zetas array.
        //
        // The polynomials x² ± ζⁱ are irreducible and coprime, hence by
        // the Chinese Remainder Theorem we know
        //
        //  ℤ_q[x]/(x²⁵⁶+1) → ℤ_q[x]/(x²-ζ) x … x  ℤ_q[x]/(x²+ζ¹²⁷)
        //
        // given by a ↦ ( a mod x²-ζ, …, a mod x²+ζ¹²⁷ )
        // is an isomorphism, which is the "NTT".  It can be efficiently computed by
        //
        //
        //  a ↦ ( a mod (x²)⁶⁴ - ζ⁶⁴, a mod (x²)⁶⁴ + ζ⁶⁴ )
        //    ↦ ( a mod (x²)³² - ζ³², a mod (x²)³² + ζ³²,
        //        a mod (x²)⁹⁶ - ζ⁹⁶, a mod (x²)⁹⁶ + ζ⁹⁶ )
        //
        //      et cetera
        // If N was 8 then this can be pictured in the following diagram:
        //
        //  https://cnx.org/resources/17ee4dfe517a6adda05377b25a00bf6e6c93c334/File0026.png
        //
        // Each cross is a Cooley-Tukey butterfly: it's the map
        //
        //  (a, b) ↦ (a + ζb, a - ζb)
        //
        // for the appropriate power ζ for that column and row group.
        var p = a;
        var k: usize = 0; // index into zetas

        var l: usize = N >> 1;
        while (l > 1) : (l >>= 1) {
            // On the nᵗʰ iteration of the l-loop, the absolute value of the
            // coefficients are bounded by nq.

            // offset effectively loops over the row groups in this column; it is
            // the first row in the row group.
            var offset: usize = 0;
            while (offset < N - l) : (offset += 2 * l) {
                k += 1;
                var z: i32 = @as(i32, zetas[k]);

                // j loops over each butterfly in the row group.
                var j: usize = offset;
                while (j < offset + l) : (j += 1) {
                    const t = montReduce(z * @as(i32, p.cs[j + l]));
                    p.cs[j + l] = p.cs[j] - t;
                    p.cs[j] += t;
                }
            }
        }

        return p;
    }

    // Executes an inverse "NTT" on p and multiply by the Montgomery factor R.
    //
    // Assumes the coefficients are in absolute value ≤q.  The resulting
    // coefficients are in absolute value ≤q.  If the input is in Montgomery
    // form, then the result is in Montgomery form and so (by linearity)
    // if the input is in regular form, then the result is also in regular form.
    fn invNTT(a: Poly) Poly {
        var k: usize = 127; // index into zetas
        var r: usize = 0; // index into invNTTReductions
        var p = a;

        // We basically do the oppposite of NTT, but postpone dividing by 2 in the
        // inverse of the Cooley-Tukey butterfly and accumulate that into a big
        // division by 2⁷ at the end.  See the comments in the ntt() function.

        var l: usize = 2;
        while (l < N) : (l <<= 1) {
            var offset: usize = 0;
            while (offset < N - l) : (offset += 2 * l) {
                // As we're inverting, we need powers of ζ⁻¹ (instead of ζ).
                // To be precise, we need ζᵇʳᵛ⁽ᵏ⁾⁻¹²⁸. However, as ζ⁻¹²⁸ = -1,
                // we can use the existing zetas table instead of
                // keeping a separate invZetas table as in Dilithium.

                var minZeta = @as(i32, zetas[k]);
                k -= 1;

                var j = offset;
                while (j < offset + l) : (j += 1) {
                    // Gentleman-Sande butterfly: (a, b) ↦ (a + b, ζ(a-b))
                    const t = p.cs[j + l] - p.cs[j];
                    p.cs[j] += p.cs[j + l];
                    p.cs[j + l] = montReduce(minZeta * @as(i32, t));

                    // Note that if we had |a| < αq and |b| < βq before the
                    // butterfly, then now we have |a| < (α+β)q and |b| < q.
                }
            }

            // We let the invNTTReductions instruct us which coefficients to
            // Barrett reduce.
            while (true) {
                var i = invNTTReductions[r];
                r += 1;
                if (i < 0) {
                    break;
                }
                p.cs[@intCast(usize, i)] = feBarrettReduce(p.cs[@intCast(usize, i)]);
            }
        }

        var j: usize = 0;
        while (j < N) : (j += 1) {
            // Note 1441 = (128)⁻¹ R².  The coefficients are bounded by 9q, so
            // as 1441 * 9 ≈ 2¹⁴ < 2¹⁵, we're within the required bounds
            // for montReduce().
            p.cs[j] = montReduce(R2over128 * @as(i32, p.cs[j]));
        }

        return p;
    }

    // Normalizes coefficients.
    //
    // Ensures each coefficient is in {0, …, q-1}.
    fn normalize(a: Poly) Poly {
        var ret: Poly = undefined;
        var i: usize = 0;
        while (i < N) : (i += 1) {
            ret.cs[i] = csubq(feBarrettReduce(a.cs[i]));
        }
        return ret;
    }

    // Put p in Montgomery form.
    fn toMont(a: Poly) Poly {
        var ret: Poly = undefined;
        var i: usize = 0;
        while (i < N) : (i += 1) {
            ret.cs[i] = feToMont(a.cs[i]);
        }
        return ret;
    }

    // Barret reduce coefficients.
    //
    // Beware, this does not fully normalize coefficients.
    fn barrettReduce(a: Poly) Poly {
        var ret: Poly = undefined;
        var i: usize = 0;
        while (i < N) : (i += 1) {
            ret.cs[i] = feBarrettReduce(a.cs[i]);
        }
        return ret;
    }

    // Returns packed Compress_q(p, d).
    //
    // Assumes p is normalized.
    fn compress(p: Poly, comptime d: u8) [@divTrunc(N * d, 8)]u8 {
        @setEvalBranchQuota(10000);
        const Qover2: u32 = comptime @divTrunc(Q, 2); // (q-1)/2
        const twoDm1: u32 = comptime (1 << d) - 1; // 2ᵈ-1
        var inOff: usize = 0;
        var outOff: usize = 0;

        const batchSize: usize = comptime lcm(@as(i16, d), 8);
        const inBatchSize: usize = comptime batchSize / d;
        const outBatchSize: usize = comptime batchSize / 8;

        const outLen: usize = comptime @divTrunc(N * d, 8);
        comptime assert(outLen * 8 == d * N);
        var out = std.mem.zeroes([outLen]u8);

        while (inOff < N) {
            // First we compress into in.
            var in: [inBatchSize]u16 = undefined;
            comptime var i: usize = 0;
            inline while (i < inBatchSize) : (i += 1) {
                // Compress_q(x, d) = ⌈(2ᵈ/q)x⌋ mod⁺ 2ᵈ
                //                  = ⌊(2ᵈ/q)x+½⌋ mod⁺ 2ᵈ
                //                  = ⌊((x << d) + q/2) / q⌋ mod⁺ 2ᵈ
                //                  = DIV((x << d) + q/2, q) & ((1<<d) - 1)
                const t = @intCast(u32, p.cs[inOff + i]) << d;
                in[i] = @intCast(u16, @divFloor(t + Qover2, Q) & twoDm1);
            }

            // Now we pack the d-bit integers from `in' into out as bytes.
            comptime var inShift: usize = 0;
            comptime var j: usize = 0;
            i = 0;
            inline while (i < inBatchSize) : (j += 1) {
                comptime var todo: usize = 8;
                inline while (todo > 0) {
                    const outShift: usize = comptime 8 - todo;
                    out[outOff + j] |= @truncate(u8, (in[i] >> inShift) << outShift);

                    const done: usize = comptime @min(@min(d, todo), d - inShift);
                    todo -= done;
                    inShift += done;

                    if (inShift == d) {
                        inShift = 0;
                        i += 1;
                    }
                }
            }

            inOff += inBatchSize;
            outOff += outBatchSize;
        }

        return out;
    }

    // Set p to Decompress_q(m, d).
    fn decompress(comptime d: u8, in: [@divTrunc(N * d, 8)]u8) Poly {
        @setEvalBranchQuota(10000);
        const inLen: usize = comptime @divTrunc(N * d, 8);
        comptime assert(inLen * 8 == d * N);
        var ret: Poly = undefined;
        var inOff: usize = 0;
        var outOff: usize = 0;

        const batchSize: usize = comptime lcm(@as(i16, d), 8);
        const inBatchSize: usize = comptime batchSize / 8;
        const outBatchSize: usize = comptime batchSize / d;

        while (outOff < N) {
            comptime var inShift: usize = 0;
            comptime var j: usize = 0;
            comptime var i: usize = 0;
            inline while (i < outBatchSize) : (i += 1) {
                // First, unpack next coefficient.
                comptime var todo: usize = d;
                var out: u16 = 0;

                inline while (todo > 0) {
                    const outShift: usize = comptime d - todo;
                    const m = comptime (1 << d) - 1;
                    out |= (@as(u16, in[inOff + j] >> inShift) << outShift) & m;

                    const done: usize = comptime @min(@min(8, todo), 8 - inShift);
                    todo -= done;
                    inShift += done;

                    if (inShift == 8) {
                        inShift = 0;
                        j += 1;
                    }
                }

                // Decompress_q(x, d) = ⌈(q/2ᵈ)x⌋
                //                    = ⌊(q/2ᵈ)x+½⌋
                //                    = ⌊(qx + 2ᵈ⁻¹)/2ᵈ⌋
                //                    = (qx + (1<<(d-1))) >> d
                const qx = @as(u32, out) * @as(u32, Q);
                ret.cs[outOff + i] = @intCast(i16, (qx + (1 << (d - 1))) >> d);
            }

            inOff += inBatchSize;
            outOff += outBatchSize;
        }

        return ret;
    }

    // Returns the "pointwise" multiplication a o b.
    //
    // That is: invNTT(a o b) = invNTT(a) * invNTT(b).  Assumes a and b are in
    // Montgomery form.  Products between coefficients of a and b must be strictly
    // bounded in absolute value by 2¹⁵q.  a o b will be in Montgomery form and
    // bounded in absolute value by 2q.
    fn mulHat(a: Poly, b: Poly) Poly {
        // Recall from the discussion in ntt(), that a transformed polynomial is
        // an element of ℤ_q[x]/(x²-ζ) x … x  ℤ_q[x]/(x²+ζ¹²⁷);
        // that is: 128 degree-one polynomials instead of simply 256 elements
        // from ℤ_q as in the regular NTT.  So instead of pointwise multiplication,
        // we multiply the 128 pairs of degree-one polynomials modulo the
        // right equation:
        //
        //  (a₁ + a₂x)(b₁ + b₂x) = a₁b₁ + a₂b₂ζ' + (a₁b₂ + a₂b₁)x,
        //
        // where ζ' is the appropriate power of ζ.

        var p: Poly = undefined;
        var k: usize = 64;
        var i: usize = 0;
        while (i < N) : (i += 4) {
            const z = @as(i32, zetas[k]);
            k += 1;

            const a1b1 = montReduce(@as(i32, a.cs[i + 1]) * @as(i32, b.cs[i + 1]));
            const a0b0 = montReduce(@as(i32, a.cs[i]) * @as(i32, b.cs[i]));
            const a1b0 = montReduce(@as(i32, a.cs[i + 1]) * @as(i32, b.cs[i]));
            const a0b1 = montReduce(@as(i32, a.cs[i]) * @as(i32, b.cs[i + 1]));

            p.cs[i] = montReduce(a1b1 * z) + a0b0;
            p.cs[i + 1] = a0b1 + a1b0;

            const a3b3 = montReduce(@as(i32, a.cs[i + 3]) * @as(i32, b.cs[i + 3]));
            const a2b2 = montReduce(@as(i32, a.cs[i + 2]) * @as(i32, b.cs[i + 2]));
            const a3b2 = montReduce(@as(i32, a.cs[i + 3]) * @as(i32, b.cs[i + 2]));
            const a2b3 = montReduce(@as(i32, a.cs[i + 2]) * @as(i32, b.cs[i + 3]));

            p.cs[i + 2] = a2b2 - montReduce(a3b3 * z);
            p.cs[i + 3] = a2b3 + a3b2;
        }

        return p;
    }

    // Sample p from a centered binomial distribution with n=2η and p=½ - viz:
    // coefficients are in {-η, …, η} with probabilities
    //
    //  {ncr(0, 2η)/2^2η, ncr(1, 2η)/2^2η, …, ncr(2η,2η)/2^2η}
    fn noise(comptime eta: u8, nonce: u8, seed: *[32]u8) Poly {
        var h = sha3.Shake256.init(.{});
        const suffix: [1]u8 = .{nonce};
        h.update(seed);
        h.update(&suffix);

        // The distribution at hand is exactly the same as that
        // of (a₁ + a₂ + … + a_η) - (b₁ + … + b_η) where a_i,b_i~U(1).
        // Thus we need 2η bits per coefficient.
        const bufLen: usize = comptime 2 * eta * N / 8;
        var buf: [bufLen]u8 = undefined;
        h.squeeze(&buf);

        // buf is interpreted as a₁…a_ηb₁…b_ηa₁…a_ηb₁…b_η…. We process
        // multiple coefficients in one batch.
        const T: type = u64; // TODO is u128 faster?
        comptime var batchCount: usize = undefined;
        comptime var batchBytes: usize = undefined;
        comptime var mask: T = 0;
        comptime {
            batchCount = @divTrunc(@typeInfo(T).Int.bits, 2 * eta);
            while (@rem(N, batchCount) != 0 and batchCount > 0) : (batchCount -= 1) {}
            assert(batchCount > 0);
            assert(@rem(2 * eta * batchCount, 8) == 0);
            batchBytes = 2 * eta * batchCount / 8;

            comptime var i = 0;
            while (i < 2 * eta * batchCount) : (i += 1) {
                mask <<= eta;
                mask |= 1;
            }
        }

        var i: usize = 0;
        var ret: Poly = undefined;
        while (i < comptime N / batchCount) : (i += 1) {
            // Read coefficients into t. In the case of η=3,
            // we have t = a₁ + 2a₂ + 4a₃ + 8b₁ + 16b₂ + …
            var t: T = 0;
            comptime var j: usize = 0;
            inline while (j < batchBytes) : (j += 1) {
                t |= @as(T, buf[batchBytes * i + j]) << (8 * j);
            }

            // Accumelate `a's and `b's together by masking them out, shifting
            // and adding. For η=3, we have  d = a₁ + a₂ + a₃ + 8(b₁ + b₂ + b₃) + …
            var d: T = 0;
            j = 0;
            inline while (j < eta) : (j += 1) {
                d += (t >> j) & mask;
            }

            // Extract each a and b separately and set coefficient in polynomial.
            j = 0;
            inline while (j < batchCount) : (j += 1) {
                const mask2 = comptime (1 << eta) - 1;
                const a = @intCast(i16, (d >> (comptime (2 * j * eta))) & mask2);
                const b = @intCast(i16, (d >> (comptime ((2 * j + 1) * eta))) & mask2);
                ret.cs[batchCount * i + j] = a - b;
            }
        }

        return ret;
    }
};

// A vector of K polynomials.
fn Vec(comptime K: u8) type {
    return struct {
        const Self = @This();
        ps: [K]Poly,

        fn ntt(a: Self) Self {
            var ret: Self = undefined;
            var i = 0;
            while (i < K) : (i += 1) {
                ret.ps[i] = a.ps[i].ntt();
            }
            return ret;
        }

        fn add(a: Self, b: Self) Self {
            var ret: Self = undefined;
            var i = 0;
            while (i < K) : (i += 1) {
                ret.ps[i] = a.ps[i].add(b.ps[i]);
            }
            return ret;
        }

        fn sub(a: Self, b: Self) Self {
            var ret: Self = undefined;
            var i = 0;
            while (i < K) : (i += 1) {
                ret.ps[i] = a.ps[i].sub(b.ps[i]);
            }
            return ret;
        }
    };
}

test "MulHat" {
    var rnd = RndGen.init(0);
    var t: i32 = 0;

    while (t <= 100) : (t += 1) {
        const a = Poly.randAbsLeqQ(&rnd);
        var b = Poly.randAbsLeqQ(&rnd);

        const p2 = a.ntt().mulHat(b.ntt()).barrettReduce().invNTT().normalize();
        var p: Poly = undefined;

        var i: usize = 0;
        while (i < N) : (i += 1) {
            p.cs[i] = 0;
        }

        i = 0;
        while (i < N) : (i += 1) {
            var j: usize = 0;
            while (j < N) : (j += 1) {
                var v = montReduce(@as(i32, a.cs[i]) * @as(i32, b.cs[j]));
                var k = i + j;
                if (k >= N) {
                    // Recall Xᴺ = -1.
                    k -= N;
                    v = -v;
                }
                p.cs[k] = feBarrettReduce(v + p.cs[k]);
            }
        }

        p = p.toMont().normalize();

        try testing.expectEqual(p, p2);
    }
}

test "NTT" {
    var rnd = RndGen.init(0);
    var k: i32 = 0;

    while (k <= 1000) : (k += 1) {
        var p = Poly.randAbsLeqQ(&rnd);
        var q = p.toMont().normalize();
        p = p.ntt();

        var i: usize = 0;
        while (i < N) : (i += 1) {
            try testing.expect(p.cs[i] <= 7 * Q and -7 * Q <= p.cs[i]);
        }

        p = p.normalize().invNTT();
        i = 0;
        while (i < N) : (i += 1) {
            try testing.expect(p.cs[i] <= Q and -Q <= p.cs[i]);
        }

        p = p.normalize();

        try testing.expectEqual(p, q);
    }
}

test "Compression" {
    var rnd = RndGen.init(0);
    inline for (.{ 1, 4, 5, 10, 11 }) |d| {
        var k: i32 = 0;
        while (k <= 1000) : (k += 1) {
            const p = Poly.randNormalized(&rnd);
            const pp = p.compress(d);
            const pq = Poly.decompress(d, pp).compress(d);
            try testing.expectEqual(pp, pq);
        }
    }
}

test "noise" {
    var seed: [32]u8 = undefined;
    var i: usize = 0;
    while (i < seed.len) : (i += 1) {
        seed[i] = @intCast(u8, i);
    }
    try testing.expectEqual(Poly.noise(3, 37, &seed).cs, .{
        0,  0,  1,  -1, 0,  2,  0,  -1, -1, 3,  0,  1,  -2, -2, 0,  1,  -2,
        1,  0,  -2, 3,  0,  0,  0,  1,  3,  1,  1,  2,  1,  -1, -1, -1, 0,
        1,  0,  1,  0,  2,  0,  1,  -2, 0,  -1, -1, -2, 1,  -1, -1, 2,  -1,
        1,  1,  2,  -3, -1, -1, 0,  0,  0,  0,  1,  -1, -2, -2, 0,  -2, 0,
        0,  0,  1,  0,  -1, -1, 1,  -2, 2,  0,  0,  2,  -2, 0,  1,  0,  1,
        1,  1,  0,  1,  -2, -1, -2, -1, 1,  0,  0,  0,  0,  0,  1,  0,  -1,
        -1, 0,  -1, 1,  0,  1,  0,  -1, -1, 0,  -2, 2,  0,  -2, 1,  -1, 0,
        1,  -1, -1, 2,  1,  0,  0,  -2, -1, 2,  0,  0,  0,  -1, -1, 3,  1,
        0,  1,  0,  1,  0,  2,  1,  0,  0,  1,  0,  1,  0,  0,  -1, -1, -1,
        0,  1,  3,  1,  0,  1,  0,  1,  -1, -1, -1, -1, 0,  0,  -2, -1, -1,
        2,  0,  1,  0,  1,  0,  2,  -2, 0,  1,  1,  -3, -1, -2, -1, 0,  1,
        0,  1,  -2, 2,  2,  1,  1,  0,  -1, 0,  -1, -1, 1,  0,  -1, 2,  1,
        -1, 1,  2,  -2, 1,  2,  0,  1,  2,  1,  0,  0,  2,  1,  2,  1,  0,
        2,  1,  0,  0,  -1, -1, 1,  -1, 0,  1,  -1, 2,  2,  0,  0,  -1, 1,
        1,  1,  1,  0,  0,  -2, 0,  -1, 1,  2,  0,  0,  1,  1,  -1, 1,  0,
        1,
    });
    try testing.expectEqual(Poly.noise(2, 37, &seed).cs, .{
        1,  0,  1,  -1, -1, -2, -1, -1, 2,  0,  -1, 0,  0,  -1,
        1,  1,  -1, 1,  0,  2,  -2, 0,  1,  2,  0,  0,  -1, 1,
        0,  -1, 1,  -1, 1,  2,  1,  1,  0,  -1, 1,  -1, -2, -1,
        1,  -1, -1, -1, 2,  -1, -1, 0,  0,  1,  1,  -1, 1,  1,
        1,  1,  -1, -2, 0,  1,  0,  0,  2,  1,  -1, 2,  0,  0,
        1,  1,  0,  -1, 0,  0,  -1, -1, 2,  0,  1,  -1, 2,  -1,
        -1, -1, -1, 0,  -2, 0,  2,  1,  0,  0,  0,  -1, 0,  0,
        0,  -1, -1, 0,  -1, -1, 0,  -1, 0,  0,  -2, 1,  1,  0,
        1,  0,  1,  0,  1,  1,  -1, 2,  0,  1,  -1, 1,  2,  0,
        0,  0,  0,  -1, -1, -1, 0,  1,  0,  -1, 2,  0,  0,  1,
        1,  1,  0,  1,  -1, 1,  2,  1,  0,  2,  -1, 1,  -1, -2,
        -1, -2, -1, 1,  0,  -2, -2, -1, 1,  0,  0,  0,  0,  1,
        0,  0,  0,  2,  2,  0,  1,  0,  -1, -1, 0,  2,  0,  0,
        -2, 1,  0,  2,  1,  -1, -2, 0,  0,  -1, 1,  1,  0,  0,
        2,  0,  1,  1,  -2, 1,  -2, 1,  1,  0,  2,  0,  -1, 0,
        -1, 0,  1,  2,  0,  1,  0,  -2, 1,  -2, -2, 1,  -1, 0,
        -1, 1,  1,  0,  0,  0,  1,  0,  -1, 1,  1,  0,  0,  0,
        0,  1,  0,  1,  -1, 0,  1,  -1, -1, 2,  0,  0,  1,  -1,
        0,  1,  -1, 0,
    });
}

const std = @import("std");

const testing = std.testing;
const assert = std.debug.assert;
const RndGen = std.rand.DefaultPrng;

// Q is the parameter q ≡ 3329 = 2¹¹ + 2¹⁰ + 2⁸ + 1.
const Q: i16 = 3329;

// Montgomery R
const R: i32 = 1 << 16;

// Parameter n, degree of polynomials.
const N: i32 = 256;

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
    return @bitCast(i16, @truncate(u16, @bitCast(u32, x - @as(i32, m) * @as(i32, Q)) >> 16));
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
// Beware: we might have barrettReduce(x) = q ≠ 0 for some x.  In fact,
// this happens if and only if x = -nq for some positive integer n.
fn barrettReduce(x: i16) i16 {
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

test "Test Barrett reduce" {
    var x: i32 = -(1 << 15);
    while (x < 1 << 15) : (x += 1) {
        var y1: i16 = barrettReduce(@intCast(i16, x));
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

fn computeZetas() [128]i16 {
    @setEvalBranchQuota(10000);
    var ret: [128]i16 = undefined;
    var i: i32 = 0;
    while (i < 128) : (i += 1) {
        ret[@intCast(usize, i)] = csubq(barrettReduce(feToMont(@intCast(i16, mpow(@as(i32, zeta), brv(i, 7), Q)))));
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
        comptime var i = 0;
        inline while (i < N) : (i += 1) {
            ret.cs[i] = a.cs[i] + b.cs[i];
        }
        return ret;
    }

    fn sub(a: Poly, b: Poly) Poly {
        var ret: Poly = undefined;
        comptime var i = 0;
        inline while (i < N) : (i += 1) {
            ret.cs[i] = a.cs[i] - b.cs[i];
        }
        return ret;
    }

    // For testing, generates a random polynomial polynomial with for each
    // coefficient |x| ≤ q.
    fn randAbsLeqQ(rnd: anytype) Poly {
        var ret: Poly = undefined;
        var i: usize = 0;
        while (i < N) : (i += 1) {
            ret.cs[i] = rnd.random().intRangeAtMost(i16, -Q, Q);
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
                p.cs[@intCast(usize, i)] = barrettReduce(p.cs[@intCast(usize, i)]);
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
        comptime var i = 0;
        inline while (i < N) : (i += 1) {
            ret.cs[i] = csubq(barrettReduce(a.cs[i]));
        }
        return ret;
    }

    // Put p in Montgomery form.
    fn toMont(a: Poly) Poly {
        var ret: Poly = undefined;
        comptime var i = 0;
        inline while (i < N) : (i += 1) {
            ret.cs[i] = feToMont(a.cs[i]);
        }
        return ret;
    }
};

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

// Implementation of the IND-CCA2 post-quantum secure key encapsulation
// mechanism (KEM) CRYSTALS-Kyber, as submitted to the third round of the NIST
// Post-Quantum Cryptography (v3.02/"draft00"), and selected for standardisation.
//
// Kyber will likely change before final standardisation.
//
// Quoting from the CFRG I-D:
//
// Kyber is not a Diffie-Hellman (DH) style non-interactive key
// agreement, but instead, Kyber is a Key Encapsulation Method (KEM).
// In essence, a KEM is a Public-Key Encryption (PKE) scheme where the
// plaintext cannot be specified, but is generated as a random key as
// part of the encryption. A KEM can be transformed into an unrestricted
// PKE using HPKE (RFC9180). On its own, a KEM can be used as a key
// agreement method in TLS.
//
// Kyber is an IND-CCA2 secure KEM.  It is constructed by applying a
// Fujisaki--Okamato style transformation on InnerPKE, which is the
// underlying IND-CPA secure Public Key Encryption scheme.  We cannot
// use InnerPKE directly, as its ciphertexts are malleable.
//
//                     F.O. transform
//     InnerPKE   ---------------------->   Kyber
//     IND-CPA                              IND-CCA2
//
// Kyber is a lattice-based scheme.  More precisely, its security is
// based on the learning-with-errors-and-rounding problem in module
// lattices (MLWER).  The underlying polynomial ring R (defined in
// Section 5) is chosen such that multiplication is very fast using the
// number theoretic transform (NTT, see Section 5.1.3).
//
// An InnerPKE private key is a vector _s_ over R of length k which is
// _small_ in a particular way.  Here k is a security parameter akin to
// the size of a prime modulus.  For Kyber512, which targets AES-128's
// security level, the value of k is 2.
//
// The public key consists of two values:
//
// *  _A_ a uniformly sampled k by k matrix over R _and_
//
// *  _t = A s + e_, where e is a suitably small masking vector.
//
// Distinguishing between such A s + e and a uniformly sampled t is the
// module learning-with-errors (MLWE) problem.  If that is hard, then it
// is also hard to recover the private key from the public key as that
// would allow you to distinguish between those two.
//
// To save space in the public key, A is recomputed deterministically
// from a seed _rho_.
//
// A ciphertext for a message m under this public key is a pair (c_1,
// c_2) computed roughly as follows:
//
// c_1 = Compress(A^T r + e_1, d_u)
// c_2 = Compress(t^T r + e_2 + Decompress(m, 1), d_v)
//
// where
//
// *  e_1, e_2 and r are small blinds;
//
// *  Compress(-, d) removes some information, leaving d bits per
//    coefficient and Decompress is such that Compress after Decompress
//    does nothing and
//
// *  d_u, d_v are scheme parameters.
//
// Distinguishing such a ciphertext and uniformly sampled (c_1, c_2) is
// an example of the full MLWER problem, see section 4.4 of [KyberV302].
//
// To decrypt the ciphertext, one computes
//
// m = Compress(Decompress(c_2, d_v) - s^T Decompress(c_1, d_u), 1).
//
// It it not straight-forward to see that this formula is correct.  In
// fact, there is negligable but non-zero probability that a ciphertext
// does not decrypt correctly given by the DFP column in Table 4.  This
// failure probability can be computed by a careful automated analysis
// of the probabilities involved, see kyber_failure.py of [SecEst].
//
//  [KyberV302] https://pq-crystals.org/kyber/data/kyber-specification-round3-20210804.pdf
//  [I-D] https://github.com/bwesterb/draft-schwabe-cfrg-kyber
//  [SecEst] https://github.com/pq-crystals/security-estimates

// TODO
//
// - API
// - More documentation
// - We pass amd return rather large structs, like Vec, Mat and PublicKey
//   by value. Is the compiler clever enough to get rid of all the copies?
// - Add benchmarks.
// - The bottleneck in Kyber are the various hash/xof calls:
//    - Optimize Zig's keccak implementation.
//    - Use SIMD to compute keccak in parallel.
// - Can we track bounds of coefficients using comptime types without
//   duplicating code?
// - Figure out how to neatly break long lines.
// - test clauses within structs behaved weirdly, they're now moved into the
//   global scope. Would be neater to have tests closer to the thing under test.
// - When generating a keypair, we have a copy of the inner public key with
//   its large matrix A in both the public key and the priovate key. In Go we
//   can just have a pointer in the private key to the public key, but
//   how do we do this elegantly in Zig?

const std = @import("std");

const testing = std.testing;
const assert = std.debug.assert;
const RndGen = std.rand.DefaultPrng;
const sha3 = std.crypto.hash.sha3;

// Q is the parameter q ??? 3329 = 2???? + 2????? + 2??? + 1.
const Q: i16 = 3329;

// Montgomery R
const R: i32 = 1 << 16;

// Parameter n, degree of polynomials.
const N: i32 = 256;

// Size of "small" vectors used in encryption blinds.
const eta2: u8 = 2;

const Params = struct {
    name: []const u8,

    // Width and height of the matrix A.
    k: u8,

    // Size of "small" vectors used in private key and encryption blinds.
    eta1: u8,

    // How many bits to retain of u, the private-key independent part
    // of the ciphertext.
    du: u8,

    // How many bits to retain of v, the private-key dependent part
    // of the ciphertext.
    dv: u8,
};

const Kyber512 = Kyber(.{
    .name = "Kyber512",
    .k = 2,
    .eta1 = 3,
    .du = 10,
    .dv = 4,
});

const Kyber768 = Kyber(.{
    .name = "Kyber768",
    .k = 3,
    .eta1 = 2,
    .du = 10,
    .dv = 4,
});

const Kyber1024 = Kyber(.{
    .name = "Kyber1024",
    .k = 4,
    .eta1 = 2,
    .du = 11,
    .dv = 5,
});

const modes = [_]type{ Kyber512, Kyber768, Kyber1024 };
const hSize: usize = 32;
const innerSeedSize: usize = 32;
const encapsSeedSize: usize = 32;
const sharedKeySize: usize = 32;

fn Kyber(comptime p: Params) type {
    return struct {
        // Size of ciphertexts.
        const ciphertextSize: usize = Poly.compressedSize(p.du) * p.k + Poly.compressedSize(p.dv);

        const Self = @This();
        const V = Vec(p.k);
        const M = Mat(p.k);

        const seedSize: usize = innerSeedSize + sharedKeySize;
        const name = p.name;

        const PublicKey = struct {
            pk: innerPk,

            // Cached
            hpk: [hSize]u8, // H(pk)

            const packedSize: usize = innerPk.packedSize;

            // If you're unsure, you should use encaps instead.
            fn encapsDeterministically(pk: PublicKey, seed: *const [encapsSeedSize]u8, ct: *[ciphertextSize]u8, ss: *[sharedKeySize]u8) void {
                var m: [innerPlaintextSize]u8 = undefined;

                // m = H(seed)
                var h = sha3.Sha3_256.init(.{});
                h.update(seed);
                h.final(&m);

                // (K', r) = G(m ??? H(pk))
                var kr: [innerPlaintextSize + hSize]u8 = undefined;
                var g = sha3.Sha3_512.init(.{});
                g.update(&m);
                g.update(&pk.hpk);
                g.final(&kr);

                // c = innerEncrypy(pk, m, r)
                ct.* = pk.pk.encrypt(&m, kr[32..64]);

                // Compute H(c) and put in second slot of kr, which will be (K', H(c)).
                h = sha3.Sha3_256.init(.{}); // TODO is there an h.reset()?
                h.update(ct);
                h.final(kr[32..64]);

                // K = KDF(K' ??? H(c))
                var kdf = sha3.Shake256.init(.{});
                kdf.update(&kr);
                kdf.squeeze(ss);
            }

            fn pack(pk: PublicKey) [packedSize]u8 {
                return pk.pk.pack();
            }

            fn unpack(buf: *const [packedSize]u8) PublicKey {
                var ret: PublicKey = undefined;
                ret.pk = innerPk.unpack(buf[0..innerPk.packedSize]);

                var h = sha3.Sha3_256.init(.{});
                h.update(buf);
                h.final(&ret.hpk);
                return ret;
            }
        };

        const PrivateKey = struct {
            sk: innerSk,
            pk: innerPk,
            hpk: [hSize]u8, // H(pk)
            z: [sharedKeySize]u8,

            const packedSize: usize = innerSk.packedSize + innerPk.packedSize + hSize + sharedKeySize;

            fn decaps(sk: PrivateKey, ct: *const [ciphertextSize]u8) [sharedKeySize]u8 {
                // m' = innerDec(ct)
                const m2 = sk.sk.decrypt(ct);

                // (K'', r') = G(m' ??? H(pk))
                var kr2: [64]u8 = undefined;
                var g = sha3.Sha3_512.init(.{});
                g.update(&m2);
                g.update(&sk.hpk);
                g.final(&kr2);

                // ct' = innerEnc(pk, m', r')
                const ct2 = sk.pk.encrypt(&m2, kr2[32..64]);

                // Compute H(ct) and put in the second slot of kr2 which will be (K'', H(ct)).
                var h = sha3.Sha3_256.init(.{});
                h.update(ct);
                h.final(kr2[32..64]);

                // Replace K'' by z in the first slot of kr2 if ct ??? ct'.
                cmov(32, kr2[0..32], &sk.z, cteq(ciphertextSize, ct, &ct2));

                // K = KDF(K''/z, H(c))
                var kdf = sha3.Shake256.init(.{});
                var ss: [sharedKeySize]u8 = undefined;
                kdf.update(&kr2);
                kdf.squeeze(&ss);
                return ss;
            }

            fn pack(sk: PrivateKey) [packedSize]u8 {
                return sk.sk.pack() ++ sk.pk.pack() ++ sk.hpk ++ sk.z;
            }

            fn unpack(buf: *const [packedSize]u8) PrivateKey {
                var ret: PrivateKey = undefined;
                comptime var s: usize = 0;
                ret.sk = innerSk.unpack(buf[s .. s + innerSk.packedSize]);
                s += innerSk.packedSize;
                ret.pk = innerPk.unpack(buf[s .. s + innerPk.packedSize]);
                s += innerPk.packedSize;
                std.mem.copy(u8, &ret.hpk, buf[s .. s + hSize]);
                s += hSize;
                std.mem.copy(u8, &ret.z, buf[s .. s + sharedKeySize]);
                return ret;
            }
        };

        const KeyPair = struct {
            sk: PrivateKey,
            pk: PublicKey,
        };

        // Internals below.
        fn keyFromSeed(seed: *const [seedSize]u8) KeyPair {
            var ret: KeyPair = undefined;
            std.mem.copy(u8, &ret.sk.z, seed[innerSeedSize..seedSize]);

            // Generate inner key
            innerKeyFromSeed(seed[0..innerSeedSize], &ret.pk.pk, &ret.sk.sk);
            ret.sk.pk = ret.pk.pk;

            // Copy over z from seed.
            std.mem.copy(u8, &ret.sk.z, seed[innerSeedSize..seedSize]);

            // Compute H(pk)
            var h = sha3.Sha3_256.init(.{});
            h.update(&ret.pk.pk.pack());
            h.final(&ret.sk.hpk);
            ret.pk.hpk = ret.sk.hpk;

            return ret;
        }

        // Size of plaintexts of the in
        const innerPlaintextSize: usize = Poly.compressedSize(1);

        const innerPk = struct {
            rho: [32]u8, // ??, the seed for the matrix A
            th: V, // NTT(t), normalized

            // Cached values
            aT: M,

            const packedSize: usize = V.packedSize + 32;

            fn encrypt(pk: innerPk, pt: *const [innerPlaintextSize]u8, seed: *const [32]u8) [ciphertextSize]u8 {
                // Sample r, e??? and e??? appropriately
                const rh = V.noise(p.eta1, 0, seed).ntt().barrettReduce();
                const e1 = V.noise(eta2, p.k, seed);
                const e2 = Poly.noise(eta2, 2 * p.k, seed);

                // Next we compute u = A??? r + e???.  First A???.
                var u: V = undefined;
                var i: usize = 0;
                while (i < p.k) : (i += 1) {
                    // Note that coefficients of r are bounded by q and those of A???
                    // are bounded by 4.5q and so their product is bounded by 2?????q
                    // as required for multiplication.
                    u.ps[i] = pk.aT.vs[i].dotHat(rh);
                }

                // A??? and r were not in Montgomery form, so the Montgomery
                // multiplications in the inner product added a factor R????? which
                // the InvNTT cancels out.
                u = u.barrettReduce().invNTT().add(e1).normalize();

                // Next, compute v = <t, r> + e??? + Decompress_q(m, 1)
                const v = pk.th.dotHat(rh).barrettReduce().invNTT().add(Poly.decompress(1, pt)).add(e2).normalize();

                return u.compress(p.du) ++ v.compress(p.dv);
            }

            fn pack(pk: innerPk) [packedSize]u8 {
                return pk.th.pack() ++ pk.rho;
            }

            fn unpack(buf: *const [packedSize]u8) innerPk {
                var ret: innerPk = undefined;
                ret.th = V.unpack(buf[0..V.packedSize]).normalize();
                std.mem.copy(u8, &ret.rho, buf[V.packedSize..packedSize]);
                ret.aT = M.uniform(&ret.rho, true);
                return ret;
            }
        };

        // Private key of the inner PKE
        const innerSk = struct {
            sh: V, // NTT(s), normalized
            const packedSize = V.packedSize;

            fn decrypt(sk: innerSk, ct: *const [ciphertextSize]u8) [innerPlaintextSize]u8 {
                const u = V.decompress(p.du, ct[0..comptime V.compressedSize(p.du)]);
                const v = Poly.decompress(p.dv, ct[comptime V.compressedSize(p.du)..ciphertextSize]);

                // Compute m = v - <s, u>
                return v.sub(sk.sh.dotHat(u.ntt()).barrettReduce().invNTT()).normalize().compress(1);
            }

            fn pack(sk: innerSk) [packedSize]u8 {
                return sk.sh.pack();
            }

            fn unpack(buf: *const [packedSize]u8) innerSk {
                var ret: innerSk = undefined;
                ret.sh = V.unpack(buf).normalize();
                return ret;
            }
        };

        // Derives inner PKE keypair from given seed.
        fn innerKeyFromSeed(seed: *const [innerSeedSize]u8, pk: *innerPk, sk: *innerSk) void {
            var expandedSeed: [64]u8 = undefined;

            var h = sha3.Sha3_512.init(.{});
            h.update(seed);
            h.final(&expandedSeed);
            std.mem.copy(u8, &pk.rho, expandedSeed[0..32]);
            const sigma = expandedSeed[32..64];
            pk.aT = M.uniform(&pk.rho, false); // Expand ?? to A; we'll transpose later on

            // Sample secret vector s.
            sk.sh = V.noise(p.eta1, 0, sigma).ntt().normalize();

            const eh = Vec(p.k).noise(p.eta1, p.k, sigma).ntt(); // sample blind e.
            var th: V = undefined;

            // Next, we compute t = A s + e.
            var i: usize = 0;
            while (i < p.k) : (i += 1) {
                // Note that coefficients of s are bounded by q and those of A
                // are bounded by 4.5q and so their product is bounded by 2?????q
                // as required for multiplication.
                // A and s were not in Montgomery form, so the Montgomery
                // multiplications in the inner product added a factor R????? which
                // we'll cancel out with toMont().  This will also ensure the
                // coefficients of th are bounded in absolute value by q.
                th.ps[i] = pk.aT.vs[i].dotHat(sk.sh).toMont();
            }

            pk.th = th.add(eh).normalize(); // bounded by 8q
            pk.aT = pk.aT.T();
        }
    };
}

// R mod q
const RModQ: i32 = @rem(@as(i32, R), Q);

// R?? mod q
const R2ModQ: i32 = @rem(RModQ * RModQ, Q);

// ?? is the degree 256 primitive root of unity used for the NTT.
const zeta: i16 = 17;

// (128)????? R??. Used in inverse NTT.
const R2over128: i32 = @mod(invertMod(128, Q) * R2ModQ, Q);

// zetas lists precomputed powers of the primitive root of unity in
// Montgomery representation used for the NTT:
//
//  zetas[i] = ??????????????????? R mod q
//
// where ?? = 17, brv(i) is the bitreversal of a 7-bit number and R=2????? mod q.
const zetas: [128]i16 = computeZetas();

// invNTTReductions keeps track of which coefficients to apply Barrett
// reduction to in Poly.invNTT().
//
// Generated lazily: once a butterfly is computed which is about to
// overflow the i16, the largest coefficient is reduced.  If that is
// not enough, the other coefficient is reduced as well.
//
// This is actually optimal, as proven in https://eprint.iacr.org/2020/1377.pdf
// TODO generate comptime?
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
        xs[i] = 1; // start at |x| ??? q
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

// Given -2????? q ??? x < 2????? q, returns -q < y < q with x 2???????? = y (mod q).
fn montReduce(x: i32) i16 {
    const qInv = comptime invertMod(@as(i32, Q), R);
    // This is Montgomery reduction with R=2?????.
    //
    // Note gcd(2?????, q) = 1 as q is prime.  Write q' := 62209 = q????? mod R.
    // First we compute
    //
    //	m := ((x mod R) q') mod R
    //         = x q' mod R
    //	   = int16(x q')
    //	   = int16(int32(x) * int32(q'))
    //
    // Note that x q' might be as big as 2???? and could overflow the int32
    // multiplication in the last line.  However for any int32s a and b,
    // we have int32(int64(a)*int64(b)) = int32(a*b) and so the result is ok.
    const m: i16 = @truncate(i16, @truncate(i32, x *% qInv));

    // Note that x - m q is divisable by R; indeed modulo R we have
    //
    //  x - m q ??? x - x q' q ??? x - x q????? q ??? x - x = 0.
    //
    // We return y := (x - m q) / R.  Note that y is indeed correct as
    // modulo q we have
    //
    //  y ??? x R????? - m q R????? = x R?????
    //
    // and as both 2????? q ??? m q, x < 2????? q, we have
    // 2????? q ??? x - m q < 2????? and so q ??? (x - m q) / R < q as desired.
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

// Given any x, return x R mod q where R=2?????.
fn feToMont(x: i16) i16 {
    // Note |1353 x| ??? 1353 2????? ??? 13318 q ??? 2????? q and so we're within
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

// Given any x, compute 0 ??? y ??? q with x = y (mod q).
//
// Beware: we might have feBarrettReduce(x) = q ??? 0 for some x.  In fact,
// this happens if and only if x = -nq for some positive integer n.
fn feBarrettReduce(x: i16) i16 {
    // This is standard Barrett reduction.
    //
    // For any x we have x mod q = x - ???x/q??? q.  We will use 20159/2????? as
    // an approximation of 1/q. Note that  0 ??? 20159/2????? - 1/q ??? 0.135/2?????
    // and so | x 20156/2????? - x/q | ??? 2???????? for |x| ??? 2?????.  For all x
    // not a multiple of q, the number x/q is further than 1/q from any integer
    // and so ???x 20156/2???????? = ???x/q???.  If x is a multiple of q and x is positive,
    // then x 20156/2????? is larger than x/q so ???x 20156/2???????? = ???x/q??? as well.
    // Finally, if x is negative multiple of q, then ???x 20156/2???????? = ???x/q???-1.
    // Thus
    //                        [ q        if x=-nq for pos. integer n
    //  x - ???x 20156/2???????? q = [
    //                        [ x mod q  otherwise
    //
    // To actually compute this, note that
    //
    //  ???x 20156/2???????? = (20159 x) >> 26.
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

// Returns x if x < q and x - q otherwise.  Assumes x ??? -29439.
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

// An element of our base ring R which are polynomials over ???_q
// modulo the equation X??? = -1, where q=3329 and N=256.
//
// This type is also used to store NTT-transformed polynomials,
// see Poly.NTT().
//
// Coefficients aren't always reduced.  See Normalize().
const Poly = struct {
    cs: [N]i16,

    const packedSize = N / 2 * 3;
    const zero: Poly = .{ .cs = .{0} ** N };

    fn add(a: Poly, b: Poly) Poly {
        var ret: Poly = undefined;
        var i: usize = 0;
        while (i < N) : (i += 1) {
            ret.cs[i] = a.cs[i] + b.cs[i];
        }
        return ret;
    }

    fn sub(a: Poly, b: Poly) Poly {
        var ret: Poly = undefined;
        var i: usize = 0;
        while (i < N) : (i += 1) {
            ret.cs[i] = a.cs[i] - b.cs[i];
        }
        return ret;
    }

    // For testing, generates a random polynomial with for each
    // coefficient |x| ??? q.
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
    // Assumes the coefficients are in absolute value ???q.  The resulting
    // coefficients are in absolute value ???7q.  If the input is in Montgomery
    // form, then the result is in Montgomery form and so (by linearity of the NTT)
    // if the input is in regular form, then the result is also in regular form.
    fn ntt(a: Poly) Poly {
        // Note that ???_q does not have a primitive 512????? root of unity (as 512
        // does not divide into q-1) and so we cannot do a regular NTT.  ???_q
        // does have a primitive 256????? root of unity, the smallest of which
        // is ?? := 17.
        //
        // Recall that our base ring R := ???_q[x] / (x???????? + 1).  The polynomial
        // x????????+1 will not split completely (as its roots would be 512????? roots
        // of unity.)  However, it does split almost (using ????????? = -1):
        //
        // x???????? + 1 = (x??)??????? - ?????????
        //          = ((x??)?????? - ????????)((x??)?????? + ????????)
        //          = ((x??)???? - ??????)((x??)???? + ??????)((x??)???? - ????????)((x??)???? + ????????)
        //          ???
        //          = (x?? - ??)(x?? + ??)(x?? - ????????)(x?? + ????????) ??? (x?? + ?????????)
        //
        // Note that the powers of ?? that appear (from the second line down) are
        // in binary
        //
        // 0100000 1100000
        // 0010000 1010000 0110000 1110000
        // 0001000 1001000 0101000 1101000 0011000 1011000 0111000 1111000
        //         ???
        //
        // That is: brv(2), brv(3), brv(4), ???, where brv(x) denotes the 7-bit
        // bitreversal of x.  These powers of ?? are given by the Zetas array.
        //
        // The polynomials x?? ?? ????? are irreducible and coprime, hence by
        // the Chinese Remainder Theorem we know
        //
        //  ???_q[x]/(x????????+1) ??? ???_q[x]/(x??-??) x ??? x  ???_q[x]/(x??+?????????)
        //
        // given by a ??? ( a mod x??-??, ???, a mod x??+????????? )
        // is an isomorphism, which is the "NTT".  It can be efficiently computed by
        //
        //
        //  a ??? ( a mod (x??)?????? - ????????, a mod (x??)?????? + ???????? )
        //    ??? ( a mod (x??)???? - ??????, a mod (x??)???? + ??????,
        //        a mod (x??)?????? - ????????, a mod (x??)?????? + ???????? )
        //
        //      et cetera
        // If N was 8 then this can be pictured in the following diagram:
        //
        //  https://cnx.org/resources/17ee4dfe517a6adda05377b25a00bf6e6c93c334/File0026.png
        //
        // Each cross is a Cooley-Tukey butterfly: it's the map
        //
        //  (a, b) ??? (a + ??b, a - ??b)
        //
        // for the appropriate power ?? for that column and row group.
        var p = a;
        var k: usize = 0; // index into zetas

        var l: usize = N >> 1;
        while (l > 1) : (l >>= 1) {
            // On the n????? iteration of the l-loop, the absolute value of the
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
    // Assumes the coefficients are in absolute value ???q.  The resulting
    // coefficients are in absolute value ???q.  If the input is in Montgomery
    // form, then the result is in Montgomery form and so (by linearity)
    // if the input is in regular form, then the result is also in regular form.
    fn invNTT(a: Poly) Poly {
        var k: usize = 127; // index into zetas
        var r: usize = 0; // index into invNTTReductions
        var p = a;

        // We basically do the oppposite of NTT, but postpone dividing by 2 in the
        // inverse of the Cooley-Tukey butterfly and accumulate that into a big
        // division by 2??? at the end.  See the comments in the ntt() function.

        var l: usize = 2;
        while (l < N) : (l <<= 1) {
            var offset: usize = 0;
            while (offset < N - l) : (offset += 2 * l) {
                // As we're inverting, we need powers of ??????? (instead of ??).
                // To be precise, we need ?????????????????????????????. However, as ???????????? = -1,
                // we can use the existing zetas table instead of
                // keeping a separate invZetas table as in Dilithium.

                var minZeta = @as(i32, zetas[k]);
                k -= 1;

                var j = offset;
                while (j < offset + l) : (j += 1) {
                    // Gentleman-Sande butterfly: (a, b) ??? (a + b, ??(a-b))
                    const t = p.cs[j + l] - p.cs[j];
                    p.cs[j] += p.cs[j + l];
                    p.cs[j + l] = montReduce(minZeta * @as(i32, t));

                    // Note that if we had |a| < ??q and |b| < ??q before the
                    // butterfly, then now we have |a| < (??+??)q and |b| < q.
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
            // Note 1441 = (128)????? R??.  The coefficients are bounded by 9q, so
            // as 1441 * 9 ??? 2????? < 2?????, we're within the required bounds
            // for montReduce().
            p.cs[j] = montReduce(R2over128 * @as(i32, p.cs[j]));
        }

        return p;
    }

    // Normalizes coefficients.
    //
    // Ensures each coefficient is in {0, ???, q-1}.
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

    fn compressedSize(comptime d: u8) usize {
        return @divTrunc(N * d, 8);
    }

    // Returns packed Compress_q(p, d).
    //
    // Assumes p is normalized.
    fn compress(p: Poly, comptime d: u8) [compressedSize(d)]u8 {
        @setEvalBranchQuota(10000);
        const Qover2: u32 = comptime @divTrunc(Q, 2); // (q-1)/2
        const twoDm1: u32 = comptime (1 << d) - 1; // 2???-1
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
                // Compress_q(x, d) = ???(2???/q)x??? mod??? 2???
                //                  = ???(2???/q)x+????? mod??? 2???
                //                  = ???((x << d) + q/2) / q??? mod??? 2???
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
    fn decompress(comptime d: u8, in: *const [compressedSize(d)]u8) Poly {
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

                // Decompress_q(x, d) = ???(q/2???)x???
                //                    = ???(q/2???)x+?????
                //                    = ???(qx + 2????????)/2??????
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
    // bounded in absolute value by 2?????q.  a o b will be in Montgomery form and
    // bounded in absolute value by 2q.
    fn mulHat(a: Poly, b: Poly) Poly {
        // Recall from the discussion in ntt(), that a transformed polynomial is
        // an element of ???_q[x]/(x??-??) x ??? x  ???_q[x]/(x??+?????????);
        // that is: 128 degree-one polynomials instead of simply 256 elements
        // from ???_q as in the regular NTT.  So instead of pointwise multiplication,
        // we multiply the 128 pairs of degree-one polynomials modulo the
        // right equation:
        //
        //  (a??? + a???x)(b??? + b???x) = a???b??? + a???b?????' + (a???b??? + a???b???)x,
        //
        // where ??' is the appropriate power of ??.

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

    // Sample p from a centered binomial distribution with n=2?? and p=?? - viz:
    // coefficients are in {-??, ???, ??} with probabilities
    //
    //  {ncr(0, 2??)/2^2??, ncr(1, 2??)/2^2??, ???, ncr(2??,2??)/2^2??}
    fn noise(comptime eta: u8, nonce: u8, seed: *const [32]u8) Poly {
        var h = sha3.Shake256.init(.{});
        const suffix: [1]u8 = .{nonce};
        h.update(seed);
        h.update(&suffix);

        // The distribution at hand is exactly the same as that
        // of (a??? + a??? + ??? + a_??) - (b??? + ??? + b_??) where a_i,b_i~U(1).
        // Thus we need 2?? bits per coefficient.
        const bufLen: usize = comptime 2 * eta * N / 8;
        var buf: [bufLen]u8 = undefined;
        h.squeeze(&buf);

        // buf is interpreted as a??????a_??b??????b_??a??????a_??b??????b_?????. We process
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
            // Read coefficients into t. In the case of ??=3,
            // we have t = a??? + 2a??? + 4a??? + 8b??? + 16b??? + ???
            var t: T = 0;
            comptime var j: usize = 0;
            inline while (j < batchBytes) : (j += 1) {
                t |= @as(T, buf[batchBytes * i + j]) << (8 * j);
            }

            // Accumelate `a's and `b's together by masking them out, shifting
            // and adding. For ??=3, we have  d = a??? + a??? + a??? + 8(b??? + b??? + b???) + ???
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

    // Sample p uniformly from the given seed and x and y coordinates.
    fn uniform(seed: *const [32]u8, x: u8, y: u8) Poly {
        var h = sha3.Shake128.init(.{});
        const suffix: [2]u8 = .{ x, y };
        h.update(seed);
        h.update(&suffix);

        const bufLen = 168; // rate SHAKE-128
        var buf: [bufLen]u8 = undefined;

        var ret: Poly = undefined;
        var i: usize = 0; // index into ret.cs
        outer: while (true) {
            h.squeeze(&buf);

            var j: usize = 0; // index into buf
            while (j < bufLen) : (j += 3) {
                const b0 = @as(u16, buf[j]);
                const b1 = @as(u16, buf[j + 1]);
                const b2 = @as(u16, buf[j + 2]);

                const ts: [2]u16 = .{
                    b0 | ((b1 & 0xf) << 8),
                    (b1 >> 4) | (b2 << 4),
                };

                inline for (ts) |t| {
                    if (t < Q) {
                        ret.cs[i] = @intCast(i16, t);
                        i += 1;

                        if (i == N) {
                            break :outer;
                        }
                    }
                }
            }
        }

        return ret;
    }

    // Packs p.
    //
    // Assumes p is normalized (and not just Barrett reduced).
    fn pack(p: Poly) [packedSize]u8 {
        var i: usize = 0;
        var ret: [packedSize]u8 = undefined;
        while (i < comptime N / 2) : (i += 1) {
            const t0 = @intCast(u16, p.cs[2 * i]);
            const t1 = @intCast(u16, p.cs[2 * i + 1]);
            ret[3 * i] = @truncate(u8, t0);
            ret[3 * i + 1] = @truncate(u8, (t0 >> 8) | (t1 << 4));
            ret[3 * i + 2] = @truncate(u8, t1 >> 4);
        }
        return ret;
    }

    // Unpacks a Poly from buf.
    //
    // p will not be normalized; instead 0 ??? p[i] < 4096.
    fn unpack(buf: *const [packedSize]u8) Poly {
        var ret: Poly = undefined;
        var i: usize = 0;
        while (i < comptime N / 2) : (i += 1) {
            const b0 = @as(i16, buf[3 * i]);
            const b1 = @as(i16, buf[3 * i + 1]);
            const b2 = @as(i16, buf[3 * i + 2]);
            ret.cs[2 * i] = b0 | ((b1 & 0xf) << 8);
            ret.cs[2 * i + 1] = (b1 >> 4) | b2 << 4;
        }
        return ret;
    }
};

// A vector of K polynomials.
fn Vec(comptime K: u8) type {
    return struct {
        ps: [K]Poly,

        const Self = @This();
        const packedSize = K * Poly.packedSize;

        fn compressedSize(comptime d: u8) usize {
            return Poly.compressedSize(d) * K;
        }

        fn ntt(a: Self) Self {
            var ret: Self = undefined;
            var i: usize = 0;
            while (i < K) : (i += 1) {
                ret.ps[i] = a.ps[i].ntt();
            }
            return ret;
        }

        fn invNTT(a: Self) Self {
            var ret: Self = undefined;
            var i: usize = 0;
            while (i < K) : (i += 1) {
                ret.ps[i] = a.ps[i].invNTT();
            }
            return ret;
        }

        fn normalize(a: Self) Self {
            var ret: Self = undefined;
            var i: usize = 0;
            while (i < K) : (i += 1) {
                ret.ps[i] = a.ps[i].normalize();
            }
            return ret;
        }

        fn barrettReduce(a: Self) Self {
            var ret: Self = undefined;
            var i: usize = 0;
            while (i < K) : (i += 1) {
                ret.ps[i] = a.ps[i].barrettReduce();
            }
            return ret;
        }

        fn add(a: Self, b: Self) Self {
            var ret: Self = undefined;
            var i: usize = 0;
            while (i < K) : (i += 1) {
                ret.ps[i] = a.ps[i].add(b.ps[i]);
            }
            return ret;
        }

        fn sub(a: Self, b: Self) Self {
            var ret: Self = undefined;
            var i: usize = 0;
            while (i < K) : (i += 1) {
                ret.ps[i] = a.ps[i].sub(b.ps[i]);
            }
            return ret;
        }

        // Samples v[i] from centered binomial distribution with the given ??,
        // seed and nonce+i.
        fn noise(comptime eta: u8, nonce: u8, seed: *const [32]u8) Self {
            var ret: Self = undefined;
            var i: u8 = 0;
            while (i < K) : (i += 1) {
                ret.ps[i] = Poly.noise(eta, nonce + i, seed);
            }
            return ret;
        }

        // Sets p to the inner product of a and b using "pointwise" multiplication.
        //
        // See MulHat() and NTT() for a description of the multiplication.
        // Assumes a and b are in Montgomery form.  p will be in Montgomery form,
        // and its coefficients will be bounded in absolute value by 2kq.
        // If a and b are not in Montgomery form, then the action is the same
        // as "pointwise" multiplication followed by multiplying by R?????, the inverse
        // of the Montgomery factor.
        fn dotHat(a: Self, b: Self) Poly {
            var ret: Poly = Poly.zero;
            var i: usize = 0;
            while (i < K) : (i += 1) {
                ret = ret.add(a.ps[i].mulHat(b.ps[i]));
            }
            return ret;
        }

        fn compress(v: Self, comptime d: u8) [compressedSize(d)]u8 {
            const cs = comptime Poly.compressedSize(d);
            var ret: [compressedSize(d)]u8 = undefined;
            var i: usize = 0;
            while (i < K) : (i += 1) {
                std.mem.copy(u8, ret[i * cs .. (i + 1) * cs], &v.ps[i].compress(d));
            }
            return ret;
        }

        fn decompress(comptime d: u8, buf: *const [compressedSize(d)]u8) Self {
            const cs = comptime Poly.compressedSize(d);
            var ret: Self = undefined;
            comptime var i: usize = 0;
            inline while (i < K) : (i += 1) {
                ret.ps[i] = Poly.decompress(d, buf[i * cs .. (i + 1) * cs]);
            }
            return ret;
        }

        fn pack(v: Self) [packedSize]u8 {
            var ret: [packedSize]u8 = undefined;
            comptime var i = 0;
            inline while (i < K) : (i += 1) {
                std.mem.copy(u8, ret[i * Poly.packedSize .. (i + 1) * Poly.packedSize], &v.ps[i].pack());
            }
            return ret;
        }

        fn unpack(buf: *const [packedSize]u8) Self {
            var ret: Self = undefined;
            comptime var i: usize = 0;
            inline while (i < K) : (i += 1) {
                ret.ps[i] = Poly.unpack(buf[i * Poly.packedSize .. (i + 1) * Poly.packedSize]);
            }
            return ret;
        }
    };
}

// A matrix of K vectors
fn Mat(comptime K: u8) type {
    return struct {
        const Self = @This();
        vs: [K]Vec(K),

        fn uniform(seed: *const [32]u8, comptime transpose: bool) Self {
            var ret: Self = undefined;
            var i: u8 = 0;
            while (i < K) : (i += 1) {
                var j: u8 = 0;
                while (j < K) : (j += 1) {
                    ret.vs[i].ps[j] = Poly.uniform(
                        seed,
                        if (transpose) i else j,
                        if (transpose) j else i,
                    );
                }
            }
            return ret;
        }

        // Returns transpose of A
        fn T(m: Self) Self {
            var i: usize = 0;
            var ret: Self = undefined;
            while (i < K) : (i += 1) {
                var j: usize = 0;
                while (j < K) : (j += 1) {
                    ret.vs[i].ps[j] = m.vs[j].ps[i];
                }
            }
            return ret;
        }
    };
}

// Returns 0 if a = b and 1 otherwise.
fn cteq(comptime len: usize, a: *const [len]u8, b: *const [len]u8) usize {
    // TODO Is there an existing function in the stdlib for this?
    var i: usize = 0;
    var ret: u8 = 0;
    while (i < len) : (i += 1) {
        ret |= a[i] ^ b[i];
    }
    return @bitCast(usize, -@as(isize, ret)) >> (@typeInfo(usize).Int.bits - 1);
}

// Copy src into dst given b = 1.
//
// Assumes b is either 0 or 1.
fn cmov(comptime len: usize, dst: *[len]u8, src: *const [len]u8, b: usize) void {
    // TODO Is there an existing function in the stdlib for this?
    const mask = @bitCast(u8, -@intCast(i8, b));
    var i: usize = 0;
    while (i < len) : (i += 1) {
        dst[i] ^= mask & (dst[i] ^ src[i]);
    }
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
                    // Recall X??? = -1.
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
            const pq = Poly.decompress(d, &pp).compress(d);
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

test "uniform sampling" {
    var seed: [32]u8 = undefined;
    var i: usize = 0;
    while (i < seed.len) : (i += 1) {
        seed[i] = @intCast(u8, i);
    }
    try testing.expectEqual(Poly.uniform(&seed, 1, 0).cs, .{
        797,  993,  161,  6,    2608, 2385, 2096, 2661, 1676, 247,  2440,
        342,  634,  194,  1570, 2848, 986,  684,  3148, 3208, 2018, 351,
        2288, 612,  1394, 170,  1521, 3119, 58,   596,  2093, 1549, 409,
        2156, 1934, 1730, 1324, 388,  446,  418,  1719, 2202, 1812, 98,
        1019, 2369, 214,  2699, 28,   1523, 2824, 273,  402,  2899, 246,
        210,  1288, 863,  2708, 177,  3076, 349,  44,   949,  854,  1371,
        957,  292,  2502, 1617, 1501, 254,  7,    1761, 2581, 2206, 2655,
        1211, 629,  1274, 2358, 816,  2766, 2115, 2985, 1006, 2433, 856,
        2596, 3192, 1,    1378, 2345, 707,  1891, 1669, 536,  1221, 710,
        2511, 120,  1176, 322,  1897, 2309, 595,  2950, 1171, 801,  1848,
        695,  2912, 1396, 1931, 1775, 2904, 893,  2507, 1810, 2873, 253,
        1529, 1047, 2615, 1687, 831,  1414, 965,  3169, 1887, 753,  3246,
        1937, 115,  2953, 586,  545,  1621, 1667, 3187, 1654, 1988, 1857,
        512,  1239, 1219, 898,  3106, 391,  1331, 2228, 3169, 586,  2412,
        845,  768,  156,  662,  478,  1693, 2632, 573,  2434, 1671, 173,
        969,  364,  1663, 2701, 2169, 813,  1000, 1471, 720,  2431, 2530,
        3161, 733,  1691, 527,  2634, 335,  26,   2377, 1707, 767,  3020,
        950,  502,  426,  1138, 3208, 2607, 2389, 44,   1358, 1392, 2334,
        875,  2097, 173,  1697, 2578, 942,  1817, 974,  1165, 2853, 1958,
        2973, 3282, 271,  1236, 1677, 2230, 673,  1554, 96,   242,  1729,
        2518, 1884, 2272, 71,   1382, 924,  1807, 1610, 456,  1148, 2479,
        2152, 238,  2208, 2329, 713,  1175, 1196, 757,  1078, 3190, 3169,
        708,  3117, 154,  1751, 3225, 1364, 154,  23,   2842, 1105, 1419,
        79,   5,    2013,
    });
}

test "Polynomial packing" {
    var rnd = RndGen.init(0);
    var k: i32 = 0;

    while (k <= 1000) : (k += 1) {
        var p = Poly.randNormalized(&rnd);
        try testing.expectEqual(Poly.unpack(&p.pack()), p);
    }
}

test "Test inner PKE" {
    var seed: [32]u8 = undefined;
    var pt: [32]u8 = undefined;
    var i: usize = 0;
    while (i < seed.len) : (i += 1) {
        seed[i] = @intCast(u8, i);
        pt[i] = @intCast(u8, i + 32);
    }
    inline for (modes) |mode| {
        i = 0;
        while (i < 100) : (i += 1) {
            var pk: mode.innerPk = undefined;
            var sk: mode.innerSk = undefined;
            seed[0] = @intCast(u8, i);
            mode.innerKeyFromSeed(&seed, &pk, &sk);
            var j: usize = 0;
            while (j < 10) : (j += 1) {
                seed[1] = @intCast(u8, j);
                try testing.expectEqual(sk.decrypt(&pk.encrypt(&pt, &seed)), pt);
            }
        }
    }
}

test "Test happy flow" {
    var seed: [64]u8 = undefined;
    var i: usize = 0;
    while (i < seed.len) : (i += 1) {
        seed[i] = @intCast(u8, i);
    }
    inline for (modes) |mode| {
        i = 0;
        while (i < 100) : (i += 1) {
            seed[0] = @intCast(u8, i);
            var kp = mode.keyFromSeed(&seed);
            const sk = mode.PrivateKey.unpack(&kp.sk.pack());
            try testing.expectEqual(sk, kp.sk);
            const pk = mode.PublicKey.unpack(&kp.pk.pack());
            try testing.expectEqual(pk, kp.pk);
            var j: usize = 0;
            while (j < 10) : (j += 1) {
                seed[1] = @intCast(u8, j);
                var ct: [mode.ciphertextSize]u8 = undefined;
                var ss: [sharedKeySize]u8 = undefined;
                pk.encapsDeterministically(seed[0..32], &ct, &ss);
                try testing.expectEqual(ss, sk.decaps(&ct));
            }
        }
    }
}

// Code to test NIST Known Answer Tests (KAT), see PQCgenKAT.c.

const sha2 = std.crypto.hash.sha2;

test "NIST KAT test" {
    inline for (.{
        .{ Kyber512, "e9c2bd37133fcb40772f81559f14b1f58dccd1c816701be9ba6214d43baf4547" },
        .{ Kyber1024, "89248f2f33f7f4f7051729111f3049c409a933ec904aedadf035f30fa5646cd5" },
        .{ Kyber768, "a1e122cad3c24bc51622e4c242d8b8acbcd3f618fee4220400605ca8f9ea02c2" },
    }) |modeHash| {
        const mode = modeHash[0];
        var seed: [48]u8 = undefined;
        var i: usize = 0;
        while (i < seed.len) : (i += 1) {
            seed[i] = @intCast(u8, i);
        }
        var f = sha2.Sha256.init(.{});
        var fw = f.writer();
        var g = NistDRBG.new(&seed);
        try std.fmt.format(fw, "# {s}\n\n", .{mode.name});
        i = 0;
        while (i < 100) : (i += 1) {
            g.fill(&seed);
            try std.fmt.format(fw, "count = {}\n", .{i});
            try std.fmt.format(fw, "seed = {s}\n", .{std.fmt.fmtSliceHexUpper(&seed)});
            var g2 = NistDRBG.new(&seed);

            // This is not equivalent to g2.fill(kseed[:]).  As the reference
            // implementation calls randombytes twice generating the keypair,
            // we have to do that as well.
            var kseed: [64]u8 = undefined;
            var eseed: [32]u8 = undefined;
            g2.fill(kseed[0..32]);
            g2.fill(kseed[32..64]);
            g2.fill(&eseed);
            const kp = mode.keyFromSeed(&kseed);
            var ct: [mode.ciphertextSize]u8 = undefined;
            var ss: [sharedKeySize]u8 = undefined;
            kp.pk.encapsDeterministically(&eseed, &ct, &ss);
            const ss2 = kp.sk.decaps(&ct);
            try testing.expectEqual(ss2, ss);
            try std.fmt.format(fw, "pk = {s}\n", .{std.fmt.fmtSliceHexUpper(&kp.pk.pack())});
            try std.fmt.format(fw, "sk = {s}\n", .{std.fmt.fmtSliceHexUpper(&kp.sk.pack())});
            try std.fmt.format(fw, "ct = {s}\n", .{std.fmt.fmtSliceHexUpper(&ct)});
            try std.fmt.format(fw, "ss = {s}\n\n", .{std.fmt.fmtSliceHexUpper(&ss)});
        }

        var out: [32]u8 = undefined;
        f.final(&out);
        var outHex: [64]u8 = undefined;
        _ = try std.fmt.bufPrint(&outHex, "{s}", .{std.fmt.fmtSliceHexLower(&out)});
        try testing.expectEqual(outHex, modeHash[1].*);
    }
}

const NistDRBG = struct {
    key: [32]u8,
    v: [16]u8,

    fn incV(g: *NistDRBG) void {
        var j: usize = 15;
        while (j >= 0) : (j -= 1) {
            if (g.v[j] == 255) {
                g.v[j] = 0;
            } else {
                g.v[j] += 1;
                break;
            }
        }
    }

    // AES256_CTR_DRBG_Update(pd, &g.key, &g.v).
    fn update(g: *NistDRBG, pd: ?*const [48]u8) void {
        var buf: [48]u8 = undefined;
        var ctx = std.crypto.core.aes.Aes256.initEnc(g.key);
        var i: usize = 0;
        while (i < 3) : (i += 1) {
            g.incV();
            var block: [16]u8 = undefined;
            ctx.encrypt(&block, &g.v);
            std.mem.copy(u8, buf[i * 16 .. (i + 1) * 16], &block);
        }
        if (pd != null) {
            i = 0;
            while (i < buf.len) : (i += 1) {
                buf[i] ^= pd.?[i];
            }
        }
        std.mem.copy(u8, &g.key, buf[0..32]);
        std.mem.copy(u8, &g.v, buf[32..48]);
    }

    // randombytes.
    fn fill(g: *NistDRBG, out: []u8) void {
        var block: [16]u8 = undefined;
        var dst = out;

        var ctx = std.crypto.core.aes.Aes256.initEnc(g.key);
        while (dst.len > 0) {
            g.incV();
            ctx.encrypt(&block, &g.v);
            if (dst.len < 16) {
                std.mem.copy(u8, dst, block[0..dst.len]);
                break;
            }
            std.mem.copy(u8, dst, &block);
            dst = dst[16..dst.len];
        }
        g.update(null);
    }

    // randombyte_init(seed, NULL, 256).
    fn new(seed: *[48]u8) NistDRBG {
        var ret: NistDRBG = NistDRBG{ .key = .{0} ** 32, .v = .{0} ** 16 };
        ret.update(seed);
        return ret;
    }
};

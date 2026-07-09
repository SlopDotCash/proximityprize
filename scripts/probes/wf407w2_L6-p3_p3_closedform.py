#!/usr/bin/env python3
"""WF407 / thread L6-p3 (T334-13 follow-up): the CLOSED FORM of P3(t2) = sum_phi t2^3
(smooth subgroup MINUS random) and the q^-4 M3 signal exponent.

Wave-1 established (O133 / wf407_T334-13-M3_t2moments):
  P1 = sum_phi t2   = C(n,2)(q-1)        -- PINNED (domain-independent)
  P2 = sum_phi t2^2                       -- PINNED (domain-independent, both probes)
  P3 = sum_phi t2^3                       -- FIRST power sum that SEPARATES smooth vs random.

This probe derives P3 EXACTLY and decomposes the SEPARATION (smooth - random) into the
mechanism predicted by the t2_weil reduction:

  t2 = (N(sigma) - fixed)/2,  N(sigma) = #{x in mu_n : sigma(x) in mu_n}.
  * NORMALIZER pencils  x -> c/x (c in H) and x -> -x  : t2 = (n - fixed)/2 ~ n/2  (the SPIKES,
    n+1 of them on the SUBGROUP; they are the degenerate-char-pair main term, |S| ~ q-1).
  * non-normalizer pencils : t2 = O(n^2/q + 1)  (Weil noise band, |S| <= deg*sqrt q).

CLAIM (closed form of the separation):
  Delta_P3 := P3(subgroup) - P3(random)  is dominated by the cube of the spike height,
  i.e. Delta_P3 ~ (#spikes) * (n/2)^3 - (random spike content).  The SUBGROUP has n+1 full
  spikes; a RANDOM n-set has expected #{c in D : x->c/x preserves D} = O(n^2/q) involution
  hits, so its 'spikes' are noise-height.  Hence Delta_P3 = Theta(n * (n/2)^3) = Theta(n^4/8),
  a q-INDEPENDENT integer.  The RELATIVE signal divides by M3 ~ q^k * (stuff): rel ~ Delta/M3.

We measure EXACTLY at n=8,16,32:
  (1) P1,P2,P3 for subgroup and randoms -> confirm P1,P2 pinned, P3 separates;
  (2) the EXACT Delta_P3 and its decomposition spike-cube + noise;
  (3) the closed form Delta_P3 = (n+1)*[(n-2)/2]^3 + n*[n/2]^3 ... (fit the exact integer);
  (4) confirm Delta_P3 is q-INDEPENDENT at fixed n (run multiple q per n);
  (5) the relative M3 signal rel = Delta_P3-driven / M3 and its q-exponent.

EXACT integers throughout.  Reproduce: python wf407w2_L6-p3_p3_closedform.py
"""

import math
import random
import sys


def is_prime(m):
    if m < 2:
        return False
    f = 2
    while f * f <= m:
        if m % f == 0:
            return False
        f += 1
    return True


def prime_factors(m):
    fs, d = set(), 2
    while d * d <= m:
        while m % d == 0:
            fs.add(d); m //= d
        d += 1
    if m > 1:
        fs.add(m)
    return fs


def primitive_root(q):
    fs = prime_factors(q - 1)
    for g in range(2, q):
        if all(pow(g, (q - 1) // p, q) != 1 for p in fs):
            return g
    raise ValueError


def subgroup(q, n, g=None):
    if g is None:
        g = primitive_root(q)
    h = pow(g, (q - 1) // n, q)
    out, e = [], 1
    for _ in range(n):
        out.append(e); e = (e * h) % q
    return sorted(set(out))


def mobius_apply(phi, x, q):
    p0, p1, p2 = phi
    den = (p0 * x - p1) % q
    if den == 0:
        return None
    return ((p1 * x - p2) * pow(den, q - 2, q)) % q


def pencil_t2_fixed(phi, Hset, q):
    """t2 = #2-orbits inside H ; fixed = #fixed points of sigma inside H."""
    seen, t2, fixed = set(), 0, 0
    for x in Hset:
        y = mobius_apply(phi, x, q)
        if y is None or y not in Hset:
            continue
        if y == x:
            fixed += 1
        else:
            kf = (x, y) if x < y else (y, x)
            if kf not in seen:
                seen.add(kf); t2 += 1
    return t2, fixed


def all_pencils(q):
    """Nondegenerate involutory pencils phi=(p0,p1,p2) with p1^2 - p0 p2 != 0."""
    out = []
    for p1 in range(q):
        for p2 in range(q):
            if (p1 * p1 - p2) % q != 0:          # p0 = 1 branch
                out.append((1, p1, p2))
    for p2 in range(q):                          # p0 = 0, p1 = 1 branch
        out.append((0, 1, p2))
    return out


def power_sums_and_spikes(q, D, n):
    """Return (P1,P2,P3, spike_list, noise_max, normalizer_t2_list).
    A SPIKE = pencil with t2 >= n//2 - 1 (the normalizer band)."""
    Hset = set(D)
    P1 = P2 = P3 = 0
    spikes = []
    noise_max = 0
    for phi in all_pencils(q):
        t2, _ = pencil_t2_fixed(phi, Hset, q)
        P1 += t2
        P2 += t2 * t2
        P3 += t2 ** 3
        if t2 >= n // 2 - 1:
            spikes.append(t2)
        else:
            noise_max = max(noise_max, t2)
    return P1, P2, P3, sorted(spikes), noise_max


def normalizer_t2(q, D, n, g):
    """t2 of the n+1 torus-normalizer pencils on the SUBGROUP H = <h>:
    x -> c/x for c in H (n pencils) and x -> -x (1 pencil).  Returns the multiset of t2."""
    Hset = set(D)
    out = []
    for c in D:
        phi = (1, 0, (q - c) % q)             # sigma(x) = (0*x - (-c))/(1*x - 0) = c/x
        if (0 - 1 * ((q - c) % q)) % q == 0:   # p1^2 - p0 p2 = 0 - (-c) = c != 0 always
            pass
        t2, fx = pencil_t2_fixed(phi, Hset, q)
        out.append((t2, fx))
    # negation x -> -x  : phi = (0,1,0)
    t2, fx = pencil_t2_fixed((0, 1, 0), Hset, q)
    out.append((t2, fx))
    return out


def main():
    print("WF407 / L6-p3 : closed form of P3 = sum_phi t2^3 (smooth - random) + q^-4 exponent\n")

    # ---- PART 1+2+3: pinning of P1,P2 ; separation of P3 ; the spike decomposition ----
    cases = [(41, 8), (73, 8), (89, 8), (113, 16), (257, 16), (97, 32)]
    print("=" * 92)
    print("PART 1-3: P1,P2 pinned ; P3 separates ; spike decomposition (exact integers)")
    print("=" * 92)
    for (q, n) in cases:
        if (q - 1) % n or not is_prime(q):
            continue
        g = primitive_root(q)
        H = subgroup(q, n, g)
        P1H, P2H, P3H, spkH, nmaxH = power_sums_and_spikes(q, H, n)
        rs = []
        for seed in range(1, 5):
            dom = sorted(random.Random(31337 * q + seed).sample(range(1, q), n))
            rs.append(power_sums_and_spikes(q, dom, n))
        P1r = [r[0] for r in rs]; P2r = [r[1] for r in rs]; P3r = [r[2] for r in rs]
        print(f"\n--- q={q}, n={n} (mu_{n}) ---")
        print(f"  P1: H={P1H}  rand={P1r}   pinned={all(v==P1H for v in P1r)}  "
              f"[C(n,2)(q-1)={math.comb(n,2)*(q-1)}]")
        print(f"  P2: H={P2H}  rand={P2r}   pinned={all(v==P2H for v in P2r)}")
        print(f"  P3: H={P3H}  rand={P3r}   separates={any(v!=P3H for v in P3r)}")
        # spike decomposition of P3
        spike_cube = sum(t**3 for t in spkH)
        # subgroup's n+1 normalizer pencils, exact t2:
        norm = normalizer_t2(q, H, n, g)
        norm_cube = sum(t**3 for (t, fx) in norm)
        dP3 = P3H - min(P3r)
        print(f"  subgroup spikes (t2 list)={spkH}  spike_cube(sum t2^3 over spikes)={spike_cube}")
        print(f"  normalizer pencils (t2,fixed)={norm}")
        print(f"     sum_normalizer t2^3 = {norm_cube}")
        print(f"  Delta_P3 = P3(H) - P3(rand_best) = {dP3}")

    # ---- PART 4: q-INDEPENDENCE of Delta_P3 at fixed n (the closed-form core) ----
    print("\n" + "=" * 92)
    print("PART 4: is Delta_P3 q-INDEPENDENT at fixed n?  (multiple primes q==1 mod n)")
    print("=" * 92)
    for n in (8, 16):
        qs = [q for q in range(n + 1, 2000) if is_prime(q) and (q - 1) % n == 0][:8]
        print(f"\nn={n}:  normalizer-cube law:  the n+1 spikes are x->c/x (c in H) + x->-x")
        print(f"{'q':>6}{'P3(H)':>22}{'P3(rand)':>22}{'Delta_P3':>16}{'norm_cube':>14}")
        for q in qs:
            g = primitive_root(q)
            H = subgroup(q, n, g)
            P3H = power_sums_and_spikes(q, H, n)[2]
            # take min over randoms as the 'random baseline'
            P3rs = []
            for seed in range(1, 4):
                dom = sorted(random.Random(31337 * q + seed).sample(range(1, q), n))
                P3rs.append(power_sums_and_spikes(q, dom, n)[2])
            P3r = min(P3rs)
            norm = normalizer_t2(q, H, n, g)
            norm_cube = sum(t**3 for (t, fx) in norm)
            print(f"{q:>6}{P3H:>22}{P3r:>22}{P3H-P3r:>16}{norm_cube:>14}")

    # ---- PART 5: the predicted closed form for the SPIKE content ----
    print("\n" + "=" * 92)
    print("PART 5: predicted closed-form spike content of P3 on the subgroup")
    print("=" * 92)
    print("Normalizer spikes on mu_n (n even): x->c/x has fixed pts = #{x in mu_n: x^2=c}.")
    print(" c in mu_n is a square in mu_n iff c in mu_n^2 (index-2): for those 2 fixed pts,")
    print(" t2=(n-2)/2 ; for non-square c: 0 fixed, t2=n/2.  x->-x: -1 in mu_n, x=-x impossible")
    print(" (char!=2), so 0 fixed, t2=n/2.  Count: n/2 squares -> t2=(n-2)/2 ; n/2 nonsq -> n/2;")
    print(" plus negation -> n/2.  So spike t2-multiset = {(n-2)/2 : n/2 times, n/2 : n/2+1 times}.")
    for n in (8, 16, 32):
        c_lo = ((n - 2) // 2) ** 3 * (n // 2)
        c_hi = (n // 2) ** 3 * (n // 2 + 1)
        print(f"  n={n}:  predicted sum_normalizer t2^3 = "
              f"(n/2)*((n-2)/2)^3 + (n/2+1)*(n/2)^3 = {c_lo} + {c_hi} = {c_lo + c_hi}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

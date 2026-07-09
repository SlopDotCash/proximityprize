#!/usr/bin/env python3
"""
probe_407_minkowski_latticecount.py  --  #407: the Minkowski/Gaussian lattice count of P, head-on.

THE ROUTE'S CENTRAL OBJECT.
  O = Z[zeta_n], D = phi(n). P = prime over p (residue degree 1, since z=g^{(p-1)/n} in F_p, so
  the map X|->z gives O/P = F_p). covol of the Minkowski lattice Lambda_P = p * sqrt|disc(O)|.
  disc(Q(zeta_n)) for n=2^mu: |disc| = 2^{(mu-1) 2^{mu-1}} ... we use sympy to get it exactly.

  A defect alpha at depth r is a nonzero element of P whose group-ring (length-n, balanced) coeff
  vector has L1 <= 2r. In the POWER basis (length D) its coords c satisfy: it is a Z-combination of
  the n reduced basis images, each of L1<=1 in power coords... For n=2^mu, Phi_n = X^{D}+1 (D=n/2),
  and X^{D+k} = -X^k, so reducing a length-n balanced vector to power coords keeps each |c_i| <= the
  number of group positions mapping to +-i, and L1(power) <= L1(group) <= 2r. GOOD: for n=2^mu the
  reduction is an ISOMETRY-ish fold (no blowup) -- L1(power) <= 2r exactly. So defect alpha are
  EXACTLY nonzero c in Z^D with L1(c) <= 2r AND c in Lambda_P (c . (1,z,z^2,...,z^{D-1}) == 0 mod p).

  THE COUNT we need: N_def(r,p) = #{ c in Z^D, c != 0, |c|_1 <= 2r, sum c_i z^i == 0 mod p }.
  (z^i for i in [0,D) are the power-basis images; here z has order n=2D in F_p.)

  Minkowski/Gaussian heuristic: the constraint "sum c_i z^i == 0 mod p" is ONE linear condition mod p
  on c, cutting density 1/p. So heuristically
        N_def(r,p)  ~  (# c with |c|_1 <= 2r) / p   =  Vol_1(2r, D)/p,
  where Vol_1(R,D) = #{c in Z^D : |c|_1<=R} ~ (2R)^D/D! for R>>D ... but here R=2r can be < D.
  THE WALL CHECK: in the prize regime p ~ n^beta = (2D)^beta, and at deep r ~ ln p ~ beta ln(2D),
  is Vol_1(2r,D)/p <= o(E_r^(0))? E_r^(0) ~ (2r-1)!! D^r-ish ... we compute all exactly here.

This probe (EXACT short-vector enumeration in P):
  For a concrete prize prime p ~ n^beta, ENUMERATE all nonzero c in Z^D with |c|_1 <= L for L=2..12,
  test c in P (sum c_i z^i == 0 mod p), and report:
     N_def(L,p) (actual count of short vectors in P),
     Vol_1(L,D)  (total short lattice points),
     ratio N_def * p / Vol_1   (heuristic predicts ~1 if the 1/p density law holds),
     and the implied defect weight vs E_r^(0).
This is the rigorous core: it shows whether the count obeys the 1/p heuristic or has an EXCESS of
STRUCTURED short vectors forced into P (which would break the route).

Run:  python scripts/probes/probe_407_minkowski_latticecount.py
"""
import sys, math, itertools
from collections import Counter

sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, odd_part, primitive_root
import sympy


def prize_prime(n, beta, pmax=10**12):
    base = int(round(n ** beta)); base -= base % n; base += 1; p = base
    while p < pmax:
        if is_prime(p) and odd_part((p - 1) // n) > 1:
            return p
        p += n
    return None


def short_vectors_L1(D, L):
    """Yield all integer vectors c in Z^D with 1 <= |c|_1 <= L, canonical (first nonzero > 0 to
       dedupe +-). We generate compositions: choose support and signed values. For modest D,L this is
       fine. Yields tuples."""
    # iterate over total L1 weight w from 1..L, over supports, over sign/magnitude compositions
    seen_lead = True
    for w in range(1, L + 1):
        # distribute weight w over D coords with magnitudes m_i >= 0 sum = w, then signs on nonzeros
        for support_size in range(1, min(D, w) + 1):
            for support in itertools.combinations(range(D), support_size):
                # compositions of w into support_size positive parts
                for parts in _compositions(w, support_size):
                    mags = [0] * D
                    for idx, pos in enumerate(support):
                        mags[pos] = parts[idx]
                    # signs: 2^{support_size}, dedupe global sign by fixing first support sign = +
                    for signs in itertools.product((1, -1), repeat=support_size):
                        if signs[0] == -1:
                            continue  # canonical: leading nonzero positive
                        c = list(mags)
                        for idx, pos in enumerate(support):
                            c[pos] = mags[pos] * signs[idx]
                        yield tuple(c)


def _compositions(total, parts):
    """positive integer compositions of `total` into exactly `parts` parts."""
    if parts == 1:
        yield (total,); return
    for first in range(1, total - parts + 2):
        for rest in _compositions(total - first, parts - 1):
            yield (first,) + rest


def main():
    print("=" * 86)
    print(" #407 MINKOWSKI LATTICE COUNT:  N_def(L,p) = #{c in Z^D, 0<|c|_1<=L, c in P}  vs  Vol/p")
    print("=" * 86)
    for n in (8, 16):
        D = n // 2  # phi(2^mu) = 2^{mu-1}
        disc = abs(int(sympy.ntheory.discriminant if False else sympy.cyclotomic_poly(n)
                       .as_poly().discriminant()))
        print(f"\n n={n}: D=phi(n)={D}; |disc(Phi_n)|={disc} (2^{math.log2(disc):.1f}); "
              f"covol(Lambda_P)=p*sqrt|disc_field|.")
        for beta in (4.0, 5.0):
            p = prize_prime(n, beta)
            g = primitive_root(p); z = pow(g, (p - 1) // n, p)
            zpows = [pow(z, i, p) for i in range(D)]
            print(f"  beta={beta}: p={p} (2^{math.log2(p):.2f}); z order {n}; "
                  f"power-basis images z^0..z^{D-1} mod p ready.")
            print(f"     {'L=2r':>5} {'r':>3} {'N_def(in P)':>12} {'Vol_1(L,D)':>14} "
                  f"{'N_def*p/Vol':>12} {'minkowski 1?':>13}")
            Lmax = 12 if D <= 4 else (10 if D <= 8 else 8)
            for L in range(2, Lmax + 1, 1):
                if L % 2 == 1:  # depth r = L/2 integer only at even L (balanced relation)
                    continue
                # count short vectors in P, and total
                ndef = 0; vol = 0
                # bound work: Vol_1 grows fast; cap
                est_vol = sum(math.comb(D, s) * math.comb(L - 1, s - 1) * 2 ** s
                              for s in range(1, min(D, L) + 1))  # ~ #vectors (overcount-free comp)
                if est_vol > 6_000_000:
                    print(f"     {L:>5} {L//2:>3}   (Vol_1~{est_vol:.2e} too large to enumerate)")
                    continue
                for c in short_vectors_L1(D, L):
                    vol += 1
                    s = 0
                    for i in range(D):
                        if c[i]: s += c[i] * zpows[i]
                    if s % p == 0:
                        ndef += 1
                # vol counts canonical (one of +-c); true lattice points = 2*vol (+ 0). For density:
                total_pts = 2 * vol
                ndef_pts = 2 * ndef
                ratio = (ndef_pts * p / total_pts) if total_pts else float('nan')
                mink = total_pts / p  # >1 means Minkowski could force a point; <1 generically empty
                print(f"     {L:>5} {L//2:>3} {ndef_pts:>12} {total_pts:>14} "
                      f"{ratio:>12.3f} {mink:>13.4f}")
    print("\nKEY:")
    print(" - N_def*p/Vol ~ 1  => the '1 linear condition mod p' heuristic holds: short vectors in P")
    print("   are as RARE as random (density 1/p). Then N_def ~ Vol_1(2r,D)/p, and the defect is")
    print("   controlled by Vol_1(2r,D)/p -- a CLEAN, COUNTABLE quantity (the route's deliverable).")
    print(" - 'minkowski 1?' = Vol/p: when < 1, NO short vector is FORCED (P generically avoids the")
    print("   L1-ball); the first forced short vector appears at L where Vol_1(L,D) ~ p, i.e.")
    print("   (2L)^D/D! ~ p  =>  L ~ (D!/2^D p)^{1/D} ~ (D/e)(p)^{1/D}. For prize p~ (2D)^beta this is")
    print("   L ~ (D/e)(2D)^{beta/D} -> D/e as D grows: the SHORTEST forced vector has L1 ~ D/e = n/(2e).")


if __name__ == "__main__":
    main()

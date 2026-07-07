"""probe_466_novel_sos_dgen10.py -- LANE N5 (#466), round-3 verifier extension of
probe_466_novel_sos_collapse.py.

GOAL: decide the ONE open constant flagged in
docs/kb/deltastar-466-novel-N5-sos-duality-2026-07-01.md (S6/S8): the l1-generation
radius d_gen(n,p) of the relation lattice L = ker(Z^n -> F_p, a |-> sum a_j h^j) at
GENERIC beta=4 primes, where the norm-8 scan gave only "d_gen > 8".  The dossier's
balanced wraparound onset r0 = 5 predicts the first char-p relations at l1-norm 10,
so the scan must reach norm 10 to see them.  Method identical to the parent probe
(meet-in-the-middle over the full integer l1-ball + exact integer HNF index), with a
generator-based second half to keep memory flat.

Scales: n = 16, dmax = 10, the same three primes (65537 Fermat cross-check + 65617 +
65633 generic); n = 8, dmax = 12 (cheap, closes the n=8 row too).

Output: scripts/probes/_out_466_novel_sos_dgen10.txt
"""

import os
import sys
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_466_novel_sos_collapse import (  # noqa: E402
    subgroup, hnf_add, basis_index, is_charzero, plog, compositions)


def half_iter(dim, dmax):
    """generator over (vec tuple, l1-norm) for all integer vectors, l1 <= dmax."""
    yield (tuple([0] * dim), 0)
    for m in range(1, dmax + 1):
        for s in range(1, min(m, dim) + 1):
            for supp in combinations(range(dim), s):
                for comp in compositions(m, s):
                    for signs in range(1 << s):
                        v = [0] * dim
                        for i, (pos, c) in enumerate(zip(supp, comp)):
                            v[pos] = c if (signs >> i) & 1 == 0 else -c
                        yield (tuple(v), m)


def relations_upto_lowmem(xs, p, dmax):
    """all a in Z^n, l1-norm <= dmax, sum_j a_j x_j = 0 mod p, grouped by norm.
    Meet-in-the-middle; second half streamed (memory ~ one half only)."""
    n = len(xs)
    nh = n // 2
    xs1, xs2 = xs[:nh], xs[nh:]
    d1 = {}
    for v, m in half_iter(nh, dmax):
        val = sum(c * x for c, x in zip(v, xs1)) % p
        d1.setdefault(val, []).append((v, m))
    rels = {m: [] for m in range(1, dmax + 1)}
    for v2, m2 in half_iter(n - nh, dmax):
        bucket = d1.get((-sum(c * x for c, x in zip(v2, xs2))) % p)
        if bucket:
            for v1, m1 in bucket:
                m = m1 + m2
                if 0 < m <= dmax:
                    rels[m].append(v1 + v2)
    return rels


def analyze(n, p, dmax, out):
    xs = subgroup(n, p)
    nh = n // 2
    assert all((xs[j] + xs[j + nh]) % p == 0 for j in range(nh)), "antipodal sanity"
    rels = relations_upto_lowmem(xs, p, dmax)
    basis = {}
    d_onset = None
    d_gen = None
    out.append(f"\n===== n={n}, p={p}  (beta = log_n p = {plog(n, p):.3f}), "
               f"scan to l1-norm {dmax} =====")
    for d in range(1, dmax + 1):
        new = rels[d]
        n_wrap = sum(1 for v in new if not is_charzero(v, n))
        if n_wrap and d_onset is None:
            d_onset = d
        for v in new:
            hnf_add(basis, v)
        idx, rank = basis_index(basis, n)
        tag = ""
        if idx is not None:
            mult = idx // p if idx % p == 0 else None
            tag = (f" index = {idx} = p*{mult}" if mult is not None
                   else f" index = {idx} (NOT mult of p -- BUG?)")
            if idx == p and d_gen is None:
                d_gen = d
                tag += "   <-- d_gen"
        out.append(f"  d={d}: #new rel = {len(new):6d} (wraparound {n_wrap:5d}), "
                   f"rank = {rank:2d}{tag}")
    out.append(f"  SUMMARY n={n} p={p}: d_onset(wraparound) = {d_onset}, "
               f"d_gen = {d_gen if d_gen else f'>{dmax}'}")
    return d_onset, d_gen


def main():
    out = ["PROBE 466 N5 SOS-COLLAPSE d_gen EXTENSION (norm-10/12 scan; round-3 verifier)",
           "decides the open constant d_gen at generic beta=4 primes (parent scan: >8);",
           "dossier onset r0 = 5 predicts first balanced wraparounds at l1-norm 10."]
    results = []
    for n, dmax, ps in ((8, 12, (4129, 4153, 4177)),
                        (16, 10, (65537, 65617, 65633))):
        for p in ps:
            results.append((n, p, dmax) + analyze(n, p, dmax, out))
    out.append("\n================ CROSS-SCALE TABLE (extended scan) ================")
    out.append(f"{'n':>4} {'p':>8} {'beta':>6} {'scan':>5} {'d_onset':>8} {'d_gen':>6}")
    for n, p, dmax, d_on, d_gen in results:
        out.append(f"{n:>4} {p:>8} {plog(n, p):>6.3f} {dmax:>5} "
                   f"{str(d_on):>8} {str(d_gen) if d_gen else '>' + str(dmax):>6}")
    out.append("""
READING: d_gen <= 10 at generic beta=4 primes closes the honest-axiom (B2) version of
the collapse at those scales: the poly-size axiom set {circle, antipodal, relations of
l1-norm <= d_gen} already cuts out V exactly, so Theorem A applies over it and the SoS
degree window [d_onset, 6*k0] is O(1) end to end.  d_gen > 10 would leave B2 conditional
(the semantic Theorem A is unaffected either way).""")
    text = "\n".join(out)
    print(text)
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "_out_466_novel_sos_dgen10.txt"), "w") as f:
        f.write(text + "\n")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
#444 [pseudocyclic] lead — exact probe on PROPER mu_n (never full group, p >> n^3 where feasible).

LEAD: van Dam-Muzychuk: a cyclotomic association scheme is *pseudocyclic* iff all m nontrivial
eigenvalue multiplicities are equal. Equivalently for the cyclotomic scheme (all valencies = n
equal), the dual/amorphic ideal would force |eta_b| = sqrt(p) ... NO: that is the FULL group / the
Paley case (m=2). For general m the "pseudocyclic prize bound" the lead names is the EVEN
distribution of the spectrum, whose extreme is sqrt(n log m). The lead asks: is the deviation of the
cyclotomic scheme from EXACT pseudocyclicity a genuine NEW closed target = the log overshoot, or is
it max|eta| restated?

We measure, for proper mu_n (n | p-1, n=2^mu small, m=(p-1)/n, p prime, p >> n^2..n^3):

  (A) eta_b = Gauss periods (distinct values = m, indexed by quotient F_p^*/mu_n).
  (B) Multiplicity spread: the *eigenvalue* multiplicities of the Cayley graph Cay(F_p, mu_n).
      Pseudocyclic <=> these are all equal. Defect_mult = (max mult - min mult)/mean mult.
  (C) The pseudocyclic *target* value: a pseudocyclic m-class scheme on v=p vertices with valency
      n has nontrivial eigenvalues theta with theta(theta+1) tied to (v - ...). The clean
      "amorphic" benchmark is |eta| = sqrt(v)/sqrt(m) ... we compute the EXACT pseudocyclic
      eigenvalue and compare to sqrt(n log m) and to true max|eta|.
  (D) The DECISIVE test: is the "non-pseudocyclic defect" any quantity COMPUTABLE without already
      knowing max|eta|? We test 3 candidate defect functionals and check whether each
      (i) equals/upper-bounds max|eta| (=> restatement / no handle), or
      (ii) is provably <= something n,m-explicit while still controlling max|eta| (=> genuine).

  (E) Intersection numbers p^k_{ij} of the cyclotomic Bose-Mesner algebra: their deviation from
      the pseudocyclic ideal p^k_{ij} = n^2/v (off-diag) — does that deviation track log m?
"""
import numpy as np
from sympy import isprime, primitive_root
import math


def cyclotomic_data(p, n):
    """Return distinct Gauss periods eta (length m), and the full eigenvalue list of Cay(F_p,mu_n)."""
    g = primitive_root(p)
    m = (p - 1) // n
    # cosets c_i mu_n, i=0..m-1 ; coset i = { g^{i + m j} : j }
    cosets = [[pow(g, i + m * j, p) for j in range(n)] for i in range(m)]
    w = np.exp(2j * np.pi * np.arange(p) / p)
    # eta over quotient: eta indexed by coset k of the DUAL (characters chi_b, b in coset k)
    # eta_k = sum_{x in mu_n} e_p(g^k * x)  -- value of S(b) for b in coset k
    eta = np.array([sum(w[(pow(g, k, p) * x) % p] for x in cosets[0]) for k in range(m)])
    # Eigenvalues of the Cayley graph Cay(F_p, S=mu_n): lambda_b = sum_{s in mu_n} e_p(b s),
    # one per character b in F_p (b=0 gives n). Distinct nonzero-b values = eta (m of them),
    # each with multiplicity n (n characters per coset).
    return eta, m


def krein_and_intersection(p, n):
    """
    Compute the m+1 class scheme adjacency eigen-structure.
    Relations R_0 = identity, R_i = {(x,y): x-y in coset c_i} for i=1..m.
    Eigenmatrix P: P[k][i] = eta value of class i at eigenspace k (Gauss period of coset i under chi_k).
    Multiplicities f_k from Q-matrix / orthogonality.
    """
    g = primitive_root(p)
    m = (p - 1) // n
    cosets = [[pow(g, (i) + m * j, p) for j in range(n)] for i in range(m)]
    # class i (i=0..m-1) is difference-set = coset i  (each class has valency n)
    w = np.exp(2j * np.pi * np.arange(p) / p)
    # P[k,i] = eigenvalue of relation R_i on the eigenspace indexed by character g^k:
    #          = sum_{x in coset_i} chi_{g^k}(x) = sum_{x in coset_i} e_p(g^k x)
    P = np.zeros((m, m), dtype=complex)
    for k in range(m):
        gk = pow(g, k, p)
        for i in range(m):
            P[k, i] = sum(w[(gk * x) % p] for x in cosets[i])
    # eigenspace multiplicities: row k corresponds to characters in coset k of the dual; each has
    # multiplicity = n (number of characters), EXCEPT the all-ones (k giving trivial) -> handled.
    # Actually for the cyclotomic scheme the principal eigenspace is the all-ones (mult 1) and each
    # of the m "period classes" has multiplicity n... but distinct PERIOD VALUES can coincide,
    # FUSING eigenspaces and changing multiplicities. The TRUE eigenvalue multiplicities of the
    # graph Cay(F_p, coset_0) are what test pseudocyclicity. Compute them directly:
    A_eigs = []
    for b in range(1, p):
        val = sum(w[(b * x) % p] for x in cosets[0]).real
        A_eigs.append(round(val, 6))
    A_eigs.append(round(float(n), 6))  # b=0 eigenvalue = n (valency)
    vals, counts = np.unique(np.array(A_eigs), return_counts=True)
    return P, vals, counts


print("=" * 110)
print(" #444 PSEUDOCYCLIC DEFECT PROBE — proper mu_n, p >> n^2 .. n^3")
print("=" * 110)

# Choose proper subgroups: n = 2^mu, m growing, p prime, PROPER (m>=2), deep (p >> n^2).
configs = []
for mu in range(2, 7):          # n = 4,8,16,32,64
    n = 2 ** mu
    for m in range(2, 200):
        p = m * n + 1
        if not isprime(p):
            continue
        if p < n * n:           # require p >> n (deep-ish); we will tag deepness
            continue
        configs.append((p, n, m))

# keep a spread: per n, sample m geometrically
sel = {}
for (p, n, m) in configs:
    sel.setdefault(n, [])
    sel[n].append((p, n, m))

print(f"\n{'n':>4} {'m':>5} {'p':>9} {'maxeta':>8} {'sqrt(nlnm)':>10} {'ratio':>6} "
      f"{'#distmult':>9} {'multspread':>10} {'pseudo?':>8}")
print("-" * 110)
for n in sorted(sel):
    rows = sel[n]
    # sample of m
    idxs = sorted(set(min(i, len(rows) - 1) for i in
                      [0, len(rows)//8, len(rows)//4, len(rows)//2, 3*len(rows)//4, len(rows)-1]))
    for i in idxs:
        p, nn, m = rows[i]
        if p > 200000:   # keep brute O(p*n) feasible
            continue
        eta, _ = cyclotomic_data(p, n)
        maxeta = np.abs(eta).max()
        target = math.sqrt(n * math.log(m)) if m > 1 else 0.0
        ratio = maxeta / target if target > 0 else float('nan')
        _, vals, counts = krein_and_intersection(p, n)
        # exclude the valency eigenvalue (n) for the multiplicity-spread test
        nontrivial = [(v, c) for v, c in zip(vals, counts) if abs(v - n) > 1e-6]
        cs = np.array([c for _, c in nontrivial])
        spread = (cs.max() - cs.min()) / cs.mean() if len(cs) else 0.0
        pseudo = "YES" if spread < 1e-9 else "no"
        print(f"{n:>4} {m:>5} {p:>9} {maxeta:>8.3f} {target:>10.3f} {ratio:>6.3f} "
              f"{len(cs):>9} {spread:>10.4f} {pseudo:>8}")

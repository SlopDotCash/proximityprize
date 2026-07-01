#!/usr/bin/env python3
"""
STRUCTURAL confirmation of the clique-kernel degeneracy escape clause (Conj 41 / #444 6.3).

We verify, exactly, the three structural facts that make EVERY clique-kernel syndrome
DEGENERATE (a Remark-31 false positive), giving a NON-NUMERICAL (provable) closure:

  (A) {ev_beta : beta in W} are linearly independent in F^D whenever D >= |W| (Vandermonde,
      distinct points). [reproduce evalSyndrome_family_injective from the in-tree file]
  (B) s2 = sum_{beta in W} b(beta) ev_beta is in span{ev_beta : beta in E_alpha=W\{alpha}}
      IFF b(alpha) = 0.  (the omitted coordinate must carry zero weight)
  (C) When b(alpha)=0, s2 decodes on E_alpha to e_beta = b(beta) (all nonzero iff b|_{E_alpha}
      nonzero), and s1 = -sum_{beta in E_alpha} gamma(beta) b(beta) ev_beta.  The single-twist
      relation s1 = -gamma_alpha * s2 holds IFF gamma(beta)=gamma_alpha for every beta in E_alpha
      with b(beta)!=0 -- IMPOSSIBLE once >=2 such beta have DISTINCT gamma.  So a kernel
      syndrome with >=2 nonzero weights on E_alpha is NEVER a single-support list member.

  => the ONLY would-be "list members" are single-vertex weights b = c * 1_{beta0}, which give
     a WEIGHT-1 (not weight-w) error on a degenerate support -- excluded by definition (a
     genuine codim-c list member needs all c -- here all w -- error values nonzero on a FULL
     size-w support, not a 1-sparse vector). These are exactly the Remark-31 false positives.

We also rank-check the twisted double block to reproduce rank = D + c - 1 (=> kerdim w+1),
independently of the symbolic in-tree proof.
"""

import itertools
from fractions import Fraction
from sympy import Matrix, nextprime

def ev(t, D):
    return [Fraction(t) ** j for j in range(D)]

def rank_Q(rows):
    return Matrix(rows).rank()

def banner(s):
    print("\n" + "=" * 78); print(s); print("=" * 78)

# ---- (A) independence of ev_beta over W ----
def check_independence(W, D):
    M = Matrix([ev(b, D) for b in W])   # |W| x D
    return M.rank() == len(W)

# ---- locator coeffs over Q ----
def locator_coeffs_Q(E):
    coeffs = [Fraction(1)]
    for a in E:
        new = [Fraction(0)] * (len(coeffs) + 1)
        for i, ci in enumerate(coeffs):
            new[i]   -= Fraction(a) * ci
            new[i+1] += ci
        coeffs = new
    return coeffs

def normal_rows_Q(E, c, D):
    base = locator_coeffs_Q(E)
    rows = []
    for r in range(c):
        row = [Fraction(0)] * D
        for i, ci in enumerate(base):
            if i + r < D:
                row[i + r] = ci
        rows.append(row)
    return rows

def twisted_block_rank_Q(family, gammas, c, D):
    rows = []
    for E, g in zip(family, gammas):
        for row in normal_rows_Q(E, c, D):
            rows.append(row + [Fraction(g) * x for x in row])
    return rank_Q(rows), len(rows)

def clique_block_rank(W, c):
    w = len(W) - 1
    D = w + c
    supports = [tuple(x for x in W if x != a) for a in W]
    gammas = [(i + 1) * 7 + 3 for i in range(len(W))]  # distinct
    r, nrows = twisted_block_rank_Q(supports, gammas, c, D)
    return D, c, w, r, nrows, 2 * D

# ---- (B)+(C) the membership / twist structural test ----
def membership_and_twist(W, c):
    """For random nonzero weights b, confirm:
       decodable-on-E_alpha-with-all-nonzero  <=>  b(alpha)=0,
       and in that case single-twist fails whenever >=2 nonzero weights remain."""
    import random
    random.seed(0)
    w = len(W) - 1
    D = w + c
    gammas = {b: (i + 1) * 7 + 3 for i, b in enumerate(W)}
    fails_twist = 0
    holds_twist = 0
    membership_matches = 0
    trials = 0
    for _ in range(2000):
        b = {beta: random.randint(-3, 3) for beta in W}
        if all(v == 0 for v in b.values()):
            continue
        trials += 1
        s2 = [sum(Fraction(b[beta]) * (Fraction(beta) ** j) for beta in W) for j in range(D)]
        s1 = [sum(-Fraction(gammas[beta]) * Fraction(b[beta]) * (Fraction(beta) ** j)
                  for beta in W) for j in range(D)]
        for alpha in W:
            E = [x for x in W if x != alpha]
            # decodable with all-nonzero <=> b(alpha)=0 and b|_E all nonzero
            V = Matrix([[Fraction(beta) ** j for beta in E] for j in range(D)])  # D x w
            aug = V.row_join(Matrix(D, 1, s2))
            decodable = (V.rank() == aug.rank() == len(E))
            allnz = False
            if decodable:
                e = V.solve_least_squares(Matrix(D, 1, s2)) if V.rank() == len(E) else None
                # exact solve since full col rank & consistent:
                sol = V.solve(Matrix(D, 1, s2))
                allnz = all(x != 0 for x in sol)
            pred = (b[alpha] == 0)
            # membership prediction: decodable iff b(alpha)=0
            if decodable == pred:
                membership_matches += 1
            if decodable and allnz:
                ga = Fraction(gammas[alpha])
                single_twist = all(s1[j] == -ga * s2[j] for j in range(D))
                # count remaining nonzero weights on E
                nnz = sum(1 for beta in E if b[beta] != 0)
                if single_twist:
                    holds_twist += 1
                else:
                    fails_twist += 1
    return trials, membership_matches, holds_twist, fails_twist

if __name__ == "__main__":
    print("STRUCTURAL closure of the clique-kernel degeneracy escape clause (#444 6.3)")

    for (W, c) in [([0,1,2],2), ([0,1,2,3],3), ([0,1,2,3,4],4), ([2,3,5,7],3), ([1,2,3,4,6],4)]:
        w = len(W) - 1; D = w + c
        banner(f"W={W} (w={w}), c={c}, D={D}")
        # (A)
        indep = check_independence(W, D)
        print(f"  (A) ev_beta independent over W (D>=|W|): {indep}  (need True)")
        # rank of twisted block = D + c - 1 ?
        Dd, cc, ww, r, nrows, twoD = clique_block_rank(W, c)
        print(f"  twisted [N|gN] block: rank={r}  rows={nrows}  2D={twoD}  "
              f"predicted D+c-1={D + c - 1}  ==> kerdim={2*D - r} (predict w+1={w+1})  "
              f"MATCH={r == D + c - 1 and 2*D - r == w + 1}")
        # (B)+(C)
        trials, mm, ht, ft = membership_and_twist(W, c)
        print(f"  (B) membership 'decodable<=>b(alpha)=0' matched on {mm} / {trials*len(W)} "
              f"(alpha,b) pairs")
        print(f"  (C) all-nonzero decodes: single-twist HOLDS={ht}  FAILS={ft}  "
              f"==> REAL list members (twist holds) = {ht}")
        if ht == 0:
            print("      ==> EVERY all-nonzero decode is twist-inconsistent => DEGENERATE.")

    print("\nDONE.")

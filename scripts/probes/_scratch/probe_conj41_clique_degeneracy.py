#!/usr/bin/env python3
"""
DECISIVE TEST of the Conjecture 41 clique DEGENERACY ESCAPE CLAUSE (#444 off-BGK lead 6.3).

Setup (faithful to Conjecture41CliqueKernelStructure.lean / Round20CliqueKernel):
  - W = a (w+1)-vertex set; the clique supports are E_alpha = W \ {alpha}, |E_alpha| = w.
  - codimension excess c; window D = w + c; syndromes live in F^D.
  - ev_t = (1, t, t^2, ..., t^{D-1}) in F^D.
  - The twisted normal block [N_{E} | gamma N_{E}] has kernel (the WHOLE kernel, dim w+1):
        s1 = -sum_{beta in W} gamma(beta) b(beta) ev_beta,
        s2 =  sum_{beta in W} b(beta) ev_beta
    for any weight b : W -> F and twist gamma : W -> F.  (clique_kernel_mem, proven in-tree.)
  - rank [N|gN]_clique = D + c - 1, kerdim = 2D - (D+c-1) = w+1.

DECODING / "real list member" semantics (Chai-Fan, Remark 31):
  A genuine list member is an error vector e supported on a size-w support E_alpha with
  ALL w error values nonzero, whose syndrome (in BOTH blocks, via the twist gamma_alpha
  attached to E_alpha) equals the kernel syndrome (s1, s2).  A kernel syndrome is a
  REMARK-31 FALSE POSITIVE (degenerate) if for every support E_alpha on which it can be
  explained, the decoded error has some value = 0 (so the true support is a proper subset
  / the whole W, not a genuine size-w / size-c error).

ESCAPE CLAUSE (the thing we test):
  CLAIM: every clique-kernel syndrome is DEGENERATE -- decoding on each E_alpha forces
  some e_beta = 0.  If TRUE => Conj 41 floor holds OFF the BGK wall (non-character-sum
  closure).  If a kernel syndrome decodes to an ALL-NONZERO error on some E_alpha => it
  is a REAL list member => Conj 41 fails as posed (relocates to exponential-height residual).

We compute exactly over Q (Fraction) and mod good primes, c = 2 (K3), 3 (K4), 4 (K5),
small w/n, exhaustively over the kernel pencil basis and random/structured weights b.
"""

import itertools
from fractions import Fraction
from sympy import nextprime

# ---------------------------------------------------------------------------
# Field arithmetic: Q via Fraction, F_p via modular ints.  We abstract via a
# small helper so the SAME enumeration runs in char 0 and char p.
# ---------------------------------------------------------------------------

class QField:
    name = "Q"
    @staticmethod
    def of(x): return Fraction(x)
    @staticmethod
    def zero(): return Fraction(0)
    @staticmethod
    def is_zero(x): return x == 0
    @staticmethod
    def inv(x): return Fraction(1) / x

class FpField:
    def __init__(self, p): self.p = p; self.name = f"F_{p}"
    def of(self, x): return x % self.p
    def zero(self): return 0
    def is_zero(self, x): return (x % self.p) == 0
    def inv(self, x): return pow(x % self.p, self.p - 2, self.p)
    def mul(self, a, b): return (a * b) % self.p
    def add(self, a, b): return (a + b) % self.p
    def sub(self, a, b): return (a - b) % self.p

# ---------------------------------------------------------------------------
# Linear algebra over a field given as add/mul/inv lambdas (works for Q and Fp).
# We solve V e = s for e (least info: overdetermined; return solution iff consistent).
# ---------------------------------------------------------------------------

def solve_overdetermined(V, s, zero, is_zero, inv, mul, sub):
    """
    V: list of D rows, each row length k (the k columns ev_{beta}, beta in E).
    s: target vector length D.
    Returns (solvable, e) where e is the unique length-k solution if V has rank k
    and s in colspace(V); else (False, None).
    Gaussian elimination on the augmented [V | s].
    """
    D = len(V)
    k = len(V[0]) if D else 0
    # Build augmented matrix (copy)
    M = [list(V[i]) + [s[i]] for i in range(D)]
    pivot_rows = []
    row = 0
    for col in range(k):
        # find pivot in column col at or below `row`
        piv = None
        for r in range(row, D):
            if not is_zero(M[r][col]):
                piv = r; break
        if piv is None:
            # no pivot in this column -> V not full column rank; the column-space
            # may still contain s, but solution not unique. For our distinct-point
            # Vandermonde columns this never happens (full column rank), so treat as fail.
            return (False, None)
        M[row], M[piv] = M[piv], M[row]
        pv = M[row][col]
        ipv = inv(pv)
        M[row] = [mul(x, ipv) for x in M[row]]
        for r in range(D):
            if r != row and not is_zero(M[r][col]):
                f = M[r][col]
                M[r] = [sub(M[r][j], mul(f, M[row][j])) for j in range(k + 1)]
        pivot_rows.append((row, col))
        row += 1
        if row == D:
            break
    # after elimination: columns 0..k-1 should each have a pivot (full col rank)
    if len(pivot_rows) < k:
        return (False, None)
    # check consistency: any row with all-zero V-part but nonzero s-part => inconsistent
    e = [zero for _ in range(k)]
    for (r, col) in pivot_rows:
        e[col] = M[r][k]
    for r in range(D):
        # recompute residual quickly: rows beyond rank must have zero rhs
        if r >= len(pivot_rows):
            if not is_zero(M[r][k]):
                return (False, None)
    return (True, e)

# Wrappers for the two fields -------------------------------------------------

def make_ops(field):
    if isinstance(field, QField) or field is QField:
        zero = Fraction(0)
        return (lambda x: Fraction(x), zero,
                lambda x: x == 0,
                lambda x: Fraction(1) / x,
                lambda a, b: a * b,
                lambda a, b: a - b,
                lambda a, b: a + b)
    else:
        p = field.p
        return (lambda x: x % p, 0,
                lambda x: (x % p) == 0,
                lambda x: pow(x % p, p - 2, p),
                lambda a, b: (a * b) % p,
                lambda a, b: (a - b) % p,
                lambda a, b: (a + b) % p)

# ---------------------------------------------------------------------------
# The clique-kernel pencil and the decode test.
# ---------------------------------------------------------------------------

def ev(t, D, of, mul):
    """ev_t = (1, t, t^2, ..., t^{D-1})."""
    out = []
    cur = of(1)
    tt = of(t)
    for _ in range(D):
        out.append(cur)
        cur = mul(cur, tt)
    return out

def kernel_syndrome(W, b, gamma, D, of, mul, add, sub, zero):
    """
    s2 = sum_{beta in W} b(beta) ev_beta            (the 'second block' syndrome)
    s1 = -sum_{beta in W} gamma(beta) b(beta) ev_beta
    Returns (s1, s2) as length-D vectors.
    """
    s2 = [zero for _ in range(D)]
    s1 = [zero for _ in range(D)]
    for beta in W:
        evb = ev(beta, D, of, mul)
        bb = of(b[beta])
        gg = of(gamma[beta])
        for j in range(D):
            s2[j] = add(s2[j], mul(bb, evb[j]))
            s1[j] = sub(s1[j], mul(mul(gg, bb), evb[j]))
    return s1, s2

def decode_on_support(s, E, D, of, zero, is_zero, inv, mul, sub):
    """
    Solve s = sum_{beta in E} e_beta ev_beta for the error values e (size |E|).
    Returns (solvable, e_dict) ; e_dict maps beta->value.
    """
    Elist = list(E)
    # columns = ev_beta for beta in E
    cols = [ev(beta, D, of, mul) for beta in Elist]
    # V has shape D x |E|: V[i][j] = cols[j][i]
    V = [[cols[j][i] for j in range(len(Elist))] for i in range(D)]
    solvable, e = solve_overdetermined(V, s, zero, is_zero, inv, mul, sub)
    if not solvable:
        return (False, None)
    return (True, {Elist[j]: e[j] for j in range(len(Elist))})

# ---------------------------------------------------------------------------
# MAIN TEST per (W, c).
# ---------------------------------------------------------------------------

def run_case(W, c, field, weights_iter, gammas, label, verbose=False):
    """
    W: list of w+1 vertices (field elements as ints).
    c: codimension excess.  w = |W| - 1.  D = w + c.
    field: QField (singleton/class) or FpField instance.
    weights_iter: iterable of dicts beta->b(beta).
    gammas: dict beta->gamma(beta), distinct.
    Returns dict of statistics.
    """
    of, zero, is_zero, inv, mul, sub, add = make_ops(field)
    w = len(W) - 1
    D = w + c
    supports = [tuple(x for x in W if x != alpha) for alpha in W]  # E_alpha, size w

    n_kernel = 0
    n_decodable_some_support = 0
    n_allnz_decode = 0      # decodes to all-nonzero on some support (ignoring twist)
    n_real_listmember = 0   # all-nonzero AND single-twist s1 = -gamma_alpha s2 (a REAL member)
    real_examples = []
    allnz_examples = []

    for b in weights_iter:
        # need a nonzero weight to get a nonzero syndrome
        if all(is_zero(of(b[beta])) for beta in W):
            continue
        s1, s2 = kernel_syndrome(W, b, gammas, D, of, mul, add, sub, zero)
        n_kernel += 1
        # The genuine-list-member question:
        #   a real size-w error on support E_alpha must reproduce BOTH blocks with the
        #   support's OWN twist gamma_alpha:  (s1, s2) = (-gamma_alpha s2, s2), AND all
        #   w decoded values nonzero. We decode s2 on each E_alpha and check both.
        decoded_any = False
        allnz_here = False
        real_here = False
        for alpha in W:
            E = tuple(x for x in W if x != alpha)
            ok, e = decode_on_support(s2, E, D, of, zero, is_zero, inv, mul, sub)
            if not ok:
                continue
            decoded_any = True
            all_nonzero = all(not is_zero(e[beta]) for beta in E)
            ga = of(gammas[alpha])
            # single-twist consistency: s1 == -gamma_alpha * s2  (componentwise)
            neg_ga = sub(zero, ga)
            single_twist = all(is_zero(sub(s1[j], mul(neg_ga, s2[j]))) for j in range(D))
            if all_nonzero:
                allnz_here = True
                if len(allnz_examples) < 6:
                    allnz_examples.append((dict(b), alpha, {k: str(v) for k, v in e.items()},
                                           single_twist, bool(is_zero(of(b[alpha])))))
            if all_nonzero and single_twist:
                real_here = True
                if len(real_examples) < 6:
                    real_examples.append((dict(b), alpha, {k: str(v) for k, v in e.items()}))
        if decoded_any:
            n_decodable_some_support += 1
        if allnz_here:
            n_allnz_decode += 1
        if real_here:
            n_real_listmember += 1

    return {
        "label": label, "field": field.name if hasattr(field, "name") else "Q",
        "w": w, "c": c, "D": D,
        "n_kernel_tested": n_kernel,
        "n_decodable_some_support": n_decodable_some_support,
        "n_allnz_decode": n_allnz_decode,
        "n_real_listmember": n_real_listmember,
        "real_examples": real_examples,
        "allnz_examples": allnz_examples,
    }

# ---------------------------------------------------------------------------
# Weight enumerators.
# ---------------------------------------------------------------------------

def all_weights_small(W, vals):
    """All b: W -> vals (exhaustive small)."""
    keys = list(W)
    for combo in itertools.product(vals, repeat=len(keys)):
        yield {keys[i]: combo[i] for i in range(len(keys))}

def banner(s):
    print("\n" + "=" * 78); print(s); print("=" * 78)

if __name__ == "__main__":
    print("DECISIVE clique-kernel DEGENERACY ESCAPE-CLAUSE test (Conj 41 / #444 lead 6.3)")
    print("Question: does EVERY clique-kernel syndrome force some decoded error value = 0")
    print("(degenerate / Remark-31 false positive), OR is some kernel syndrome an")
    print("all-nonzero genuine size-w list member (=> Conj 41 fails as posed)?")

    # --- c = 2 (K3): W = 3 vertices, w = 2, supports E_alpha = pairs, D = 4 ---
    for (W, c, primes) in [
        ([0, 1, 2], 2, [1009, 1013]),          # K3 over small int vertices
        ([0, 1, 2, 3], 3, [1009, 1013]),       # K4 / c=3, w=3, D=6
        ([0, 1, 2, 3, 4], 4, [10007]),         # K5 / c=4, w=4, D=8
        ([1, 2, 4, 5], 3, [1009]),             # K4, non-consecutive vertices
    ]:
        w = len(W) - 1
        banner(f"CLIQUE W={W} (w={w}), c={c}")
        # distinct gammas
        gammas = {beta: (idx + 1) * 7 + 3 for idx, beta in enumerate(W)}
        # CHAR 0 (Q) -- exhaustive small weights
        vals = [-2, -1, 0, 1, 2]
        statsQ = run_case(W, c, QField, all_weights_small(W, vals), gammas, "Q-exhaustive")
        print(f"  [Q ] kernel={statsQ['n_kernel_tested']:>5}  "
              f"decodable={statsQ['n_decodable_some_support']:>5}  "
              f"all-nz-decode={statsQ['n_allnz_decode']:>5}  "
              f"REAL-list-member(all-nz & single-twist)={statsQ['n_real_listmember']:>5}")
        # CHAR p -- same weights
        for p in primes:
            fp = FpField(p)
            statsP = run_case(W, c, fp, all_weights_small(W, vals), gammas, f"Fp-exhaustive")
            print(f"  [F{p}] kernel={statsP['n_kernel_tested']:>5}  "
                  f"decodable={statsP['n_decodable_some_support']:>5}  "
                  f"all-nz-decode={statsP['n_allnz_decode']:>5}  "
                  f"REAL-list-member={statsP['n_real_listmember']:>5}")
        # Diagnostics: all-nz decodes -- is b(alpha)=0 always, and twist always inconsistent?
        if statsQ["allnz_examples"]:
            print("  -- all-NONZERO decode examples (b, removed alpha, e, single_twist?, b(alpha)==0?):")
            for (b, alpha, e, st, balpha0) in statsQ["allnz_examples"][:4]:
                print(f"     remove alpha={alpha}  b(alpha)=={b[alpha]}  e={e}  "
                      f"single_twist={st}  b(alpha)==0:{balpha0}")
        if statsQ["real_examples"]:
            print(f"  !!! REAL LIST MEMBERS FOUND (all-nonzero AND single-twist): "
                  f"{len(statsQ['real_examples'])} examples")
            for (b, alpha, e) in statsQ["real_examples"][:4]:
                print(f"     b={b}  remove alpha={alpha}  e={e}")
        else:
            print("  ==> ZERO real list members: every all-nonzero decode FAILS the single-twist")
            print("      relation s1=-gamma_alpha*s2 => DEGENERATE (Remark-31 false positive).")

    print("\nDONE.")

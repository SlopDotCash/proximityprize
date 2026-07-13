"""
G252c: BALANCED (histogram-preserving) phase-split annihilation test.

Codex correctly flagged that G252's earlier split search over "flip the first k
by phase order" includes the degenerate k=0 (all +1) and k=len (all -1)
assignments, which makes `min split covariance <= 0` tautological for any nonzero
covariance and does NOT test a histogram-preserving move.

A global phase-discrepancy budget preserves the phase HISTOGRAM. The admissible
move is therefore a sign vector s in {+1,-1}^N with EQUAL numbers of +1 and -1
(sum s = 0), i.e. a *balanced* split (N even). We recompute the achievable real
covariance restricted to balanced sign vectors and report:

  bal_min_cov  = min over balanced sign vectors of Re<s, W conj(R)>
  bal_can_zero = (bal_min_cov <= 0)   [balanced move can annihilate]
  bal_frac     = bal_min_cov / triangle

The exact minimum over balanced sign vectors is a cardinality-constrained
assignment: with per-index real contribution c_i = Re(W_i conj(R_i)) the
UNCONSTRAINED min flips exactly the indices with c_i > 0. The BALANCED min forces
exactly N/2 flips: pick the N/2 indices with the largest c_i to flip (each flip
changes the objective by -2 c_i, so flipping the largest c_i first is optimal),
giving  bal_min_cov = sum_i c_i - 2 * (sum of top N/2 c_i).
We also report the achieved covariance of the *specific* balanced split used in
the Lean invariant (first half +1, second half -1 by phase order) for honesty.
"""
import numpy as np, cmath, math

def is_prime(x):
    if x < 2: return False
    i = 2
    while i*i <= x:
        if x % i == 0: return False
        i += 1
    return True

def primitive_root(p):
    phi = p-1; facs = []; x = phi; d = 2
    while d*d <= x:
        if x % d == 0:
            facs.append(d)
            while x % d == 0: x //= d
        d += 1
    if x > 1: facs.append(x)
    for gg in range(2, p):
        if all(pow(gg, (p-1)//f, p) != 1 for f in facs): return gg
    return None

def run(n, p, r):
    if not is_prime(p) or (p-1) % n != 0: return None
    m = (p-1)//n
    g = primitive_root(p)
    ind = {}; x = 1
    for e in range(p-1):
        ind[x] = e; x = (x*g) % p
    def ql(t): return ind[t] % m
    def sign_r(l): return math.cos(2*math.pi*r*l/m)
    Rr = np.zeros(m)
    for a in range(1, p):
        b = (2-a) % p
        if b == 0: continue
        Rr[ql(b)] += sign_r(ql(a))
    Rr -= Rr.mean()
    psis = np.array([cmath.exp(2j*math.pi*t/p) for t in range(1, p)])
    labels = np.array([ql(t) for t in range(1, p)])
    m_arr = np.arange(m)
    What = np.zeros(m, dtype=complex); Rhat = np.zeros(m, dtype=complex)
    for a in range(m):
        ph = np.exp(2j*math.pi*a*labels/m)
        What[a] = np.sum(psis*ph)
        ph2 = np.exp(2j*math.pi*a*m_arr/m)
        Rhat[a] = np.sum(Rr*ph2)
    idx = np.arange(1, m)
    W = What[idx]; R = Rhat[idx]
    c = np.real(W*np.conj(R))            # per-index real contribution
    cov = float(np.sum(c))
    tri = float(np.sum(np.abs(W)*np.abs(R)))
    N = len(idx)
    # A strictly balanced sign vector (Sigma s = 0, equal +1/-1 counts) exists only
    # for EVEN N.  For odd N the histogram-preserving constraint is unsatisfiable, so
    # we mark the cell and skip the headline claim there.
    if N % 2 != 0:
        return dict(n=n, p=p, r=r, m=m, N=N, skipped_odd=True)
    # exact balanced minimum: force exactly N/2 flips, flip the largest c_i
    half = N // 2
    cs = np.sort(c)[::-1]                 # descending
    bal_min = cov - 2.0*float(np.sum(cs[:half]))
    # unconstrained minimum (for contrast): flip all positive c_i
    unc_min = cov - 2.0*float(np.sum(c[c > 0]))
    # the SPECIFIC Lean-style split: order by phase(R), flip second half
    order = np.argsort(np.angle(R))
    s = np.ones(N); s[order[half:]] = -1.0
    lean_split = float(np.sum(s*c))
    n_plus = int(np.sum(s > 0)); n_minus = int(np.sum(s < 0))
    return dict(n=n, p=p, r=r, m=m, N=N, cov=cov, tri=tri, skipped_odd=False,
                bal_min=bal_min, bal_can_zero=(bal_min <= 1e-6*max(1.0, abs(tri))),
                bal_frac=bal_min/(tri+1e-30), unc_min=unc_min,
                lean_split=lean_split, lean_balanced=(n_plus == n_minus))

# NOTE ON WEIGHT: sign_r below is a cosine/Krawtchouk-style SURROGATE for the rank-r
# Newton packet coefficient, not the literal G245 coefficient.  The claim tested is
# structural (phase/row decoupling under a histogram-preserving move) and is stable
# across this surrogate; it is not a numerical estimate of the true covariance.
#
# We report ONLY even-N cells (odd N has no exactly-balanced sign vector).
print("G252c BALANCED (histogram-preserving) split annihilation test")
print("surrogate rank weight; even-N cells only (strict Sigma s = 0 requires even N)")
print("="*74)
for (n, p) in [(8,1009),(8,2003),(16,1009),(8,4001),(16,2003),(8,8009),(16,4001),
               (8,3001),(16,3457),(8,6961)]:
    for r in (5, 6):
        res = run(n, p, r)
        if res is None: continue
        if res.get('skipped_odd'):
            print(f"n={res['n']} p={res['p']} r={res['r']} m={res['m']} N={res['N']} "
                  f"SKIPPED (odd N, no balanced sign vector)")
            continue
        print(f"n={res['n']} p={res['p']} r={res['r']} m={res['m']} N={res['N']} "
              f"cov={res['cov']:.3g} bal_min={res['bal_min']:.3g} "
              f"bal_frac={res['bal_frac']:.4f} bal_zero={res['bal_can_zero']} "
              f"lean_balanced={res['lean_balanced']}")
print("="*74)
print("bal_min = exact min real covariance over BALANCED sign vectors (sum s = 0).")
print("bal_zero=True  => a histogram-preserving move drives covariance <= 0")
print("   => global phase-discrepancy control cannot lower-bound fixed-row cov => NO-GO.")
print("bal_zero=False => balanced moves cannot annihilate; joint law is rigid => LIVE.")

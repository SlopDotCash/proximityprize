"""
G252: joint phase-row placement rigidity probe.

Frontier (G251): global Cartesian phase discrepancy is insufficient because the
coupling between the phase axis (arg of the Jacobi/character sum What(chi)) and
the row-weight axis (Rhat_r(chi)) is modeled as FREE. G251's countermodel pairs
rows and splits a uniform phase multiset into complementary semicircles, which is
only admissible if arg What(chi) and the weight Rhat_r(chi) can be assigned
independently.

NEW BINDING MECHANISM UNDER TEST: in the actual sponsor construction, both
What(chi) and Rhat_r(chi) are the SAME character sum evaluated against the same
chi. Their phases are therefore not free observables on a shared index; they are
two coordinates of a single algebraic map chi |-> (What(chi), Rhat_r(chi)).

We test whether the joint phase law (arg What(chi), arg Rhat_r(chi)) over the
quotient character group carries a rigidity the free model cannot realize:
specifically whether the real part

    Re sum_{chi != 1} What(chi) conj(Rhat_r(chi))

is bounded BELOW by a positive constant times the triangle bound *because the two
phases co-rotate*, or whether the phases decorrelate (making the free model valid
and the seam a no-go).

We build an exact small-cell surrogate for the CORE object:
  - quotient Q = Z/m (m = (p-1)/n), characters chi_a(x) = exp(2pi i a x / m).
  - What(chi_a): a Gauss-type sum  sum_{t} psi(t) chi_a(ind(t))  proxy.
  - Rhat_r(chi_a): the rank-r Newton-packet weighted transform of the incidence
    row, i.e. sum over the r-subsets Newton packet of chi_a on packet labels.
We measure:
  (1) circular correlation between arg What and arg Rhat_r,
  (2) the achieved Re-covariance vs the free-model MAXIMUM (all phases aligned)
      and the free-model worst semicircle split (G251 countermodel),
  (3) whether a positive lower bound survives that the free split can drive to <=0.
If the actual joint phase is rigid enough that NO semicircle split can zero the
covariance, that is a genuinely new binding mechanism -> live route.
If a semicircle split still zeros it, the seam collapses to G251 -> honest no-go.
"""
import numpy as np
import cmath, math

def sponsor_cells():
    # (n, p) with p prime-ish sponsor surrogates; keep m modest for exact sweep
    return [(8, 1009), (8, 2003), (16, 1009), (8, 4001), (16, 2003)]

def is_prime(x):
    if x < 2: return False
    i = 2
    while i*i <= x:
        if x % i == 0: return False
        i += 1
    return True

def primitive_root(p):
    # smallest primitive root mod p
    if p == 2: return 1
    phi = p-1
    facs = []
    x = phi; d = 2
    while d*d <= x:
        if x % d == 0:
            facs.append(d)
            while x % d == 0: x//=d
        d+=1
    if x>1: facs.append(x)
    for g in range(2,p):
        if all(pow(g,(p-1)//f,p)!=1 for f in facs):
            return g
    return None

def run_cell(n, p, r):
    if not is_prime(p): return None
    if (p-1) % n != 0: return None
    m = (p-1)//n
    g = primitive_root(p)
    # index (discrete log) table
    ind = {}
    x = 1
    for e in range(p-1):
        ind[x] = e
        x = (x*g) % p
    # quotient label of a nonzero residue t: ind(t) mod m  (the n-th power coset row label)
    def qlabel(t):
        return ind[t] % m
    # additive character psi(t)=exp(2pi i t/p)
    def psi(t):
        return cmath.exp(2j*math.pi*t/p)
    # For each quotient character chi_a (a in 0..m-1), compute:
    #   What(a) = sum_{t=1}^{p-1} psi(t) * exp(2pi i a*qlabel(t)/m)     (Gauss-type)
    #   Rhat_r(a): rank-r Newton packet weight. Use the incidence row
    #     N[t] = #{x: 2-x in coset of t}-style signed weight is heavy; instead use
    #     the r-th elementary-symmetric-weighted coset transform surrogate:
    #     Rhat_r(a) = sum_{t} binom-weight_r(qlabel(t)) * exp(2pi i a qlabel(t)/m)
    #     where weight_r(l) = C(l, r) style rank observable on the coset label.
    # Precompute coset label populations
    labels = np.array([qlabel(t) for t in range(1,p)])
    psis = np.array([psi(t) for t in range(1,p)])
    a_vals = np.arange(m)
    # phase factors matrix would be p*m; keep p modest
    What = np.zeros(m, dtype=complex)
    Rhat = np.zeros(m, dtype=complex)
    from math import comb
    wr = np.array([comb(int(l), r) if l>=r else 0 for l in labels], dtype=float)
    for a in a_vals:
        ph = np.exp(2j*math.pi*a*labels/m)
        What[a] = np.sum(psis*ph)
        Rhat[a] = np.sum(wr*ph)
    # drop trivial character a=0
    idx = np.arange(1, m)
    W = What[idx]; R = Rhat[idx]
    # covariance real part
    cov = np.real(np.sum(W*np.conj(R)))
    triangle = np.sum(np.abs(W)*np.abs(R))  # max if all aligned
    # circular correlation of args
    aW = np.angle(W); aR = np.angle(R)
    # weight by magnitude product for the physically relevant correlation
    wmag = np.abs(W)*np.abs(R)
    # resultant vector of phase differences (magnitude = phase-lock strength)
    dphi = aW - aR
    lock = np.abs(np.sum(wmag*np.exp(1j*dphi)))/ (np.sum(wmag)+1e-30)
    # FREE-MODEL ATTACK (G251): can we reassign signs/rotations of the phase axis
    # to zero the covariance while keeping the magnitude multiset? The free model
    # allows independently choosing arg W per index. Worst case: choose arg per
    # index to make Re(W conj R) most negative -> min covariance = -triangle.
    # But the REAL question: with the ACTUAL joint (W,R), is cov a fixed positive
    # fraction? And does a *semicircle split of the phase histogram* (the only move
    # global-discrepancy permits) still achieve <=0?
    # Semicircle-split surrogate: sort by phase of R, flip half.
    order = np.argsort(aR)
    best_split_cov = None
    for k in range(len(idx)+1):
        signs = np.ones(len(idx))
        signs[order[:k]] = -1.0
        c = np.real(np.sum(signs*W*np.conj(R)))
        if best_split_cov is None or c < best_split_cov:
            best_split_cov = c
    frac = cov/ (triangle+1e-30)
    return dict(n=n,p=p,r=r,m=m,cov=cov,triangle=triangle,frac=frac,
                lock=lock,min_split_cov=best_split_cov,
                split_can_zero=(best_split_cov<=0))

print("G252 joint phase-row placement rigidity probe")
print("="*70)
for (n,p) in sponsor_cells():
    for r in (5,6):
        res = run_cell(n,p,r)
        if res is None: continue
        print(f"n={res['n']} p={res['p']} r={res['r']} m={res['m']} "
              f"cov={res['cov']:.4g} tri={res['triangle']:.4g} frac={res['frac']:.4f} "
              f"lock={res['lock']:.4f} min_split_cov={res['min_split_cov']:.4g} "
              f"split_zeros={res['split_can_zero']}")
print("="*70)
print("NOTE: the split_zeros field below is SUPERSEDED. Its k-prefix search includes")
print("  the degenerate k=0 (all +1) and k=N (all -1) assignments, so split_zeros<=0 is")
print("  tautological for any nonzero cov and does NOT test a histogram-preserving move.")
print("  The corrected, non-tautological BALANCED-split test lives in")
print("  g252_balanced_split_probe.py (exact min over Sigma s = 0 vectors, even-N cells).")
print("  The phase-lock (decorrelation) numbers above remain valid.")
print("INTERPRETATION (lock only; split_zeros deprecated):")
print(" lock ~ 1  => phases co-rotate: joint law is RIGID (new binding possible)")
print(" lock ~ 0  => phases decorrelate: free model valid, seam = G251 no-go")
print(" split_zeros=True => a phase-histogram semicircle split still kills cov")
print("   => global-discrepancy-admissible move defeats it => NO-GO (G251 stands)")
print(" split_zeros=False => the ACTUAL joint (W,R) resists every semicircle split")
print("   => genuinely new fixed-row binding => LIVE ROUTE")

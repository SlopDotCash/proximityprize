"""
C020 attack: is CS25's fourier_pair_identity off-diagonal the SAME spectral object as
the prize Gauss-period sup-norm M(n) = max_{b != 0} |sum_{x in mu_n} e_p(b x)| ?

Connection claim (C020):
  (1) CS25 fourier_pair_identity (proven Lean lemma, CS25FourierIdentity.lean):
      |G|*#{(w,f) in B^2 : w-f in C} = sum_psi Shat(psi) Shat(-psi);
      psi=0 term = |B|^2; off-diagonal = q^{k-n} sum_{psi != 0} ||Shat(psi)||^2  (DUAL-CODE L2 char sum).
  (2) LineIncidenceSpectral.lineIncidence_spectral (proven Lean lemma):
      #{gamma : s0 + gamma s1 in S}*|V| = |F| * sum_{psi perp s1} sum_{s in S} psi(s0 - s).
  (3) CLAIM: with B=syndrome ball, C^perp=line direction s1, the surviving dual frequencies'
      WORST Fourier coefficient is EXACTLY M(n) = max_b |sum_{x in mu_n} e_p(b x)|.
      => CS25 L2 Parseval mass and prize L-inf sup-norm are "the SAME Parseval mass".

Honest tests:
  A. Verify CS25 fourier_pair_identity numerically (both sides) on a concrete F_q, C, B.
  B. The prize content: per-frequency coefficient over a mu_n set is the Gauss-period sum
     C(b) = sum_{x in mu_n} e_p(b x).  Check worst |C(b)|, b!=0  == M(n)  (tautology / consistency).
  C. The DISCRIMINATING test: CS25 only delivers the L2 SUM sum_b|C(b)|^2 (= q*n, Parseval, FREE),
     NOT the worst single |C(b*)| = M(n). Show the L2 mass is regime-INDEPENDENT (= q*n exactly,
     trivial), while M(n) is the open object. So the identity is REAL but the prize content (worst
     frequency) is exactly what CS25's L2 identity DISCARDS. Quantify the gap sqrt(L2 mass)/M(n).
"""
import cmath, math
import numpy as np
from itertools import product

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def primes_1modn(n, beta_lo, beta_hi, count):
    lo = int(n**beta_lo); hi = int(n**beta_hi)
    out=[]
    q = 1 + ((lo-1)//n)*n
    while q < lo: q += n
    while q <= hi and len(out) < count:
        if is_prime(q): out.append(q)
        q += n
    return out

def primitive_root(q):
    m=q-1; fac=set(); d=2
    while d*d<=m:
        if m%d==0:
            fac.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.add(m)
    for g in range(2,q):
        if all(pow(g,(q-1)//p,q)!=1 for p in fac): return g
    raise RuntimeError

def subgroup(g, n, q):
    h = pow(g, (q-1)//n, q)
    s=[]; x=1
    for _ in range(n):
        s.append(x); x=(x*h)%q
    assert len(set(s))==n
    return np.array(s, dtype=np.int64)

# ---------- PART A: CS25 identity numeric check (small field, complex) ----------
def verify_cs25_identity():
    p = 5; length = 2
    F = list(range(p))
    c = (1,2)                                  # C = span<c>, plays role of line direction s1
    Cset = {tuple((a*ci)%p for ci in c) for a in F}
    B = [v for v in product(F,repeat=length) if sum(1 for t in v if t!=0)<=1]   # weight<=1 ball
    w = lambda t: cmath.exp(2j*math.pi*(t%p)/p)
    Gcard = p**length//p
    cnt = sum(1 for x in B for y in B
              if tuple((x[i]-y[i])%p for i in range(length)) in Cset)
    LHS = Gcard*cnt
    chars = [u for u in product(F,repeat=length) if sum(u[i]*c[i] for i in range(length))%p==0]
    assert len(chars)==Gcard
    RHS = 0+0j
    for u in chars:
        Sh  = sum(w(sum(u[i]*x[i] for i in range(length))) for x in B)
        Shm = sum(w(-sum(u[i]*x[i] for i in range(length))) for x in B)
        RHS += Sh*Shm
    return LHS, RHS, abs(LHS-RHS.real)

# ---------- PART B/C: Gauss-period coefficients vs M(n) and L2 (Parseval) mass ----------
def coeffs_abs2_all_b(mu, q):
    """|C(b)|^2 for all b in 0..q-1, C(b)=sum_{x in mu} e_p(b x). Vectorized."""
    b = np.arange(q, dtype=np.int64)
    # phases for each x: exp(2pi i b x / q); sum over x.
    acc = np.zeros(q, dtype=np.complex128)
    for x in mu:
        acc += np.exp(2j*math.pi*((b*x) % q)/q)
    return np.abs(acc)**2

def analyse(n, q, g):
    mu = subgroup(g, n, q)
    a2 = coeffs_abs2_all_b(mu, q)
    l2_total = float(a2.sum())                 # sum_b |C(b)|^2
    worst_nonzero = float(math.sqrt(a2[1:].max()))  # M(n) = max_{b!=0} |C(b)|
    l2_offdiag = float(a2[1:].sum())           # CS25 off-diagonal L2 mass
    parseval = q*n                             # Parseval prediction sum_b|C(b)|^2 = q*|mu|
    return {
        'n': n, 'q': q, 'beta': math.log(q)/math.log(n),
        'M(n)': worst_nonzero,
        'l2_total': l2_total,
        'parseval_qn': parseval,
        'parseval_holds': abs(l2_total-parseval) < 1e-3*parseval,
        'l2_offdiag': l2_offdiag,
        'l2_offdiag_pred': q*n - n*n,
        'sqrt_offdiag': math.sqrt(l2_offdiag),
        'sqrt_offdiag_over_Mn': math.sqrt(l2_offdiag)/worst_nonzero,
        'Mn_over_sqrt_nlogq': worst_nonzero/math.sqrt(n*math.log(q/n)),
    }

if __name__ == '__main__':
    print("="*80)
    print("PART A: CS25 fourier_pair_identity numeric check (LHS == RHS)")
    LHS, RHS, err = verify_cs25_identity()
    print(f"  LHS={LHS}  RHS={RHS.real:.6f}(+{RHS.imag:.1e}i)  |err|={err:.2e}  HOLDS={err<1e-9}")
    print()
    print("="*80)
    print("PART B/C: Gauss-period coeffs vs prize M(n) and the L2/Parseval mass")
    print("  PRIZE REGIME: proper dyadic mu_n < F_q*, q=1 mod n, q~n^4-n^5")
    print()
    print(f"  {'n':>4} {'q':>10} {'beta':>5} {'M(n)':>9} {'L2tot':>12} {'=q*n?':>6} "
          f"{'sqrt(offdiag)':>13} {'sqrt(L2)/M':>11} {'M/sqrt(n logq)':>14}")
    for n in (8, 16, 32, 64):
        # keep q moderate so q-length numpy arrays fit fast; one prime in [n^4, n^4.5]
        qs = primes_1modn(n, 4.0, 4.5, 1)
        for q in qs:
            g = primitive_root(q)
            r = analyse(n, q, g)
            print(f"  {r['n']:>4} {r['q']:>10} {r['beta']:>5.2f} {r['M(n)']:>9.3f} "
                  f"{r['l2_total']:>12.1f} {str(r['parseval_holds']):>6} "
                  f"{r['sqrt_offdiag']:>13.1f} {r['sqrt_offdiag_over_Mn']:>11.2f} "
                  f"{r['Mn_over_sqrt_nlogq']:>14.3f}")
    print()
    print("  INTERPRETATION:")
    print("   - L2tot == q*n EXACTLY (Parseval) is regime-INDEPENDENT and FREE => this is")
    print("     the 'same Parseval mass' the connection points to. CS25 off-diag = q*n - n^2.")
    print("   - sqrt(L2)/M ~ sqrt(q/?) is LARGE & GROWS with q (the sqrt-loss): the L2 mass")
    print("     does NOT pin M(n). M(n)/sqrt(n log q) is the BOUNDED-but-open prize constant.")
    print("   - => identity is REAL (objects coincide) but CS25 delivers L2 (free), the prize")
    print("     needs L-inf worst frequency = M(n) = the BGK open core. Connection welds to W-BGK.")

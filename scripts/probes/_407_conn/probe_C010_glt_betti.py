#!/usr/bin/env python3
"""
C010 attack: "GLT identity makes the anomaly defect LITERALLY the Hasse-Weil Betti error;
W-anomaly = W-Betti by an exact equation, proven at r=2."

We test FOUR distinct sub-claims of C010 at PROPER-SUBGROUP primes (dyadic mu_n, q~n^beta,
beta~4, n << sqrt q -- the prize regime, NOT the full group):

  (S1) GLT r=2 EXACT identity:  V4 = sum_s eta_s^4 = 3p(n-1) - n^3 exactly (zero error term).
  (S2) The moment-to-hypersurface IDENTITY: V_{2r} = sum_s eta_s^{2r} equals an exact
       affine point count of x_1^n + ... + x_{2r}^n = 0 ? (the GLT mechanism). We check the
       exact linear relation E_r-as-period-sum  <->  N(hypersurface) at r=2,3.
  (S3) The "anomaly defect IS the Hasse-Weil error" claim, made PRECISE. The char-0 ("Gaussian")
       reference for V_{2r} of m mean-zero unit-circle periods of L2-size sqrt(p) is
       V_{2r}^C = (2r-1)!! * m * p^r / m^r-ish ... we must define the reference exactly. We compute
       the ACTUAL defect = V_{2r} - leading_diagonal and ask: is it <= 2*genus*sqrt(p)*(scale)?
  (S4) r>=3 CROSSOVER claim: does the Betti error m^{2r-1} sqrt(p) overtake the diagonal
       (2r-1)!! n^r m at some r, and does that r match CharSumMomentDeepWall r_max = 2 log_n p ?

Exact integer arithmetic for point counts; complex only as cross-check on the period moments
(which are integers up to fp).
"""
import cmath
import numpy as np
from math import comb, isqrt

# ---------- number theory ----------
def is_prime(m):
    if m < 2: return False
    small = [2,3,5,7,11,13,17,19,23,29,31,37]
    for q in small:
        if m % q == 0: return m == q
    d = m-1; r = 0
    while d % 2 == 0: d//=2; r+=1
    for a in small:
        x = pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(r-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def factorize(m):
    s=set(); d=2
    while d*d<=m:
        while m%d==0: s.add(d); m//=d
        d+=1
    if m>1: s.add(m)
    return s

def gen_Fp_star(p):
    F=factorize(p-1)
    for h in range(2,p):
        if all(pow(h,(p-1)//q,p)!=1 for q in F): return h
    return None

def find_prime(n, beta):
    # smallest prime p = 1 mod n with p >= n^beta (proper subgroup: n | p-1, n^2 < p)
    lo=int(n**beta); p=lo + ((1-lo) % n)
    if p < lo: p += n
    while True:
        if p>2 and is_prime(p) and (p-1)%n==0: return p
        p+=n

# ---------- the d2pow-th power residue / period machinery ----------
def double_well_factor():
    pass

# ---------- EXACT moment of mu_n periods via residue counting ----------
def gauss_periods_exact_moment(p, n, r2):
    """
    V_{r2} = sum over the m=(p-1)/n cosets b of (eta_b)^{r2}, where
    eta_b = sum_{x in mu_n} zeta^{b x},  zeta = e(1/p).
    Computed via complex (high precision enough for moderate p), returned as nearest int.
    """
    g0 = gen_Fp_star(p)
    m = (p-1)//n
    gen_mu = pow(g0,(p-1)//n,p)
    mu = [pow(gen_mu,i,p) for i in range(n)]
    # coset reps of mu_n in F_p^*  (m of them)
    seen=set(); reps=[]; b=1
    while len(reps)<m and b<p:
        if b not in seen:
            reps.append(b)
            for x in mu: seen.add(b*x%p)
        b+=1
    etas = np.array([sum(cmath.exp(2j*cmath.pi*((b*x)%p)/p) for x in mu).real for b in reps])
    V = float(np.sum(etas**r2))
    return V, m, etas

# ---------- EXACT count of the GLT diagonal-equation hypersurface ----------
def hypersurface_count_exact(p, n, k):
    """
    Exact #{ (x_1,...,x_k) in (F_p)^k : x_1^n + ... + x_k^n = 0 }  (affine, including 0s).
    Uses the n-th power character convolution.  For k=2r this is the GLT object.
    Computed exactly via the distribution of x^n over F_p.
    """
    # count of each value attained by x^n (n-th powers); image is mu_n-cosets-of-powers + 0
    cnt = {}
    for x in range(p):
        v = pow(x,n,p)
        cnt[v] = cnt.get(v,0)+1
    # number of solutions to sum_{i} v_i = 0 with each v_i an n-th power value (weighted by cnt)
    # do it via DFT over Z/p of the weight vector
    w = np.zeros(p)
    for v,c in cnt.items(): w[v]=c
    W = np.fft.fft(w)
    conv = (W**k)
    # number of tuples summing to 0 = (1/p) sum_t prod = inverse-DFT at 0
    val = np.fft.ifft(conv)[0].real
    return round(val)

# =========================================================
print("="*78)
print("C010 attack -- PROPER-SUBGROUP regime (dyadic mu_n, q~n^4, n^2<<q)")
print("="*78)

for n in (8,16,32,64):
    p = find_prime(n,4.0)
    m = (p-1)//n
    print(f"\n--- n={n}  p={p}  m=(p-1)/n={m}   (p/n^4={p/n**4:.2f}, n^2/p={n*n/p:.2e}) ---")

    # (S1) r=2 exact identity
    V4, _, etas = gauss_periods_exact_moment(p,n,4)
    glt_r2 = 3*p*(n-1) - n**3   # GLT Thm1(a) for even k
    print(f"(S1) V4 measured = {V4:.3f}   3p(n-1)-n^3 = {glt_r2}   diff = {V4-glt_r2:.3e}  "
          f"=> r=2 identity {'HOLDS' if abs(V4-glt_r2)<1e-3 else 'FAILS'}")

    # (S2) moment <-> hypersurface identity at r=2 (k=4) and r=3 (k=6)
    # GLT: sum_s eta_s^{2r} relates to N_k = #{sum x_i^n = 0} via a known LINEAR formula.
    # The exact relation (GLT / standard Gauss-period moment identity):
    #   sum_{b in F_p^*} (sum_{x in mu_n} zeta^{bx})^{k}  (sum over ALL p-1 nonzero b, with
    #   eta constant on cosets so = n^? ...). We test the cleanest exact statement:
    #   N_k = #{(x_1..x_k) in F_p^k: x_1^n+...+x_k^n=0}
    #       = p^{k-1} + (1/p)* sum_{t in F_p^*} (eta-type sum)^k   [standard]
    # Concretely:  N_k - p^{k-1}  must equal  (m/?)*V_k(periods)  exactly. We just print both
    # exact integers and the deduced linear coefficient.
    for r in (2,3):
        k = 2*r
        if p**(k-1) > 6e8 and n>=32:   # keep FFT count tractable
            print(f"(S2) r={r}: skipped (p^{k-1} too large for exact count at n={n})")
            continue
        if p**(k-1) > 6e8:
            print(f"(S2) r={r}: skipped (count too large)")
            continue
        Nk = hypersurface_count_exact(p,n,k)
        Vk,_,_ = gauss_periods_exact_moment(p,n,k)
        defect = Nk - p**(k-1)        # N_k - p^{k-1}
        # relation defect == coeff * Vk ?  coeff should be a clean rational; report it
        coeff = defect / Vk if abs(Vk)>1e-6 else float('nan')
        print(f"(S2) r={r} k={k}: N_k={Nk}  p^(k-1)={p**(k-1)}  N_k-p^(k-1)={defect}  "
              f"V_k(periods)={Vk:.1f}  (N_k-p^(k-1))/V_k = {coeff:.6f}")

    # (S4) crossover diagnostic: compare measured deep moment to diagonal vs Betti error
    for r in (2,3,4):
        k=2*r
        Vk,_,_ = gauss_periods_exact_moment(p,n,k)
        diag = (np.prod([2*j-1 for j in range(1,r+1)]) ) * (n**r) * m   # (2r-1)!! n^r m
        betti_err = (m**(k-1)) * (p**0.5)   # crude m^{2r-1} sqrt p
        print(f"(S4) r={r}: V_{k}={Vk:.3e}  diagonal (2r-1)!! n^r m={diag:.3e}  "
              f"V/diag={Vk/diag:.3f}  [crude Betti m^(2r-1)sqrt(p)={betti_err:.3e}]")

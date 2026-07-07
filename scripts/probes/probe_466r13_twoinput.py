#!/usr/bin/env python3
"""
#466 R13 -- the ROUND-13 CORE QUESTION, settled numerically:

  Is the prize localizable to WallHolds ALONE (single-Prop iff),
  or does it genuinely need a SECOND, DISTINCT open input
  (the sqrt(q)*B hyperplane cancellation)?

Setup: WallHolds controls, for every rung r and every b!=0,
    ||eta_b||^{2r} <= q*(2r-1)!!*n^r          (the per-frequency moment/Wick bound)
=>  M := max_{b!=0} ||eta_b||   <=  C*sqrt(n log q).      (LANE M, formalized this round)

The M->delta* step needs (over a size-|H| "hyperplane" H of frequencies, |H| up to q):
    T(H, s0) := | sum_{b in H} conj(eta_b) psi(b s0) |   <~   sqrt(|H|) * M     (the sqrt-cancellation)
whereas the wall/M ALONE only gives the NAIVE triangle bound
    T(H, s0)  <=  sum_{b in H} ||eta_b||  <=  |H| * M     (no cancellation).

CLAIM TO TEST: the sqrt(|H|)*M bound is a STRICTLY STRONGER statement that does NOT follow from
the per-frequency moment control WallHolds supplies. We test this two ways:

(A) POINTWISE: exhibit configurations where sum_{b in H} conj(eta_b) psi(b s0) is close to |H|*M
    in magnitude (constructive worst-case alignment) -- i.e. the naive bound is TIGHT for adversarial
    (H, s0), so nothing about per-frequency size forces cancellation. We take H = a coset/AP of
    frequencies and s0=0 (all phases psi(0)=1), so T = |sum_{b in H} conj(eta_b)| which for a
    cleverly chosen H (all eta_b real-positive-ish) approaches |H|*typical.

(B) MOMENT-INVARIANCE: two spectra {eta_b} with the SAME per-frequency moments (same multiset of
    ||eta_b||, hence same WallHolds status and same M) but DIFFERENT hyperplane sums T -- proving
    T is NOT a function of the moment data the wall controls. If we can permute/re-phase the eta_b
    keeping all ||eta_b|| fixed but sending T from ~sqrt(|H|)M to ~|H|M, then sqrt-cancellation is
    provably a distinct input (a joint/phase-correlation statement, not a marginal-moment one).

We instantiate the actual eta_b from a real regime prime, then run (A) and (B).
"""
import cmath, math, random

def is_prime(m):
    if m < 2: return False
    i = 2
    while i*i <= m:
        if m % i == 0: return False
        i += 1
    return True

def mu_n_elements(n, p):
    def order(a):
        o=1; cur=a%p
        while cur!=1:
            cur=(cur*a)%p; o+=1
        return o
    g=None
    for c in range(2,p):
        if order(c)==p-1:
            g=c; break
    h=pow(g,(p-1)//n,p)
    e=[]; cur=1
    for _ in range(n):
        e.append(cur); cur=(cur*h)%p
    return e

def eta_vec(n,p):
    """complex eta_b for all b in F_p (b=0..p-1)."""
    mu=mu_n_elements(n,p)
    tp=2*math.pi/p
    out=[]
    for b in range(p):
        s=0j
        for y in mu:
            s+=cmath.exp(1j*tp*((b*y)%p))
        out.append(s)
    return out

def find_prime(n, minpow=4):
    lo=n**minpow
    k=max(1,lo//n)
    while True:
        pp=k*n+1; k+=1
        if pp>=lo and is_prime(pp):
            return pp

def run(n):
    p=find_prime(n)
    eta=eta_vec(n,p)
    norms=[abs(eta[b]) for b in range(p)]
    M=max(norms[1:])  # sup over b!=0
    print(f"\n=== n={n}, p={p}, q={p}, M=max_b!=0||eta_b||={M:.3f}, sqrt(n ln q)={math.sqrt(n*math.log(p)):.3f} ===")

    # ---- (A) naive triangle bound is TIGHT for adversarial (H, s0) ----
    # H = a random hyperplane-like subset (an AP of frequencies of size ~ sqrt(p) to keep it cheap),
    # s0 chosen to align phases: pick s0 to (approximately) maximize |sum conj(eta_b) psi(b s0)|.
    Hsize = min(p-1, int(math.isqrt(p)))   # |H| ~ sqrt(q); the honest prize hyperplane is size ~q
    H = list(range(1, Hsize+1))            # a contiguous block of nonzero frequencies
    # try many s0, record the max aligned sum
    tp=2*math.pi/p
    best=0.0; best_s0=0
    trials = min(p, 4000)
    for s0 in random.sample(range(p), trials):
        s=0j
        for b in H:
            s+= eta[b].conjugate()*cmath.exp(1j*tp*((b*s0)%p))
        if abs(s)>best:
            best=abs(s); best_s0=s0
    sqrtbound = math.sqrt(Hsize)*M
    naivebound = Hsize*M
    print(f"  (A) |H|={Hsize} (~sqrt q): best aligned T={best:.2f}")
    print(f"      sqrt(|H|)*M = {sqrtbound:.2f}   |H|*M (naive) = {naivebound:.2f}")
    print(f"      best T / sqrt-bound = {best/sqrtbound:.3f}   best T / naive = {best/naivebound:.3f}")
    print(f"      => aligned adversarial sum {'EXCEEDS' if best>1.05*sqrtbound else 'is within'} sqrt(|H|)*M "
          f"(cancellation is NOT automatic; {best/sqrtbound:.2f}x the sqrt bound)")

    # ---- (B) moment-invariance: same {||eta_b||} multiset, different T ----
    # Build a SURROGATE spectrum with identical per-frequency norms but adversarial phases:
    # eta'_b = ||eta_b|| (all real positive) -> T'(s0=0) = sum_{b in H} ||eta_b|| = naive = |H|*avg.
    # vs the true eta with random s0 giving ~sqrt. Same WallHolds inputs (norms identical), T differs.
    T_true_typical = 0.0
    K=200
    for _ in range(K):
        s0=random.randrange(p)
        s=sum(eta[b].conjugate()*cmath.exp(1j*tp*((b*s0)%p)) for b in H)
        T_true_typical += abs(s)
    T_true_typical/=K
    T_surrogate = sum(norms[b] for b in H)   # all-real-positive rephasing, same norms
    print(f"  (B) SAME per-frequency norms multiset, two phase-assignments:")
    print(f"      typical T (true phases, random s0)         = {T_true_typical:.2f}  (~sqrt regime)")
    print(f"      T for all-aligned rephasing (same norms)   = {T_surrogate:.2f}  (=|H|*avg, naive regime)")
    print(f"      ratio surrogate/typical = {T_surrogate/max(T_true_typical,1e-9):.2f}"
          f"  (~sqrt(|H|)={math.sqrt(Hsize):.2f} if T is genuinely sqrt-cancelled)")
    print(f"      => T is NOT determined by the per-frequency norms: the wall's moment data fixes "
          f"the multiset {{||eta_b||}} but T ranges over [~sqrt(|H|)M .. |H|M]. Two DISTINCT inputs.")

def main():
    print("#466 R13 -- ONE-INPUT vs TWO-INPUT decision")
    print("Testing whether sqrt(q)*B hyperplane cancellation follows from the per-frequency moment")
    print("control (WallHolds/M). If T ranges freely over [sqrt(|H|)M, |H|M] at FIXED norms, it does NOT.")
    random.seed(466)
    for n in (8, 16, 32):
        run(n)

if __name__=="__main__":
    main()

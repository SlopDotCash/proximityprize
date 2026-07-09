#!/usr/bin/env python3
"""
C100 attack: "Bessel I0 tail gives a sub-exponential MGF -- a Bennett/Freedman bound the
Azuma route could not reach (it used only L^inf increments)."

The claim: the proven Bessel even-moment law E_r=(2r)![x^r]I0(2sqrt x)^{n/2} + the in-tree
I0(2x)<=e^{x^2} bound give the EXACT conditional MGF of a per-level increment Delta_k in the
dyadic tower eta^{(2^a)}_b = sum_k Delta_k(b). Feeding this CONDITIONAL MGF (the bulk/L^2
distribution) -- rather than the crude L^inf bound B_{k-1} that Azuma is forced to use --
into a Bennett/Freedman martingale tail should beat the Azuma sqrt(2 ln m) inflation, since
the predictable variance <S> ~ n (Parseval) and the MGF is the missing conditional input.

DECISIVE TESTS at PROPER dyadic subgroups, large prime, beta ~ 4-5 (prize regime):
 (T1) Is the tower (S_k = eta^{(2^k)}_b) a MEAN-ZERO MARTINGALE in b? A Bennett/Freedman
      bound REQUIRES E[Delta_k | F_{k-1}] = 0 (conditional mean zero). Measure the conditional
      mean of the increment given the coarse coset. If it is NOT ~0, NO martingale bound of
      ANY kind (Azuma, Bennett, Freedman, Bernstein) applies -- the whole premise is void.
 (T2) For the WORST-CASE coset b (the one achieving the house B_a = max), do the increments
      add coherently (all same sign, |S_a| = sum|Delta_k|) or as a cancelling walk? Coherent
      addition => the conditional MGF / variance is IRRELEVANT (no cancellation to exploit);
      the worst coset is exactly where Bennett/Freedman give NOTHING beyond the triangle
      inequality sum B_{k-1}.
 (T3) Quantify: triangle-inequality bound sum_{k} B_{k-1} for the worst b -- does it equal
      B_a (coherent) ? And is the Bennett "variance term" sqrt(2 <S> ln m) with <S>~n vs the
      "range term" (1/3) b_max ln m -- which dominates at prize scale? The KB claims the range
      term b_max*ln m ~ n ln m DOMINATES <S> ~ n once ln m > 1. Verify with the ACTUAL Bessel
      MGF conditional variance, not the crude L^inf.
"""
import cmath, math
import numpy as np

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(r-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def factorize(m):
    s = set(); d = 2
    while d*d <= m:
        while m % d == 0: s.add(d); m //= d
        d += 1
    if m > 1: s.add(m)
    return s

def gen_Fp_star(p):
    F = factorize(p-1)
    for h in range(2, p):
        if all(pow(h, (p-1)//q, p) != 1 for q in F): return h
    return None

def find_prime_tower(a, beta):
    """prime p with 2^a | p-1 and p ~ n^beta, n=2^a (proper subgroup, big prime, beta~4-5)."""
    n = 2**a
    lo = int(n**beta)
    step = 2**a
    p = lo - (lo % step) + 1
    if p <= lo: p += step
    hi = int(n**(beta+1.0))
    while p < hi:
        if is_prime(p): return p
        p += step
    return None

def eta_of(p, b, mu_list):
    s = 0j
    for x in mu_list:
        s += cmath.exp(2j*cmath.pi*((b*x) % p)/p)
    return s.real

print("="*100)
print("C100  BESSEL-MGF BENNETT/FREEDMAN vs AZUMA -- decisive tests at PROPER subgroups")
print("="*100)

for a in (4, 5, 6):
    n = 2**a
    p = find_prime_tower(a, 4.0)
    if p is None:
        print(f"\nn={n}: no full-tower prime"); continue
    g0 = gen_Fp_star(p)
    m = (p-1)//n
    beta = math.log(p)/math.log(n)
    L = math.log(m)
    print(f"\n--- n={n}=2^{a}  p={p}  m=(p-1)/n={m}  beta=log_n(p)={beta:.2f}  L=ln m={L:.2f} ---")
    def mu(k):
        gen = pow(g0, (p-1)//(2**k), p)
        return [pow(gen, i, p) for i in range(2**k)]
    mun = mu(a)

    # ---- find worst-case coset b (the house achiever) over a transversal of F_p*/mu_n ----
    seen = set(); reps = []; b = 1
    cap = min(m, 6000)
    while len(reps) < cap and b < p:
        if b not in seen:
            reps.append(b)
            for x in mun: seen.add((b*x) % p)
        b += 1
    eat = [(eta_of(p, bb, mun), bb) for bb in reps]
    B_a = max(abs(t[0]) for t in eat)
    Mval, bworst = max(eat, key=lambda t: abs(t[0]))
    print(f"  house B_a = max|eta| = {B_a:.3f}   target sqrt(2 n L)={math.sqrt(2*n*L):.3f}   B_a/target={B_a/math.sqrt(2*n*L):.3f}")

    # B_j = level-j house (max over a transversal of F_p*/mu_{2^j}); needed for triangle/Azuma terms
    def house_level(j):
        muj = mu(j); seen2 = set(); best = 0.0; bb = 1; cnt = 0
        capj = min((p-1)//(2**j), 4000)
        while cnt < capj and bb < p:
            if bb not in seen2:
                v = abs(eta_of(p, bb, muj)); best = max(best, v); cnt += 1
                for x in muj: seen2.add((bb*x) % p)
            bb += 1
        return best
    Bj = [house_level(j) for j in range(1, a+1)]  # Bj[k]=B_{k+1}

    # ---- (T1) CONDITIONAL MEAN of increment: is the tower a mean-zero martingale? ----
    # Coarse coset at level k-1 is fixed; the two children at level k are b and b*w_{k-1}.
    # Increment Delta_k(b) = eta^{(2^k)}_b - eta^{(2^{k-1})}_b = eta^{(2^{k-1})}_{b w_{k-1}}.
    # Conditional mean given F_{k-1} (= given eta^{(2^{k-1})}_b): average of Delta over the
    # refinement. We test the GLOBAL martingale property: E_b[Delta_k] over all cosets, and the
    # CONDITIONAL E[Delta_k | sign/bin of S_{k-1}] -- a real martingale needs cond-mean 0.
    print("  (T1) martingale check  level k:  E[Delta_k]   E[Delta_k | S_{k-1}>0]   corr(Delta_k, S_{k-1})")
    # build per-coset telescopes over the transversal
    Ss = {kk: [] for kk in range(1, a+1)}
    Deltas = {kk: [] for kk in range(1, a+1)}
    Sprev = []
    bs = reps[:min(len(reps), 4000)]
    tele = []
    for bb in bs:
        s_levels = [eta_of(p, bb, mu(kk)) for kk in range(1, a+1)]
        tele.append(s_levels)
    tele = np.array(tele)  # rows = cosets, cols = levels 1..a
    for kk in range(1, a+1):
        S_k = tele[:, kk-1]
        if kk == 1:
            Delta = S_k.copy()
            S_prev = np.zeros_like(S_k)
        else:
            S_prev = tele[:, kk-2]
            Delta = S_k - S_prev
        condpos = Delta[S_prev > 0]
        cm_pos = condpos.mean() if len(condpos) else float('nan')
        cc = np.corrcoef(Delta, S_prev)[0,1] if kk > 1 and np.std(S_prev) > 0 else 0.0
        print(f"        k={kk:2d}    E[D]={Delta.mean():+8.4f}   E[D|S>0]={cm_pos:+8.4f}   corr={cc:+.4f}")

    # ---- (T2) worst-coset coherence: triangle vs actual ----
    Sw = [eta_of(p, bworst, mu(kk)) for kk in range(1, a+1)]
    incs = [Sw[0]] + [Sw[kk]-Sw[kk-1] for kk in range(1, len(Sw))]
    signs = [1 if x > 0 else -1 for x in incs]
    sum_abs = sum(abs(x) for x in incs)
    coherence = abs(Sw[-1])/sum_abs if sum_abs > 0 else 0.0
    print(f"  (T2) worst b={bworst}: increment signs {signs}")
    print(f"       |S_a|={abs(Sw[-1]):.3f}  sum|Delta_k|={sum_abs:.3f}  coherence |S_a|/sum|D|={coherence:.3f}  (1.0 => fully coherent, NO cancellation)")

    # ---- (T3) Bennett/Freedman terms with the BESSEL conditional variance vs Azuma L^inf ----
    # Bessel conditional variance of Delta_k = eta^{(2^{k-1})}_{.}: Var = E[Delta_k^2] over cosets
    # ~ 2^{k-1} (Parseval, the L^2 scale).  Predictable variation <S> = sum Var(Delta_k) ~ n.
    Var = []
    for kk in range(1, a+1):
        S_k = tele[:, kk-1]
        Delta = S_k if kk == 1 else (S_k - tele[:, kk-2])
        Var.append(Delta.var())
    S_pred = sum(Var)  # <S>
    b_max = max(Bj)    # range = max L^inf increment bound
    # Freedman/Bennett: P(S_a >= t) <= exp(-t^2/(2(<S> + b_max t/3))); invert at union over m:
    # set rhs = 1/m => t solves t^2 = 2 ln m (<S> + b_max t/3). Quadratic in t.
    A = 1.0; Bq = -(2*L*b_max/3.0); Cq = -2*L*S_pred
    t_freedman = (-Bq + math.sqrt(Bq*Bq - 4*A*Cq))/(2*A)
    t_bennett_varonly = math.sqrt(2*L*S_pred)          # the variance term alone (the HOPE)
    t_range = (2.0/3.0)*b_max*L                          # the range/L^inf correction term scale
    t_azuma = math.sqrt(2*L*sum(bb*bb for bb in Bj))    # the Azuma bound (uses L^inf B_k^2)
    print(f"  (T3) predictable var <S>=sum Var(Delta_k)={S_pred:.2f}  (~n={n}? ratio {S_pred/n:.2f})   b_max(L^inf increment)={b_max:.2f}")
    print(f"       Bennett variance-term sqrt(2 L <S>) = {t_bennett_varonly:.2f}   (the HOPE: ~ sqrt(2 n L)={math.sqrt(2*n*L):.2f})")
    print(f"       Freedman full bound t* (var+range)   = {t_freedman:.2f}")
    print(f"       range term (2/3) b_max L            = {t_range:.2f}   <S>={S_pred:.2f}  range/<S>={t_range/S_pred:.2f}  (>1 => range DOMINATES)")
    print(f"       Azuma bound sqrt(2 L sum B_k^2)      = {t_azuma:.2f}   actual house B_a={B_a:.2f}")
    print(f"       Freedman/target ratio = {t_freedman/math.sqrt(2*n*L):.3f}   Azuma/target = {t_azuma/math.sqrt(2*n*L):.3f}")

print("\n" + "="*100)
print("VERDICT LOGIC:")
print(" * If (T1) conditional means are NOT ~0  => no martingale of any kind (Bennett incl.) applies.")
print(" * If (T2) coherence ~1.0 at worst coset => Bennett/Freedman give nothing past triangle ineq.")
print(" * If (T3) range term (2/3)b_max L >> <S>=n => Freedman range correction dominates, no gain over Azuma.")
print("="*100)

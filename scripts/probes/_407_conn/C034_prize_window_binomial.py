#!/usr/bin/env python3
"""
C034 follow-up: does the resonance binomial C(n/2^L, a/2^L) actually stay <= C*n
in the PRIZE WINDOW, and is the floor really "automatic for structural reasons"?

Two things:
  (1) n=32 robustness spot-check of claims A & B (subset of (a,t) only, to stay fast).
  (2) Prize-window numeric: for prize rates rho in {1/2,1/4,1/8,1/16}, n=2^mu (mu up to 40),
      q ~ n*2^128, eps* = 2^-128 so q*eps* ~ n.
      Window-edge gap t0 = ceil(H(rho)*n / log2(q*eps*)) ~ H(rho)*n/log2(n).
      At/near the window edge with a=k+t:
        - is t even close to a power of 2 (resonance)?
        - WORST CASE over ALL window-interior t (t>=t0): max over resonant t of
          C(n/2^L, (k+t)/2^L). Does it ever EXCEED C*n? If yes -> floor risk; if no -> floor holds.

The C034 claim is that worst-case binomial stays poly/<=C*n. We test that claim's TEETH:
the binomial C(n/2^L, a/2^L) can be LARGE when 2^L is small (L small) but a is divisible by it.
The dangerous regime is SMALL t (L small) with a=k+t large but divisible by 2^L. We sweep all t.
"""

import itertools, math
from math import comb, gcd, log2

# ---------- part 1: n=32 robustness ----------
def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def first_prime(n, beta=4):
    lo = int(n**beta)
    q = lo + (n - lo % n) % n + 1
    while not (q % n == 1 and is_prime(q)):
        q += n
    return q

def mu_n_elements(q, n):
    def order(a, q):
        o = 1; x = a % q
        while x != 1:
            x = (x*a) % q; o += 1
        return o
    g = None
    for cand in range(2, q):
        if order(cand, q) == q-1:
            g = cand; break
    e = (q-1)//n
    base = pow(g, e, q)
    elts = []; x = 1
    for _ in range(n):
        elts.append(x); x = (x*base) % q
    return elts

def esymm_mod(subset, t, q):
    if t == 0: return 1 % q
    if t > len(subset): return 0
    s = 0
    for combo in itertools.combinations(subset, t):
        p = 1
        for x in combo: p = (p*x) % q
        s = (s + p) % q
    return s

def count_vv(mu, a, t, q):
    cnt = 0
    for S in itertools.combinations(mu, a):
        ok = True
        for j in range(1, t):
            if esymm_mod(S, j, q) != 0:
                ok = False; break
        if ok: cnt += 1
    return cnt

def L_of(t):
    return 0 if t <= 1 else math.ceil(math.log2(t))

def predict(n, a, t):
    L = L_of(t); twoL = 2**L
    if a % twoL != 0 or n % twoL != 0:
        return 0, L, twoL
    return comb(n // twoL, a // twoL), L, twoL

def part1_n32():
    print("="*90)
    print("PART 1: n=32 robustness (small a only, to keep enumeration tractable)")
    print("="*90)
    n = 32
    q = first_prime(n, 4)
    print(f"n={n}, q={q} (q=1 mod {n}: {q%n==1}, prime: {is_prime(q)})")
    mu = mu_n_elements(q, n)
    mm = 0; cases = 0
    # a up to 8 keeps C(32,8)=10518300 ... too big. Limit a<=6 (C(32,6)=906192 ok-ish)
    for a in range(2, 7):
        for t in range(2, a+1):
            cnt = count_vv(mu, a, t, q)
            pred, L, twoL = predict(n, a, t)
            cases += 1
            statusA = (cnt>0) == (pred>0)
            statusB = (not (cnt>0 and pred>0)) or (cnt==pred)
            if not statusA or not statusB:
                mm += 1
            if cnt>0 or pred>0:
                print(f"  a={a} t={t} L={L} 2^L={twoL} | actual={cnt} pred={pred} "
                      f"{'OK' if statusA and statusB else 'MISMATCH'}")
    print(f"  n=32 cases checked: {cases}, mismatches: {mm}")

# ---------- part 2: prize window worst-case binomial ----------
def H(rho):
    # binary entropy in bits
    if rho <= 0 or rho >= 1: return 0.0
    return -rho*log2(rho) - (1-rho)*log2(1-rho)

def part2_prize():
    print("\n"+"="*90)
    print("PART 2: prize-window worst-case resonance binomial vs C*n")
    print("="*90)
    print("q*eps* ~ n (q~n*2^128, eps*=2^-128). Window-interior: t >= t0=ceil(H(rho)n/log2(q*eps*)).")
    print("log2(q*eps*) ~ log2(n). For each resonant t (2^L|(k+t)), binomial = C(n/2^L,(k+t)/2^L).")
    print("Floor at risk if max over window-interior resonant t exceeds C*n for moderate C.\n")
    rho_list = [("1/2",0.5),("1/4",0.25),("1/8",0.125),("1/16",0.0625)]
    for mu in [16, 24, 32, 40]:
        n = 2**mu
        log2_qeps = log2(n)  # q*eps* ~ n
        print(f"--- n=2^{mu}={n}, log2(q*eps*)~{log2_qeps:.1f} ---")
        for rname, rho in rho_list:
            k = round(rho*n)
            t0 = math.ceil(H(rho)*n / log2_qeps)
            # sweep all window-interior gaps t in [t0, n-k]; find resonant ones; max binomial
            best = 0; best_t = None
            # too many t to sweep one by one at n=2^40; but binomial only depends on L and a=k+t.
            # For each L from L(t0) up to mu, the resonant t have 2^L | (k+t).
            # We want max over t in [t0, n-k] with 2^L|(k+t) of C(n/2^L, (k+t)/2^L), L=ceil(log2 t).
            # Note L is tied to t: t in [2^{L-1}+1, 2^L]. So for each L, t ranges over that dyadic block
            # intersect [t0, n-k]. Within that block a=k+t ranges; resonance needs 2^L|(k+t).
            for Lc in range(max(1,L_of(t0)), mu+1):
                t_lo = max(t0, 2**(Lc-1)+1)
                t_hi = min(n-k, 2**Lc)
                if t_lo > t_hi: continue
                twoL = 2**Lc
                # a=k+t resonant: a multiple of twoL, a in [k+t_lo, k+t_hi]
                a_lo = k + t_lo; a_hi = k + t_hi
                # smallest multiple of twoL >= a_lo
                first_a = ((a_lo + twoL - 1)//twoL)*twoL
                a = first_a
                while a <= a_hi:
                    if a <= n and a % twoL == 0:
                        val = comb(n//twoL, a//twoL)
                        if val > best:
                            best = val; best_t = (a-k, Lc, twoL, a)
                    a += twoL
            ratio = best / n if best>0 else 0
            note = ""
            if best > n:
                note = f"  *** binomial > n (ratio {ratio:.3g}) ***"
            print(f"  rho={rname:4} k={k:>12} t0={t0:>12} | max window-interior resonance binomial="
                  f"{best:.6g}  (=> ratio binom/n={ratio:.4g}){note}")
            if best_t:
                t,Lc,twoL,a = best_t
                print(f"        achieved at t={t} (L={Lc}, 2^L={twoL}, a={a}, n/2^L={n//twoL}, a/2^L={a//twoL})")

if __name__ == "__main__":
    part1_n32()
    part2_prize()

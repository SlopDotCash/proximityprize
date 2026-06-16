#!/usr/bin/env python3
"""
C030 attack, part 2: does the EntropyGateDeltaStar gate (the attack_plan's promised
Lean advance) actually FIRE in the PRIZE regime, and does it beat Johnson?

mcaDeltaStar_le_of_entropy_gate hypotheses (EntropyGateDeltaStar.lean), with a=k+m+1:
  (lower wall)  a! * (2 * q^m)        <= (n+1-a)^a
  (upper wall)  n^a                   <  a! * q^{m+1}
  (hhi)         (1-delta)*n           <= a   (so delta >= 1 - a/n)
The conclusion: mcaDeltaStar(rsCode dom k) eps* <= delta, with the band radius a=k+m+1.

PRIZE regime: q ~ n^beta, beta in [4,5], thin dyadic subgroup. We sweep n,k,m,q and
check (i) both walls satisfiable, (ii) the resulting delta vs the Johnson radius
1-sqrt(rho) and the capacity 1-rho, where rho=(k+1)/n. The prize window is the OPEN
interior (1-sqrt(rho), 1-rho-Theta(1/log n)). A 'real advance' must put delta INSIDE
that window (strictly below 1-sqrt(rho)) for a thin-subgroup / large-prime q.
"""
from math import isqrt, log2

def factorial(x):
    r=1
    for i in range(2,x+1): r*=i
    return r

def walls_hold(n,k,m,q):
    a=k+m+1
    if a>n+1: return None
    fa=factorial(a)
    lower = fa*(2*(q**m)) <= (n+1-a)**a
    upper = (n**a) < fa*(q**(m+1))
    return lower, upper, a

print("="*108)
print("C030 part 2: does the entropy gate FIRE in the prize regime, and where is delta vs Johnson?")
print("="*108)
print(f"{'n':>5}{'k':>4}{'m':>4}{'q~n^b':>10}{'beta':>6}{'a':>4}{'low':>5}{'up':>5}"
      f"{'delta=1-a/n':>12}{'1-rho':>8}{'1-sqrtrho':>11}{'inWindow?':>11}")

def report(n,k,m,beta):
    q=int(round(n**beta))
    # make q a bit above n^beta and "prime-ish" size; exact primality irrelevant to the walls
    res=walls_hold(n,k,m,q)
    if res is None:
        return
    low,up,a=res
    rho=(k+1)/n
    delta=1-a/n
    cap=1-rho
    john=1-rho**0.5
    inwin = (low and up and delta<john and delta<cap and delta>0)
    print(f"{n:>5}{k:>4}{m:>4}{q:>10}{beta:>6.1f}{a:>4}{str(low):>5}{str(up):>5}"
          f"{delta:>12.4f}{cap:>8.4f}{john:>11.4f}{str(inwin):>11}")

# toy proper-subgroup-shaped sweep (n = subgroup-ish; rho in prize set 1/2..1/16)
for n in [16,32,64]:
    for rho_target in [0.5,0.25,0.125,0.0625]:
        k=max(1,int(round(rho_target*n))-1)
        for m in [1,2,3]:
            for beta in [4.0,5.0]:
                report(n,k,m,beta)
    print("-"*108)

print()
print("="*108)
print("DIAGNOSTIC: simultaneous wall satisfiability at q~n^beta (beta>=4).")
print("="*108)
# Lower wall needs a! * 2 q^m <= (n+1-a)^a. With q~n^beta and a=k+m+1:
#   LHS ~ a! * 2 * n^{beta*m},  RHS ~ (n)^a = n^{k+m+1}.
#   So lower wall ~ requires  beta*m <= k+m+1, i.e.  k+1 >= (beta-1)*m.
# Upper wall needs n^a < a! q^{m+1} ~ a! n^{beta(m+1)}:
#   a=k+m+1 < beta(m+1)+log_n(a!), i.e. roughly  k+m+1 < beta(m+1), k < (beta-1)(m+1).
# So BOTH walls: (beta-1)*m <= k+1  AND  k < (beta-1)(m+1).
# i.e.  (beta-1)*m - 1 <= k < (beta-1)*m + (beta-1).  A NARROW k-band of width ~beta-1.
print("Closed-form (q~n^beta): lower wall  <=>  k+1 >= (beta-1)*m   (approx)")
print("                        upper wall  <=>  k   <  (beta-1)*(m+1) (approx)")
print("=> feasible k-band has width ~ (beta-1); CENTERED at k ~ (beta-1)*m.")
print("   So rho = (k+1)/n ~ (beta-1)*m/n.  For this to hit prize rho=1/4 need m ~ n/(4(beta-1)),")
print("   i.e. m = Theta(n), hence the SUBGROUP 2^mu = n/m = Theta(1) -- a SMALL subgroup,")
print("   NOT the thin prize subgroup. The gate fires only when 2^mu = O(1) (m ~ n).")
print()
for beta in [4.0,5.0]:
    for m in [1,3,8,32]:
        klo=(beta-1)*m-1; khi=(beta-1)*(m+1)
        print(f"  beta={beta} m={m:>3}: feasible k in [{klo:.1f},{khi:.1f}); "
              f"center rho~(k+1)/n needs n~{((beta-1)*m+1)/0.25:.0f} for rho=1/4 -> "
              f"subgroup 2^mu=n/m~{((beta-1)*m+1)/0.25/m:.1f}")

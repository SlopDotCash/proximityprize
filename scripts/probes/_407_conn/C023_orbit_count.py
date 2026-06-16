#!/usr/bin/env python3
"""
C023 attack -- "Two group-actions quantize the SAME law: dilation <g^t> vs coset mu_n".

The connection's PROVEN backbone (verify numerically):
  (A) FREQUENCY side: eta_b constant on cosets b*mu_n  -> <= (q-1)/n distinct values  [in-tree]
  (B) BAD-SCALAR side: lacBad(mu_n,a,t) closed under gamma -> g^t * gamma,
      a union of cosets of <g^t> = mu_{n/gcd(t,n)}; #lacBad a multiple of n/gcd(t,n).  [in-tree]

The connection's NOVEL, NOT-YET-PROVEN claims (the real targets):
  (C) attack_plan: ORBIT count  orb(t) := #lacBad / (n/gcd(t,n))  is O(1)  EXACTLY when gcd(t,n)=1.
      If true, the floor would reduce to coprime-t directions; t-even handled by mu_{n/2} self-similar
      collapse.
  (D) "predicts the even/odd-t parity split in incidence directly" -- i.e. #lacBad (the incidence,
      = I(delta)) differs systematically by parity of t in the window.

Exact integer arithmetic, proper-subgroup dyadic mu_n, large prime q ~ n^beta, q = 1 mod n.
"""
import itertools, math
from collections import defaultdict

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d = n-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(r-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True

def prime_1_mod_n(n, beta):
    lo = int(n**beta); lo += (1 - lo) % n; p = lo
    while True:
        # require q-1 NOT a pure power of 2 (proper-subgroup + multiple-primes flavour, avoid #400 trap)
        if is_prime(p) and ((p-1) & (p-2)) != 0:
            return p
        p += n

def factorize(m):
    fs = set(); d = 2
    while d*d <= m:
        while m % d == 0: fs.add(d); m //= d
        d += 1
    if m > 1: fs.add(m)
    return fs

def order_n_gen(p, n):
    fac = factorize(p-1)
    for h in range(2, p):
        if all(pow(h, (p-1)//q, p) != 1 for q in fac):
            return pow(h, (p-1)//n, p)

def esym_all(S_vals, tmax, p):
    e = [0]*(tmax+1); e[0] = 1
    for x in S_vals:
        for j in range(min(tmax, len(e)-1), 0, -1):
            e[j] = (e[j] + e[j-1]*x) % p
    return e

def Hb(x):
    if x <= 0 or x >= 1: return 0.0
    return -x*math.log2(x) - (1-x)*math.log2(1-x)

def analyze(n, beta, rho):
    p = prime_1_mod_n(n, beta)
    g = order_n_gen(p, n)
    powg = [pow(g, i, p) for i in range(n)]      # mu_n = {g^0,...,g^{n-1}}
    muset = set(powg)
    k = int(round(rho*n))
    bbeta = math.log(p)/math.log(n)
    print(f"\n=== n={n}  q={p} (beta={bbeta:.2f})  rho={rho} k={k} | "
          f"Johnson 1-sqrt(rho)={1-rho**0.5:.3f}  cap 1-rho={1-rho:.3f} | budget B~n={n}")
    print(f"   {'t':>2} {'a':>3} {'delta':>6} {'gcd':>3} {'unit=n/gcd':>10} "
          f"{'#lacBad':>8} {'orbits':>7} {'mult?':>5} {'parity':>6} {'zone':>9}")
    rows = []
    for t in range(1, n-k+1):
        a = k + t
        if math.comb(n, a) > 3_000_000:
            continue
        gcd = math.gcd(t, n); unit = n // gcd
        img = set()
        for S in itertools.combinations(range(n), a):
            vals = [powg[j] for j in S]
            e = esym_all(vals, t, p)
            if all(e[j] == 0 for j in range(1, t)):
                img.add(e[t])
        nb = len(img)
        orbits = (nb // unit) if (nb and nb % unit == 0) else (nb/unit if nb else 0)
        mult = (nb % unit == 0) if nb > 0 else True
        delta = 1 - a/n
        J = 1 - rho**0.5; cap = 1 - rho
        zone = "<J" if delta < J-1e-9 else ("[J,cap)" if delta < cap-1e-9 else ">=cap")
        # cross-check: is img actually closed under *g^t ?  (verifies in-tree lacBad_smul_closed)
        gt = pow(g, t, p)
        closed = all(((x*gt) % p) in img for x in img)
        par = "even" if t % 2 == 0 else "odd"
        print(f"   {t:>2} {a:>3} {delta:>6.3f} {gcd:>3} {unit:>10} "
              f"{nb:>8} {str(orbits):>7} {str(mult and closed):>5} {par:>6} {zone:>9}")
        rows.append(dict(t=t,a=a,delta=delta,gcd=gcd,unit=unit,nb=nb,orbits=orbits,
                         coprime=(gcd==1),zone=zone,closed=closed,mult=mult))
    return rows

if __name__ == "__main__":
    print("="*102)
    print("C023: orbit count #lacBad/(n/gcd(t,n)) vs gcd(t,n) -- is it O(1) IFF gcd(t,n)=1?  + parity split")
    print("="*102)
    ALL = []
    for (n, beta, rho) in ((16,4.0,0.25),(16,4.0,0.5),(24,3.0,0.25),(32,4.0,0.25)):
        ALL.extend([(n,rho,r) for r in analyze(n, beta, rho)])

    # ---- TEST (C): orbit count O(1) IFF gcd=1 ----
    print("\n" + "="*102)
    print("TEST (C): orbit count classification (window-interior rows, delta in [J,cap) or >=cap)")
    print("="*102)
    cop_orb = [r for (n,rho,r) in ALL if r['coprime'] and r['nb']>0]
    non_orb = [r for (n,rho,r) in ALL if not r['coprime'] and r['nb']>0]
    def osumm(rs, lab):
        if not rs:
            print(f"  {lab}: (no nonempty rows)"); return
        vals = [r['orbits'] for r in rs]
        print(f"  {lab}: n_rows={len(rs)}  orbits min={min(vals)} max={max(vals)} "
              f"set={sorted(set(round(v,3) for v in vals))}")
    osumm(cop_orb, "gcd(t,n)=1 (coprime t)")
    osumm(non_orb, "gcd(t,n)>1 (non-coprime t)")
    # Does coprime <=> few orbits hold?  Check max orbit among coprime vs among non-coprime
    if cop_orb and non_orb:
        print(f"\n  CLAIM C predicts: coprime-t orbit count O(1) AND smaller than non-coprime.")
        print(f"    max coprime orbits   = {max(r['orbits'] for r in cop_orb)}")
        print(f"    max noncoprime orbits= {max(r['orbits'] for r in non_orb)}")

    # ---- TEST (D): parity split in incidence #lacBad ----
    print("\n" + "="*102)
    print("TEST (D): even/odd-t parity split in incidence #lacBad (same n,rho, compare consecutive t)")
    print("="*102)
    # group by (n,rho) and show #lacBad sequence with parity
    from collections import OrderedDict
    grp = OrderedDict()
    for (n,rho,r) in ALL:
        grp.setdefault((n,rho), []).append(r)
    for (n,rho), rs in grp.items():
        seq = [(r['t'], r['nb'], r['t']%2) for r in rs if r['nb']>0]
        print(f"  n={n} rho={rho}: (t,#lacBad,par)= {seq}")

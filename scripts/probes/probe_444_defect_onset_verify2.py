#!/usr/bin/env python3
"""
probe_444_defect_onset_verify2.py  (#444 Verify-2)

DECISIVE numerical test of the eta-crit synthesis: search for the FIRST (n, p, c) where a
NON-COSET defect appears.

DEFECT (exact, matching Sweep_A10 / Sweep_A40 / the even-odd descent):
  a size-s subset T of mu_n whose first c elementary-symmetric functions e_1..e_c vanish mod p,
  and which is NOT a binomial coset (root-set of X^{n/4}-const, i.e. not a single mu_{n/c'} coset).

We treat c as an INDEPENDENT knob (NOT pinned to n/8) so we can probe the wall regime (small c,
high ceiling p<=s^{n/(2c)}) vs the clean regime (large c, low ceiling).

The synthesis predicts:
  - defects appear for SMALL c (wall),
  - and whenever a defect appears it OBEYS the norm ceiling p <= s^{n/(2c)}  (the Action-Orbit bound).
"""
import itertools, sys
from sympy import isprime, primitive_root
from math import comb

def find_window_prime(n, beta=4.0, idx_min=2):
    target=int(n**beta); base=target-(target%n)+1; p=base
    while True:
        if p>n and isprime(p) and (p-1)%n==0 and (p-1)//n>=idx_min: return p
        p+=n

def subgroup(n,p):
    g=primitive_root(p); zeta=pow(g,(p-1)//n,p)
    e,x=[],1
    for _ in range(n): e.append(x); x=(x*zeta)%p
    return e

def elem_sym(roots,p,upto):
    e=[1]+[0]*upto
    for r in roots:
        for i in range(min(len(e)-1,upto),0,-1): e[i]=(e[i]+e[i-1]*r)%p
    return e[1:upto+1]

def coset_rootsets(elts, n, p, divs):
    """All exact mu_d cosets in mu_n for each divisor d: subsets {x: x^(n/d)=c}.
       Returns a set of frozensets covering ALL 'binomial-coset' subsets of every size n/d."""
    cos=set()
    for d in divs:
        e=n//d  # exponent; subset = root-set of X^e = c, size = e... wait
    return cos

def is_binomial_coset(T, elts, n, p):
    """A subset T is a binomial coset iff it is exactly {x in mu_n : x^|T| = c} for some constant c,
       i.e. T = a fixed coset of the order-|T| subgroup mu_{|T|} <= mu_n (requires |T| | n).
       Equivalently x^|T| is constant over T AND |T| = #{x: x^|T|=that const}."""
    s=len(T)
    if n % s != 0: return False
    vals=set(pow(x,s,p) for x in T)
    if len(vals)!=1: return False
    c=vals.pop()
    full=[x for x in elts if pow(x,s,p)==c]
    return len(full)==s and set(full)==set(T)

def search_defects_enum(n, p, s, c, max_report=3):
    """Full enumeration over size-s subsets (use only when comb(n,s) is small).
       Returns list of defect witnesses (non-coset T with e_1..e_c=0)."""
    elts=subgroup(n,p)
    defects=[]; total=0
    for T in itertools.combinations(elts, s):
        es=elem_sym(T,p,c)
        if all(e==0 for e in es):
            total+=1
            if not is_binomial_coset(T, elts, n, p):
                defects.append(T)
                if len(defects)>=max_report: break
    return total, defects

def ceiling(s, n, c):
    return s**(n/(2*c)) if c>0 else float('inf')

if __name__=="__main__":
    print("### VERIFY-2: DEFECT ONSET, c as independent knob ###", flush=True)
    print("### A defect = non-coset size-s T with e_1..e_c = 0 mod p. Ceiling: p <= s^(n/(2c)). ###\n", flush=True)
    # n=16: sweep s and c, full enumeration (comb(16,s) manageable up to s=8)
    for n in [16, 24, 32]:
        p = find_window_prime(n, 4.0)
        print(f"--- n={n}  p={p}  (p~n^4) ---", flush=True)
        # sweep agreement size s and condition count c (c<=s-1)
        for s in range(3, min(n//2, 9)+1):
            if comb(n, s) > 3_000_000:
                continue
            for c in range(2, s):   # c>=2 (c=1: e_1=0 trivial direction)
                tot, defs = search_defects_enum(n, p, s, c, max_report=1)
                ceil = ceiling(s, n, c)
                obeys = (p <= ceil)
                tag = ""
                if defs:
                    tag = f"  <== DEFECT  ceiling p<=s^(n/2c)={ceil:.4g}  p<=ceil? {obeys}"
                if defs or (tot>0 and c<=3):
                    print(f"   s={s} c={c}: lacunary_total={tot:5d}  defects={len(defs)}{tag}", flush=True)
        print(flush=True)

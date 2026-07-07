#!/usr/bin/env python3
"""
probe_cr_deep_charzero.py  (issue #444, [cr-monotonicity-deep], EVERY-ANGLE wall-side)

QUESTION: is c_r <= 1 a Lam-Leung COROLLARY in char 0 for ALL r (deep, r up to ~12)?
If so, the prize = c_r <= 1 in char-p = the spur bound = same wall, BUT the char-0 all-r
fact is a real partial.

SETUP (exact, char-0, n=2^mu).  a_r = E_r^{char0}/Wick_r, Wick_r=(2r-1)!!*n^r.  The
orchestrator recursion is  a_{r+1} = (a_r + 2r*c_r)/(1+2r), i.e.
   c_r = ((1+2r)*a_{r+1} - a_r)/(2r).
By Lam-Leung the Wick bound a_r <= 1 holds for ALL r (char-0).  We test:

  (T1) Does a_r <= 1 hold for all measured r (Wick / Lam-Leung)?  [known: yes]
  (T2) Does c_r <= 1 hold DEEP (r up to 12)?  Is it MONOTONE DECREASING in r at fixed n?
  (T3) STRUCTURAL: c_r <= 1  <=>  a_{r+1} <= (a_r + 2r)/(1+2r).  Since a_r<=1, the RHS
       >= (a_r + 2r*a_r)/(1+2r) is NOT automatic; but a_{r+1}<=1<=(a_r+2r)/(1+2r) when
       a_r ... let's check: (a_r+2r)/(1+2r) >= 1  <=>  a_r+2r >= 1+2r  <=>  a_r>=1.  So
       (a_r+2r)/(1+2r) >= 1 ONLY when a_r>=1, i.e. a_r=1 (r=1).  For r>=2, a_r<1 so the
       Wick bound a_{r+1}<=1 ALONE does NOT give c_r<=1; c_r<=1 is STRICTLY STRONGER than
       a_{r+1}<=1 once a_r<1.  This is the crux: is c_r<=1 a genuinely DEEPER fact?
       => measure the GAP  (a_r+2r)/(1+2r) - a_{r+1}  (>=0 iff c_r<=1).

  (T4) The cross-step c_r in terms of energies directly:
       a_{r+1}(1+2r) = a_r + 2r c_r
       => 2r c_r = (1+2r) a_{r+1} - a_r
       => c_r = [(1+2r) E_{r+1}/Wick_{r+1} - E_r/Wick_r]/(2r).
       Wick_{r+1}=(2r+1)!!n^{r+1}=(2r+1)Wick_r*n.  So
         (1+2r)E_{r+1}/Wick_{r+1} = E_{r+1}/(Wick_r*n).
         c_r = [E_{r+1}/(n) - E_r]/(2r Wick_r) = (E_{r+1} - n E_r)/(2r n Wick_r).
       So  c_r <= 1  <=>  E_{r+1} - n E_r <= 2r n Wick_r = 2r n (2r-1)!! n^r = 2r (2r-1)!! n^{r+1}
                    <=>  E_{r+1} <= n E_r + 2r(2r-1)!! n^{r+1} = n E_r + (2r+1)!! n^{r+1} - (2r-1)!! n^{r+1}
       Hmm: 2r(2r-1)!! = (2r+1)!! - (2r-1)!!.  So
         c_r<=1 <=> E_{r+1} <= n E_r + [(2r+1)!! - (2r-1)!!] n^{r+1}
                 <=> E_{r+1} - (2r+1)!!n^{r+1} <= n(E_r - (2r-1)!!n^r)
                 <=> Wick-defect_{r+1} <= n * Wick-defect_r    where defect_r := E_r - Wick_r <= 0 (Lam-Leung).
       Since defect_r <= 0, n*defect_r <= 0.  So c_r<=1 <=> (Wick_r - E_r is "growing by at
       least a factor n per step"): Wick_{r+1}-E_{r+1} >= n(Wick_r - E_r).  This is a clean
       structural reformulation -- the SLACK in Lam-Leung must grow super-geometrically (>= xn).
       => measure slack_r := Wick_r - E_r >= 0 and the ratio slack_{r+1}/slack_r vs n.
"""
from fractions import Fraction
from collections import defaultdict

def rep_vectors(n):
    half = n // 2
    reps = []
    for j in range(n):
        v = [0]*half
        if j < half: v[j] = 1
        else:        v[j-half] = -1
        reps.append(tuple(v))
    return reps

def char0_energy_upto(n, R):
    """E_r^char0(mu_n) for r=1..R via cyclotomic reduction; returns dict r->E_r."""
    reps = rep_vectors(n)
    half = n // 2
    cur = defaultdict(int)
    cur[tuple([0]*half)] = 1
    out = {}
    for r in range(1, R+1):
        nxt = defaultdict(int)
        for v, c in cur.items():
            for rv in reps:
                w = tuple(v[i]+rv[i] for i in range(half))
                nxt[w] += c
        cur = nxt
        out[r] = sum(c*c for c in cur.values())
    return out

def dfodd(r):
    res = 1
    for k in range(1, r+1): res *= (2*k-1)
    return res

def main():
    print("ISSUE #444 [cr-monotonicity-DEEP] char-0 exact, r up to deep, structural test\n")
    # n vs how deep we can push (state-space ~ (2r+1)^{n/2}; keep tractable)
    plan = [(4, 14), (8, 12), (16, 8), (32, 5)]
    all_ok_c = True
    all_ok_a = True
    for n, R in plan:
        E = char0_energy_upto(n, R)
        a = {r: Fraction(E[r], dfodd(r)*n**r) for r in range(1, R+1)}
        print(f"==== n={n} (r up to {R}) ====")
        print(f"  {'r':>2} {'a_r':>11} {'c_r':>11} {'slack_r=W-E':>16} {'slack_{r+1}/slack_r':>20} {'vs n':>6}")
        for r in range(1, R+1):
            Wick = dfodd(r)*n**r
            slack = Wick - E[r]
            ar = a[r]
            if r < R:
                cr = Fraction((1+2*r)*a[r+1] - a[r], 2*r)
                Wick1 = dfodd(r+1)*n**(r+1)
                slack1 = Wick1 - E[r+1]
                ratio = Fraction(slack1, slack) if slack != 0 else None
                cr_s = f"{float(cr):.6f}" + ("" if cr <= 1 else " >1!!")
                rt_s = f"{float(ratio):.4f}" if ratio is not None else "   --"
                if cr > 1: all_ok_c = False
            else:
                cr_s = "   --"; rt_s = "   --"
            if ar > 1: all_ok_a = False
            print(f"  {r:>2} {float(ar):>11.6f} {cr_s:>11} {float(slack):>16.3e} {rt_s:>20} {n:>6}")
        print()
    print("="*70)
    print(f"  (T1) a_r <= 1 (Lam-Leung Wick bound) all measured r,n: {'HOLDS' if all_ok_a else 'VIOLATED'}")
    print(f"  (T2) c_r <= 1 all measured DEEP r,n:                   {'HOLDS' if all_ok_c else 'VIOLATED'}")
    print("  (T3/T4) structural reformulation:")
    print("    c_r <= 1  <=>  slack_{r+1} >= n * slack_r   (slack_r = Wick_r - E_r >= 0).")
    print("    If the slack-ratio column is >= n EVERYWHERE, c_r<=1 is the super-geometric")
    print("    slack-growth law (a Lam-Leung CONSEQUENCE in char-0, ALL r).")

if __name__ == "__main__":
    main()

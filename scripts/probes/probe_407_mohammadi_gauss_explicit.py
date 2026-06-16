import math
def log2(x): return math.log(x,2)
# GENERALIZE Lemma 14 to the L^{2r} moment (the deep-moment method, = in-tree CharSumMomentDeepWall arrow).
# Standard:  sum_{a in F_q} |S(a,H)|^{2r} = q * E_r(H)   (E_r = # of 2r-tuples in H summing in pairs).
#   (because S(a,H)=sum_h psi(ah); raising to |.|^{2r} and summing over a picks out
#    h_1+..+h_r = h_{r+1}+..+h_{2r}; the a-sum gives q times that count = q E_r(H).)
# => max_a |S(a,H)|^{2r} <= sum_a |S|^{2r} = q E_r(H)  =>  M <= (q E_r(H))^{1/(2r)}.
# This is EXACTLY the in-tree arrow M <= (q E_r)^{1/2r}.  (Lemma 14 branch2 = r=4 case: M<=(q E_4)^{1/8};
#  with E_4(mu_n) ~ (2*4-1)!!*n^4 = 105 n^4 char-0, (q*105 n^4)^{1/8} ~ q^{1/8} n^{1/2}. matches.)
#
# char-0 (PROVEN Lam-Leung):  E_r(mu_n) = (2r-1)!! n^r  (Gaussian/Wick value).  Defect <= n^{2r}/q.
# Validity of char-0 value at the prize: need defect n^{2r}/q << (2r-1)!! n^r, i.e. n^r/q << (2r-1)!!,
#   i.e. r*a - (a+128) << log2((2r-1)!!).  This is the r_max wall: r <= r_max where n^{r}~q.
#   r_max ~ (a+128)/a = 1 + 128/a.  (a=40 => r_max ~ 4.2; a=30 => 5.27; a=20 => 7.4; a=10 => 13.8.)
#
# So M <= (q (2r-1)!! n^r)^{1/(2r)} = q^{1/(2r)} n^{1/2} ((2r-1)!!)^{1/(2r)}.
#   minimized at large r: q^{1/(2r)} -> 1, ((2r-1)!!)^{1/2r} ~ sqrt(2r/e). For r ~ (1/2)ln q:
#   q^{1/(2r)} = e, ((2r-1)!!)^{1/2r} ~ sqrt(ln q /e). => M <~ sqrt(n ln q). THE TARGET.
#   BUT r must be <= r_max = 1+128/a (char-0 validity). The optimal r* = (1/2)ln q = (a+128)ln2/2 is HUGE.
print("Optimal r* (to reach sqrt(n ln q)) vs r_max (char-0 validity ceiling):")
print(f"{'a':>3} {'r*=0.5 ln q':>12} {'r_max=1+128/a':>14} {'M at r_max':>14} {'M at r* (if valid)':>18} {'target':>10} {'trivial':>9}")
for a in [10,20,30,32,40]:
    n=2.0**a; log2q=a+128.0; q=2.0**log2q
    lnq = log2q*math.log(2)
    r_star = 0.5*lnq
    r_max = 1.0 + 128.0/a
    def Mr(r):
        from math import lgamma
        # (2r-1)!! = (2r)!/(2^r r!); use log
        # log2((2r-1)!!) ~ r*log2(2r) - r*log2(e) roughly; use exact via gamma for double factorial
        # (2r-1)!! = 2^r * Gamma(r+1/2)/sqrt(pi)
        log2_df = r*1.0 + (math.lgamma(r+0.5)-0.5*math.log(math.pi))/math.log(2)
        return (1.0/(2*r))*(log2q) + 0.5*a + (1.0/(2*r))*log2_df   # log2 M
    M_rmax = Mr(r_max)
    M_rstar = Mr(r_star)
    target=log2(1.5*math.sqrt(n*lnq))
    print(f"{a:>3} {r_star:>12.1f} {r_max:>14.2f} 2^{M_rmax:>11.2f} 2^{M_rstar:>15.2f} 2^{target:>7.2f} 2^{a:>6}")
print()
print("THE WALL (quantified): to REACH sqrt(n ln q) need r* = 0.5 ln q ~ 44-58 (depth ln q).")
print("But char-0 energy E_r=(2r-1)!!n^r is only valid for r <= r_max = 1+128/a ~ 4-14 (where n^r<q).")
print("At r_max the bound M <= q^{1/(2 r_max)} n^{1/2} sqrt(2 r_max/e) = q^{1/(2+256/a)} n^{1/2}*small.")
print("q^{1/(2 r_max)} = q^{a/(2(a+128))} = n^{1/2}.  => M <~ n^{1/2}*n^{1/2}=n at r_max. TRIVIAL-ish!")
print("=> deep-moment with char-0 energy stalls at ~ n (a=40: 2^41, trivial 2^40). The q^{1/(4r)} factor")
print("   only shrinks to ~n^{1/2} when r~r_max, exactly where ((2r-1)!!)^{1/2r}~n^{1/2} re-inflates it.")

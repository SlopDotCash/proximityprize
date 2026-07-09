import math
def log2(x): return math.log(x,2)
# Lemma 14 (Mohammadi, = standard, [5 eq 3.7]):
#   max_a |S(a,H)| <= min{ (q E+(H)/|H|)^{1/4},  q^{1/8} E+(H)^{1/4} }.
# This is the EXACT bridge from the additive energy E+(H) of the subgroup to the subgroup-sum house.
# (It's the L^4 / L^8 moment of the character sum, = the in-tree CharSumMomentDeepWall arrow at r=2,4.)
#
# For mu_n dyadic, the additive energy E+(mu_n) over F_q:
#   char-0 truth (proven, Lam-Leung):  E+ = E_2(mu_n) = 3n^2 - 3n  (~ 3n^2).
#   This is the GENERIC/minimal energy (only solutions are trivial + negation-pairs).
#   Over F_q the energy is >= char-0 value; the defect (extra mod-q solutions) is <= n^4/q (small).
#   So at the prize E+(mu_n) ~ 3n^2 (the n^4/q defect = 2^{4a-(a+128)}=2^{3a-128}, tiny for a<=40).
print("E+(mu_n) defect n^4/q = 2^{3a-128}:", [(a, 3*a-128) for a in [10,20,30,40]], "(all <0 => defect<1)")
print("So at prize E+(mu_n) = 3n^2 - 3n exactly (char-0 value, NO extra mod-q solutions). [GOOD - this part is clean]")
print()
# Plug E+ = 3n^2 into Lemma 14:
print(f"{'a':>3} {'branch1=(qE/|H|)^.25':>22} {'branch2=q^.125 E^.25':>22} {'min':>10} {'trivial n':>10} {'target':>10}")
for a in [10,20,30,32,40]:
    n=2.0**a; log2q=a+128.0; q=2.0**log2q
    E = 3*n*n - 3*n
    b1 = (q*E/n)**0.25
    b2 = q**0.125 * E**0.25
    mn = min(b1,b2)
    target=1.5*math.sqrt(n*math.log(q/n))
    print(f"{a:>3} 2^{log2(b1):>19.2f} 2^{log2(b2):>19.2f} 2^{log2(mn):>7.2f} 2^{a:>7} 2^{log2(target):>7.2f}")
print()
print("Lemma 14 branch1 = (q*3n^2/n)^{1/4} = (3 q n)^{1/4} ~ q^{1/4} n^{1/4} = 2^{(a+128)/4 + a/4}.")
print(" => 2^{(2a+128)/4} = 2^{a/2+32}. At a=40: 2^52. trivial n=2^40. branch1 WORSE than trivial by 2^{32}.")
print("Lemma 14 branch2 = q^{1/8}(3n^2)^{1/4} ~ q^{1/8} n^{1/2} = 2^{(a+128)/8 + a/2}. a=40: 2^{21}*2^{20}=2^41.")
print(" => branch2 = 2^{a/2 + (a+128)/8} = 2^{a/2}*q^{1/8}. The q^{1/8}=2^16 (a=10)..2^21(a=40) factor is the LOSS.")
print()
print("DECISIVE: branch2 = n^{1/2} * q^{1/8}.  Target = n^{1/2}*sqrt(log q)~n^{1/2}*11.3.")
print("Ratio branch2/target = q^{1/8}/11.3 = 2^{(a+128)/8}/11.3.  At a=40: 2^{21}/11.3 ~ 2^{17.5}.")
print("So the L^8-moment (Lemma 14) gets the n^{1/2} RIGHT but carries a q^{1/8} the prize cannot afford.")

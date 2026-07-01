# EXACT r=3 count and the INJECTION into signed 3-subsets of mu_{n/2}.
#
# #bad = #{ {a,b} subset squares, {c,d} subset nonsquares : a b = - c d }.
# Index by exponent mod n: a=w^{2i}, b=w^{2j} (i<j in Z_{n/2}), product exponent 2(i+j) mod n.
# c=w^{2k+1}, d=w^{2l+1} (k<l in Z_{n/2}), product exponent 2(k+l)+2 mod n.
# Condition: 2(i+j) = n/2 + 2(k+l)+2 mod n  <=>  i+j = n/4 + k+l + 1  mod n/2.
#
# Let m = n/2 (size of each coset = #squares). Pairs {i,j}, i<j in Z_m, with "pair-sum" s=i+j mod m.
# Pairs {k,l} similarly with sum t = k+l mod m. Condition: s = n/4 + t + 1 = t + (m/2 + 1) mod m.
# (n/4 = m/2.)  So for each square-pair-sum s, we need nonsquare-pair-sum t = s - (m/2+1) mod m.
#
# #pairs of distinct elements of Z_m with given sum s: this is N(s) = floor stuff. For Z_m,
#   #{ {i,j}: i!=j, i+j=s } = (m - [s is "doubled"])/2 ... precisely: ordered pairs (i,j) i+j=s
#   is m (i free, j=s-i). Remove i=j (i.e. 2i=s): #solutions of 2i=s in Z_m. m even (=2^{mu-1}).
#   2i=s mod m has solutions iff s even, then 2 solutions. So unordered distinct pairs:
#     N(s) = (m - (2 if s even else 0))/2 = m/2 - [s even].
# So N(s) = m/2 if s odd, m/2 - 1 if s even.
# #bad = sum over s of N(s) * N(s - (m/2+1)).  Note parity of s vs t=s-(m/2+1): m/2 is even
#   (m=2^{mu-1}, m/2=2^{mu-2}, even for mu>=3 i.e n>=16). So t = s - (even+1) = s - odd => t has
#   OPPOSITE parity to s. So exactly one of N(s),N(t) is m/2 and the other m/2-1.
#   product = (m/2)(m/2-1) for every s. There are m values of s. But each unordered (square-pair,
#   nonsquare-pair) counted once. Total = sum_s N(s)N(t). Since for each s the pair (s,t) with
#   t=s-(m/2+1): #bad = sum_{s in Z_m} N(s) N(s-(m/2+1)) = m * (m/2)(m/2-1)  ??? check: each s gives
#   N(s)*N(t) and we sum over all s (each square-pair has a unique s, each nonsquare-pair unique t,
#   and the bijection s<->t is fixed). Actually #bad = sum over square-pairs {a,b} of
#   #{nonsquare-pairs with the forced sum} = sum_s N(s)*N(t(s)). = sum_s (m/2)(m/2-1) = m*(m/2)(m/2-1).
# With m=n/2: #bad = (n/2)*(n/4)*(n/4 - 1) = (n/2)*2*C(n/4,2) = n*C(n/4,2). MATCHES O_P=C(n/4,2)!!
#
# Let's VERIFY this closed formula and the per-s structure numerically.
from math import comb
def Ncount(m):
    # N(s) for s in 0..m-1
    return [ (m//2) if (s%2==1) else (m//2 -1) for s in range(m)]
def predicted_bad(n):
    m=n//2
    N=Ncount(m)
    shift=(m//2+1)%m
    tot=0
    for s in range(m):
        t=(s-shift)%m
        tot+=N[s]*N[t]
    return tot, n*comb(n//4,2)
for n in [16,32,64,128,256]:
    tot,closed=predicted_bad(n)
    print(f"n={n}: sum_s N(s)N(t) = {tot}; n*C(n/4,2) = {closed}; match={tot==closed}; K=2^3*C(n/2,3)={8*comb(n//2,3)}; bad/K={tot/(8*comb(n//2,3)):.4f}")

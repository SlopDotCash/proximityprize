#!/usr/bin/env python3
"""
Exhibit ONE concrete char-p accidental vanishing subset at n=16, q=97 that is NOT a
union of mu_2-cosets, witnessing that C034's "empty unless 2^L|(k+t)" is char-0 only.
Case: a=5, t=2 (formula predicts 0; actual 16). t=2 means just e_1(S)=sum(S)=0.
So we need a 5-subset of mu_16 summing to 0 mod 97 that is NOT a coset union (5 is odd,
can't be a union of mu_2-cosets at all -> ANY such subset is a pure char-p accident).
"""
import itertools

def is_prime(m):
    if m<2: return False
    i=2
    while i*i<=m:
        if m%i==0: return False
        i+=1
    return True

def mu_n_elements(q,n):
    def order(a,q):
        o=1;x=a%q
        while x!=1:
            x=(x*a)%q;o+=1
        return o
    g=next(c for c in range(2,q) if order(c,q)==q-1)
    base=pow(g,(q-1)//n,q)
    return [pow(base,i,q) for i in range(n)], base

q=97; n=16
assert q%n==1 and is_prime(q)
mu, base = mu_n_elements(q,n)
print(f"n={n}, q={q}, mu_{n} = {mu}")
print(f"primitive {n}-th root base = {base}")
# find 5-subsets summing to 0 mod q
wit=[]
for S in itertools.combinations(range(n),5):
    vals=[mu[i] for i in S]
    if sum(vals)%q==0:
        wit.append((S,vals))
print(f"\n#5-subsets of mu_16 with sum=0 mod 97: {len(wit)} (formula C034 predicts 0)")
print("First few witnesses (exponent-set, values, additive relation mod 97):")
for S,vals in wit[:4]:
    print(f"  exps={S} vals={vals} sum mod {q} = {sum(vals)%q}")
print("\nThese are odd-size, so NOT unions of mu_2-cosets: pure char-p additive coincidences.")
print("They are exactly the short {0,1}-coefficient relations among 2^4-th roots mod q")
print("whose ABSENCE ('relation-free') C034 must assume -- and whose presence/absence at")
print("the prize prime q~2^158 (n=2^30) is the open BGK/generalized-Paley wall.")

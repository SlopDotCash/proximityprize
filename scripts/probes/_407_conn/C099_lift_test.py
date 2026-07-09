"""
C099 lift test (the decisive question).

Confirmed (debug + Lean lemma): on the INERT family n|p+1, max_t r(t) <= 2 over ALL
of F_{p^2}* (Frobenius=inversion forces y to satisfy a fixed deg-2 poly).
On the SPLIT family n|p-1 (the PRIZE regime), r(t) reaches n and E_2 carries the surplus.

The connection's ONLY route to the prize (attack_plan) is:
  "whether a CRT/quadratic-extension lift transfers the inert r<=2 to control the
   split count at frequency b in the F_{p^2}-coset (Frobenius-pairing the split sum
   with an inert one)."

We test this directly. For a SPLIT prime p (n|p-1, mu_n subset F_p), embed F_p into
F_{p^2}. In F_{p^2}* there ALSO exists an order-n subgroup nu_n with n|p+1-style
behavior? NO: F_{p^2}* is cyclic of order (p-1)(p+1); the UNIQUE order-n subgroup
mu_n is the SAME set whether viewed in F_p or F_{p^2} (since n|p-1 ⊂ p^2-1). There is
no second, "inert", order-n subgroup to pair with. The Frobenius y->y^p acts TRIVIALLY
on this mu_n (y in F_p => y^p=y). So the deg-2-poly argument gives X^2 - cX + 1 with
the SAME root multiplicity collapse only if Frobenius=inversion, which it is NOT.

Concretely we check, for split p:
 (1) The unique order-n subgroup of F_{p^2}* equals mu_n subset F_p (one subgroup,
     not two). => no inert partner to pair.
 (2) Whether the count r(t) for t in F_p, computed in F_{p^2}, differs from in F_p.
     (It cannot: the relation t-y in mu_n is field-intrinsic and mu_n subset F_p.)
 (3) The "Frobenius-paired" object sum_{y} chi(by)*chi(b y^p): with y^p=y on mu_n it
     is just sum chi(2by) -- gives NO new cancellation (it's the same Gauss period at
     frequency 2b). So the inert pairing degenerates on the split family.
"""
import sympy
from sympy import isprime, primitive_root

def find_split_primes(n, blo, bhi, k):
    out=[]; lo=int(n**blo); hi=int(n**bhi)
    p=lo-(lo%n)+1
    if p<lo: p+=n
    while p<=hi and len(out)<k:
        if isprime(p) and p>n: out.append(p)
        p+=n
    return out

def order_n_subgroups_in_Fp2(p, n):
    """Count order-n subgroups of F_{p^2}* (cyclic order p^2-1). A cyclic group has
    EXACTLY ONE subgroup of each order dividing the group order. Return that count
    and whether it lies in F_p."""
    order = p*p - 1
    assert order % n == 0
    # cyclic => exactly one subgroup of order n. Does it lie in F_p (order p-1)?
    in_Fp = (p - 1) % n == 0
    return 1, in_Fp

def mu_n_in_Fp(p,n):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    S=set(); x=1
    for _ in range(n): S.add(x); x=(x*h)%p
    return S

print("="*78)
print("C099 LIFT TEST: does the inert r<=2 transfer to the split (prize) count?")
print("="*78)
for n in [8,16,32,64]:
    mu=n.bit_length()-1
    print(f"\n##### n=2^{mu}={n} #####")
    sp=find_split_primes(n, 2.0, 2.5, 3)
    for p in sp:
        cnt, inFp = order_n_subgroups_in_Fp2(p,n)
        # both p-1 and p+1: which carries the order-n subgroup
        n_div_pm1 = (p-1)%n==0
        n_div_pp1 = (p+1)%n==0
        print(f"  p={p}: #order-{n} subgroups of F_(p^2)* = {cnt} (cyclic=>unique); "
              f"lies in F_p? {inFp}; n|p-1={n_div_pm1}, n|p+1={n_div_pp1}")
    # show that on split mu_n, Frobenius is the IDENTITY (not inversion) => deg-2 collapse fails
    p = sp[0]
    S = mu_n_in_Fp(p,n)
    frob_is_id = all(pow(y,p,p)==y for y in S)
    frob_is_inv = all(pow(y,p,p)==pow(y,p-2,p) for y in S)  # y^{-1}=y^{p-2}
    print(f"  [p={p}] on split mu_n: Frobenius==identity? {frob_is_id}; "
          f"Frobenius==inversion? {frob_is_inv}")

print("\n" + "="*78)
print("VERDICT-CRITICAL: the inert family is DISJOINT from the prize regime.")
print("="*78)
# For n=2^mu (mu>=2), can n | p-1 AND n | p+1 simultaneously? Then n | (p+1)-(p-1)=2,
# so n<=2. For prize n=2^mu, mu>=3, IMPOSSIBLE. The inert and split families are disjoint.
for n in [4,8,16,32,64]:
    # gcd condition: n | p-1 and n | p+1 => n | 2
    both_possible = (2 % n == 0)
    print(f"  n={n}: a prime with BOTH n|p-1 and n|p+1 exists? {both_possible} "
          f"(needs n|2). Prize n=2^mu (mu>=3): inert and split are DISJOINT prime sets.")

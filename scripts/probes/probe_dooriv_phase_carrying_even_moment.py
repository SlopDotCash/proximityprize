# Door-(iv) Lane-1: the UNMODULATED (phase-carrying) 4th moment E_b[eta_b^4]
# vs the modulus 4th moment E_b[|eta_b|^4] (= additive energy E2, PROVEN dead).
# eta_b = sum_{x in mu_n} e_p(b * x)  ... wait, the prize object is the MONOMIAL sum.
# Actually eta_b = sum over the thin subgroup mu_n of e_p(b*x). Worst-b max is M(n).
# Question (campaign terminal pointer): is E_b[eta_b^4] a NEW phase object or does it
# also collapse to a real additive count?  By char orthogonality:
#   (1/p) sum_b eta_b^4 = #{(x1,x2,x3,x4) in S^4 : x1+x2+x3+x4 = 0}   (a SIGNED-free count)
#   (1/p) sum_b |eta_b|^4 = #{x1+x2 = x3+x4}  = E2  (the dead energy)
# So E_b[eta^4] counts ZERO-SUM quadruples (4-term additive), NOT the energy E2.
# These are DIFFERENT counts. Probe both, and the cross E_b[eta^3 conj(eta)] = #{x1+x2+x3=x4}.
import cmath, math

def is_prime(n):
    if n<2: return False
    if n%2==0: return n==2
    i=3
    while i*i<=n:
        if n%i==0: return False
        i+=2
    return True

def find_prime(target, n):
    # need n | p-1, p prime, p approx target
    p = target - (target % n) + 1
    while True:
        if p>2 and is_prime(p) and (p-1)%n==0:
            return p
        p += n

def subgroup(p, n):
    # multiplicative subgroup of order n in F_p^*
    g = None
    # find generator of full group first via a primitive root
    # easier: find element of order exactly n: take h = a^((p-1)/n) for random a, check order n
    import random
    m = (p-1)//n
    for a in range(2, p):
        h = pow(a, m, p)
        # order of h divides n; check it's exactly n
        if pow(h, n, p)==1:
            # verify primitive: h^(n/q)!=1 for prime q|n
            ok=True
            nn=n; q=2; primes=set()
            while nn>1:
                while nn%q==0:
                    primes.add(q); nn//=q
                q+=1
            for q in primes:
                if pow(h, n//q, p)==1:
                    ok=False; break
            if ok:
                S=[]
                v=1
                for _ in range(n):
                    S.append(v); v=(v*h)%p
                return S
    return None

def probe(n, beta=3.2):
    target = int(n**beta)
    p = find_prime(target, n)
    S = subgroup(p, n)
    assert len(S)==n
    # exact: zero-sum quadruple count Z4 = #{x1+x2+x3+x4 ≡0}, energy E2=#{x1+x2=x3+x4},
    # triple-to-one T = #{x1+x2+x3 ≡ x4}
    # use convolution counts via residue histogram of pairwise sums
    from collections import Counter
    sums2 = Counter()
    for x in S:
        for y in S:
            sums2[(x+y)%p]+=1
    E2 = sum(c*c for c in sums2.values())  # #{x1+x2=x3+x4}
    # Z4 = #{x1+x2 = -(x3+x4)} = sum_t sums2[t]*sums2[(-t)%p]
    Z4 = sum(sums2[t]*sums2[(-t)%p] for t in sums2)
    # T (triple=single): #{x1+x2+x3 = x4} = sum over x4 of #{x1+x2+x3 = x4}
    # = sum_{x4} ( #{x1+x2 = x4 - x3 over x3} ) ; do sums3 = sum2 * S
    sums3 = Counter()
    for t,c in sums2.items():
        for z in S:
            sums3[(t+z)%p]+=c
    T = sum(sums3[x] for x in S)  # #{x1+x2+x3 = x4}
    # ratios vs random baseline: for a random n-subset, Z4 ~ n^4/p, E2 ~ n^4/p + (deg pairs)
    rnd = n**4 / p
    return p, E2, Z4, T, rnd

print(f"{'n':>4} {'p':>12} {'E2(modulus)':>14} {'Z4(phase,4-sum)':>16} {'T(3to1)':>12} {'n^4/p':>10} {'Z4/rnd':>8} {'E2/rnd':>8}")
for n in [8,16,32,64,128]:
    p,E2,Z4,T,rnd = probe(n)
    print(f"{n:>4} {p:>12} {E2:>14} {Z4:>16} {T:>12} {rnd:>10.2f} {Z4/rnd:>8.3f} {E2/rnd:>8.3f}")

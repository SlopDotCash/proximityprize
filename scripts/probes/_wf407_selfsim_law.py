import cmath, math, sympy
def primitive_root(p): return int(sympy.primitive_root(p))
def periods(p,n):
    g=primitive_root(p); d=(p-1)//n; h=pow(g,d,p)
    S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    m=(p-1)//n; w=2*math.pi/p
    out=[]; rep=1
    for i in range(m):
        s=sum(cmath.exp(1j*w*((rep*x)%p)) for x in S); out.append(s); rep=(rep*g)%p
    return max(abs(z) for z in out)

# Self-similar law: average B(2n)/B(n) across many primes, as a function of n (away from
# degenerate Fermat-prime / thin worst cases). Want: ratio -> sqrt(2)*(1+o(1)), the dyadic growth.
print("=== B(2n)/B(n) averaged over several large-m primes (fixed-index, non-degenerate) ===")
def primes_1modN_list(n, start, count):
    out=[]; cand=start|1
    while len(out)<count:
        if (cand-1)%n==0 and sympy.isprime(cand): out.append(cand)
        cand+=2
    return out
for n in (16,32,64,128):
    ratios=[]
    for p in primes_1modN_list(2*n, 2*n*500, 6):  # ensure 2n | p-1, large m
        Bn=periods(p,n); B2n=periods(p,2*n)
        ratios.append(B2n/Bn)
    avg=sum(ratios)/len(ratios)
    print(f"n={n:3d}->2n: mean B(2n)/B(n) = {avg:.4f}   sqrt2={math.sqrt(2):.4f}   samples={[f'{r:.3f}' for r in ratios]}")

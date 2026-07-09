from sympy import isprime, primitive_root
p=26034433
print(f"p={p}, prime={isprime(p)}, p-1={p-1}",flush=True)
for n in [64,128]:
    if (p-1)%n==0:
        g=primitive_root(p); z=pow(g,(p-1)//n,p)
        T_idx=[3,36,50,52]
        T=[pow(z,i,p) for i in T_idx]
        print(f"\nn={n}: T=zeta^{T_idx}",flush=True)
        # power sums p_j = sum_{x in T} x^j mod p, for j=1..8
        ps=[sum(pow(x,j,p) for x in T)%p for j in range(1,9)]
        print(f"  power sums p_1..p_8 mod {p}: {ps}",flush=True)
        zeros=[j+1 for j,v in enumerate(ps) if v==0]
        odd_zeros=[j for j in zeros if j%2==1]
        print(f"  vanishing power sums at j: {zeros}; ODD vanishing: {odd_zeros}",flush=True)
        # antipodal-free? check if -x in T for any x
        Tset=set(T); af=all((p-x)%p not in Tset for x in T)
        print(f"  antipodal-free: {af}",flush=True)
        # is T a coset of some mu_d? check x^d equal for all
        for d in [2,4,8,16,32]:
            vals=set(pow(x,n//d,p) for x in T) if n%d==0 else None
            if vals and len(vals)==1 and len(T)==n//d:
                print(f"  IS a mu_{n//d}-coset",flush=True)

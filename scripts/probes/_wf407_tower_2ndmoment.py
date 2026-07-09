import cmath, math, sympy
def primitive_root(p): return int(sympy.primitive_root(p))
def gen_order_n(p,n):
    g=primitive_root(p); d=(p-1)//n; return pow(g,d,p), g
def subgroup_set(p,n):
    h,_=gen_order_n(p,n); S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    return S
def eta(p,S,b):
    w=2*math.pi/p; return sum(cmath.exp(1j*w*((b*x)%p)) for x in S)

# From eta_b(2n)=eta_b(n)+eta_{b zeta}(n):
#  |eta_b(2n)|^2 = |eta_b(n)|^2 + |eta_{b zeta}(n)|^2 + 2 Re(eta_b(n) conj eta_{b zeta}(n))
# Sum over b in cosets of mu_{2n}.  Question: does the cross term sum to ZERO (=> V2 doubles cleanly)?
print("=== 2nd-moment tower recursion + cross-term cancellation ===")
print("Claim: V2(2n) over its m'=m/2 cosets   relates to V2(n).  And cross-term avg.")
for p in [12289, 40961, 786433]:
    for n in [8,16,32,64]:
        if (p-1)%(2*n): continue
        Sn=subgroup_set(p,n); S2n=subgroup_set(p,2*n)
        h2n,_=gen_order_n(p,2*n); zeta=h2n
        g=primitive_root(p)
        m2=(p-1)//(2*n)
        # cosets of mu_{2n}: reps g^i, i=0..m2-1
        cross=0.0; v2_2n=0.0
        rep=1
        Bvals=[]
        for i in range(m2):
            a=eta(p,Sn,rep); c=eta(p,Sn,(rep*zeta)%p)
            lhs=a+c
            Bvals.append(abs(lhs))
            v2_2n+=abs(lhs)**2
            cross+= (a*c.conjugate()).real
            rep=(rep*g)%p
        # V2(2n) should = ((2n-1)p+1)/(2n) [Garcia Lemma15, with their d=m2]... actually their V2 sums over d=m2 cosets
        v2_pred=((m2-1)*p+1)/m2  # = (d-1)p+1)/d with d=m2 (number of periods of mu_{2n})
        print(f"p={p} n={n}: m'(2n)={m2}  V2(2n)_emp={v2_2n:.1f} pred={v2_pred:.1f}  crossSum={cross:.3f}  cross/V2={cross/v2_2n:.4f}  B(2n)={max(Bvals):.3f}")

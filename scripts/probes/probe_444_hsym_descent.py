import itertools
from sympy import primitive_root
def subgroup(n,p):
    g=primitive_root(p); z=pow(g,(p-1)//n,p)
    e,x=[],1
    for _ in range(n): e.append(x); x=(x*z)%p
    return e
def h_sym(T,j,p):
    # complete homogeneous symmetric h_j(T) via generating function coeffs: prod 1/(1-t x) up to x^j
    # = sum over multisets; compute via recurrence h_j = sum_i t_i * (h_{j} with...) -- use power-series mult
    coeff=[1]+[0]*j  # 1/(prod) numerator... actually build prod 1/(1-t x) = prod (1 + t x + t^2 x^2+...)
    for t in T:
        new=[0]*(j+1)
        for d in range(j+1):
            s=0; tk=1
            for e in range(d+1):
                s=(s+coeff[d-e]*tk)%p; tk=(tk*t)%p
            new[d]=s
        coeff=new
    return coeff[j]
print("### DESCENT IDENTITY: h_{2j}(T) = h_j(T^2) and h_{odd}(T)=0 for antipodal-symmetric T ###",flush=True)
n=16; p=65537; elts=subgroup(n,p); neg={x:(p-x)%p for x in elts}
import random; random.seed(2)
ok2=ok_odd=tot=0
for _ in range(60):
    # build antipodal-symmetric T: pick m pairs
    pairs=random.sample(range(n//2),random.randint(2,4))
    # map: elt i and its antipode. find antipode-free reps
    reps=[]; used=set()
    for x in elts:
        if x in used: continue
        reps.append(x); used.add(x); used.add(neg[x])
    chosen=[reps[i] for i in pairs if i<len(reps)]
    T=[]
    for x in chosen: T+= [x, neg[x]]
    if len(set(T))!=2*len(chosen): continue
    Tsq=[(x*x)%p for x in chosen]  # squared half (one per pair)
    tot+=1
    for j in range(1,4):
        if h_sym(T,2*j,p)==h_sym(Tsq,j,p): ok2+=1
        if h_sym(T,2*j-1,p)==0: ok_odd+=1
print(f"  antipodal-sym T trials={tot}: h_2j(T)==h_j(T^2): {ok2}/{tot*3}; h_odd(T)==0: {ok_odd}/{tot*3}",flush=True)

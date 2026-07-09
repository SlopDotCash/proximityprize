exec(open('scripts/probes/probe_444_worstword_exponent.py').read().split('if __name__')[0])
import itertools
def elem_sym(roots, p, upto):
    # e_1..e_upto of the multiset roots mod p
    e=[1]+[0]*upto
    for r in roots:
        for i in range(min(len(e)-1,upto),0,-1):
            e[i]=(e[i]+e[i-1]*r)%p
    return e[1:upto+1]
def list_and_lacunary(n, p):
    elts=subgroup(n,p)
    k=n//8; s=n//4   # x^{n/4}+1, eta=1/8, s=(rho+eta)n=n/4
    u=[(pow(x,n//4,p)+1)%p for x in elts]
    # (a) window list via list_RS
    L=list_RS(u,elts,k,s,p)
    # (b) lacunary count: #{ (n/4)-subsets T of mu_n : e_1..e_{n/8}(T)=0 mod p }
    cnt=0; tcap=n//8
    for T in itertools.combinations(elts, n//4):
        es=elem_sym(T,p,tcap)
        if all(e==0 for e in es): cnt+=1
    return L,cnt,s,k
print("### list(x^{n/4}+1) =?= #{n/4-subsets T: e_1..e_{n/8}(T)=0} (the dyadic lacunary count) ###",flush=True)
for n in [16]:
    for beta in [4.0,4.5]:
        p=find_window_prime(n,beta)
        L,cnt,s,k=list_and_lacunary(n,p)
        print(f"   n={n} p={p} k={k} s={s}: window_list={L}  lacunary_count={cnt}  {'MATCH' if L==cnt else 'DIFFER'}",flush=True)

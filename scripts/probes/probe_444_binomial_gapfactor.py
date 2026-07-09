exec(open('scripts/probes/probe_444_worstword_exponent.py').read().split('if __name__')[0])
import itertools
def elem_sym(roots,p,upto):
    e=[1]+[0]*upto
    for r in roots:
        for i in range(min(len(e)-1,upto),0,-1): e[i]=(e[i]+e[i-1]*r)%p
    return e[1:upto+1]
print("### REFORMULATION: lacunary subsets (e_1..e_{n/8}=0) == root-sets of X^{n/4}-c, c in mu_4 ? ###",flush=True)
for n in [16,32]:
    p=find_window_prime(n,4.0); elts=subgroup(n,p); S=set(elts)
    tcap=n//8; sz=n//4
    # all lacunary subsets
    lac=[]
    if n==16:
        for T in itertools.combinations(elts,sz):
            if all(e==0 for e in elem_sym(T,p,tcap)): lac.append(frozenset(T))
    # binomial root-sets: roots of X^{n/4}-c for c a 4th root of unity in F_p
    # mu_4 = {x in F_p: x^4=1}; find them
    g=primitive_root(p); mu4=[pow(g,(p-1)//4*i,p) for i in range(4)]
    binom=[]
    for c in mu4:
        roots=frozenset(x for x in elts if pow(x,n//4,p)==c)
        if len(roots)==sz: binom.append(roots)
    print(f"  n={n} p={p}: #mu4={len(set(mu4))} #binomial-rootsets(size {sz})={len(set(binom))}",flush=True)
    if n==16:
        print(f"     #lacunary-subsets={len(lac)}  binomials==lacunary: {set(lac)==set(binom)}",flush=True)

import cmath, math

def primitive_root(p):
    # find generator of F_p^*
    def order(g):
        o=1; x=g%p
        while x!=1:
            x=x*g%p; o+=1
        return o
    for g in range(2,p):
        if order(g)==p-1:
            return g
    raise Exception("no g")

def run_cell(p, m, ncols, dY, label):
    """
    Reconstruct chiFamily/residual objects faithfully (a DIFFERENT construction
    than the file's cells).
      - g primitive root mod p
      - full additive char psi(x)=exp(2pi i x/p)
      - base mult char chi1(g^a)=exp(2pi i a/(p-1)); chi = chi1^((p-1)/m) has order m
      - chiFamily = {chi^j : 1<=j<m}
      - twistedThinSum(c,G,t)=sum_{x in G} conj(c(t-x)); c(0)=0
      - gaussSum(c,psi)=sum_{x} c(x) psi(x)
      - residual(s0)= sum_{c in family\Y} gaussSum(c)*twistedThinSum(c,G,s0)
    Y = chiFamily(chi^dY) (an even inversion-closed sub-block).
    """
    assert (p-1)%m==0
    g=primitive_root(p)
    # discrete log table
    dlog={}
    x=1
    for a in range(p-1):
        dlog[x]=a; x=x*g%p
    def chi_pow(j):  # character chi^j : returns function on F_p
        # chi = chi1^((p-1)/m), order m; chi^j(g^a)=exp(2pi i * a * ((p-1)/m)*j /(p-1))
        k=((p-1)//m)*j % (p-1)
        def f(v):
            v%=p
            if v==0: return 0j
            return cmath.exp(2j*math.pi*(dlog[v]*k)/(p-1))
        return f
    def psi(v):
        return cmath.exp(2j*math.pi*(v%p)/p)
    def gauss(j):
        c=chi_pow(j)
        return sum(c(v)*psi(v) for v in range(p))
    # domain G = multiplicative subgroup mu_n (n=ncols): powers of g^((p-1)/ncols)
    assert (p-1)%ncols==0
    h=pow(g,(p-1)//ncols,p)
    G=set()
    x=1
    for _ in range(ncols):
        G.add(x); x=x*h%p
    G=sorted(G)
    def T(j,t):
        c=chi_pow(j)
        return sum((c((t-x)%p)).conjugate() for x in G)
    # chiFamily(chi) = {chi^j: 1<=j<m}
    fam=list(range(1,m))
    # Y = chiFamily(chi^dY): {(chi^dY)^i:1<=i<ord(chi^dY)}. ord(chi^dY)=m/gcd(m,dY)
    gg=math.gcd(m,dY); ordY=m//gg
    Yset=set()
    for i in range(1,ordY):
        Yset.add((dY*i)%m if (dY*i)%m!=0 else None)
    Yset.discard(None)
    Yset={y for y in Yset if 1<=y<m}
    comp=[j for j in fam if j not in Yset]
    # check chi^j(-1)=1 for all j (even regime): needs 2m|p-1
    even_ok = all(abs(chi_pow(j)(p-1)-1)<1e-9 for j in fam)  # -1 = p-1
    # inversion closed check on comp
    inv_closed = all(((m-j)%m) in comp for j in comp)
    # residual over complement (the "Res")
    maxim=0.0
    for s0 in range(p):
        val=sum(gauss(j)*T(j,s0) for j in comp)
        maxim=max(maxim, abs(val.imag))
    # Main_Y over Yset (the "M'" up to the -n constant which is real)
    maxim_Y=0.0
    Ylist=sorted(Yset)
    for s0 in range(p):
        val=sum(gauss(j)*T(j,s0) for j in Ylist)
        maxim_Y=max(maxim_Y, abs(val.imag))
    print(f"[{label}] p={p} m={m} n={ncols} dY={dY}: 2m|p-1={(p-1)%(2*m)==0} even_ok={even_ok} inv_closed={inv_closed} |comp|={len(comp)} |Y|={len(Ylist)}")
    print(f"    max|Im Res|={maxim:.2e}   max|Im Main_Y|={maxim_Y:.2e}")
    return maxim, maxim_Y

# Fresh cells: 2m|p-1 required. Different from file's {97,193,257,1153}.
run_cell(41, 4, 8, 2, "cellA")     # 2m=8|40
run_cell(101,5,10, 2, "cellB")     # 2m=10|100
run_cell(61, 6, 12, 3, "cellC")    # 2m=12|60
run_cell(241,8,16, 4, "cellD")     # 2m=16|240 (m=8 like file but fresh p)
# a NON-even control: 2m does NOT divide p-1 -> expect nonzero Im
run_cell(29,7,7,1,"ctrl-nonEven")  # m=7, 2m=14, p-1=28, 14|28 actually even... pick m where 2m nmid
run_cell(31,5,5,1,"ctrl2")         # m=5,2m=10,p-1=30 ->10|30 even too
run_cell(23,11,11,1,"ctrl-odd")    # m=11,2m=22,p-1=22->22|22 even. hard to break with subgroup m|p-1

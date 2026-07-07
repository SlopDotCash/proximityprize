import cmath, math

def probe(p, n, m):
    # mu_n subgroup of F_p^*, H index-m subgroup (needs m | p-1, n | (p-1)/m so mu_n <= H)
    assert (p-1) % n == 0 and (p-1) % m == 0 and ((p-1)//m) % n == 0
    # find generator
    def is_gen(g):
        for qf in set(fac(p-1)):
            if pow(g, (p-1)//qf, p) == 1: return False
        return True
    def fac(x):
        f=[]; d=2
        while d*d<=x:
            while x%d==0: f.append(d); x//=d
            d+=1
        if x>1: f.append(x)
        return f
    g = next(a for a in range(2,p) if is_gen(a))
    e = lambda t: cmath.exp(2j*math.pi*t/p)
    mun = set(pow(g,(p-1)//n*i,p) for i in range(n))
    H = set(pow(g,m*i,p) for i in range((p-1)//m))
    assert mun <= H
    eta = {b: sum(e(b*x % p) for x in mun) for b in range(p)}
    Sigma = sum(abs(eta[b])**2 for b in H)
    fair = n*(p-n)/m
    # exact identity: m*Sigma = (np - n^2) + sum_{j=1}^{m-1} A_j
    # A_j = sum_{x!=y in mun} gauss(chi^j, psi_{x-y}) ; check via direct char sum
    chi = lambda b,j: cmath.exp(2j*math.pi*j*(dlog[b])/ m) if b%p else 0
    dlog = {}
    a=1
    for k in range(p-1):
        dlog[a]=k; a=a*g%p
    A = [sum(chi(b,j)*abs(eta[b])**2 for b in range(1,p)) for j in range(m)]
    lhs = m*Sigma
    rhs = sum(A)  # A[0] should = np-n^2
    ok1 = abs(lhs-rhs.real)<1e-6 and abs(rhs.imag)<1e-6
    ok0 = abs(A[0] - (n*p-n*n)) < 1e-6
    # triangle bound on A_j, j>=1
    bnd = n*(n-1)*math.sqrt(p)
    okA = all(abs(A[j]) <= bnd+1e-6 for j in range(1,m))
    # final: Sigma >= n*p/(2m) when p >= 16 m^2 n^2
    inreg = p >= 16*m*m*n*n
    okS = (Sigma >= n*p/(2*m)-1e-6) if inreg else None
    print(f"p={p} n={n} m={m}: Sigma={Sigma:.2f} fair={fair:.2f} ratio={Sigma/fair:.4f} "
          f"identity_ok={ok1} A0_ok={ok0} triangle_ok={okA} inregime={inreg} hSig_ok={okS} "
          f"maxAj/bnd={max((abs(A[j])/bnd for j in range(1,m)), default=0):.3f}")

for (p,n,m) in [(97,8,2),(97,8,4),(113,8,2),(193,8,2),(193,16,4),(257,16,2),(257,8,4),
                (7681,16,2),(7681,16,4),(12289,16,2),(12289,16,4),(65537,16,2),(65537,16,4),
                (65537,32,2),(65537,8,8),(59393,16,4),(786433,16,4),(786433,8,8)]:
    try:
        probe(p,n,m)
    except AssertionError:
        print(f"p={p} n={n} m={m}: divisibility fails, skipped")

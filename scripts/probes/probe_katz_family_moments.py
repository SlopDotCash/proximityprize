import numpy as np
from sympy import isprime, primitive_root

# Setup: p prime, p=1 mod n, n=2^mu. mu_n subgroup. 
# Gauss periods eta_b = sum_{x in mu_n} e_p(b x).
# Identity: eta_b = (1/m)[-1 + sum_{j=1}^{m-1} psi(b)^{-j} tau(psi^j)], m=(p-1)/n.
# S(w) = sum_{j=1}^{m-1} w^{-j} a_j, a_j = tau(psi^j)/sqrt(p) unimodular.
# CLAIM to verify: the family {S(w): w^m=1} = {m*eta_b + 1 : b}.
# => moments-of-the-family integral (1/m) sum_w |S(w)|^{2r} = m^{2r-1} sum_b |eta_b + 1/m|^{2r}.

def setup(p, n):
    assert isprime(p) and (p-1)%n==0
    g = primitive_root(p)
    m = (p-1)//n
    # subgroup mu_n = <g^m>
    h = pow(g, m, p)
    mu = [pow(h, i, p) for i in range(n)]
    # Gauss periods over all b in F_p^*  (m distinct values, one per coset of mu_n)
    ep = np.exp(2j*np.pi/p)
    eta = {}
    # coset reps: g^k for k=0..m-1
    for k in range(m):
        b = pow(g, k, p)
        val = sum(ep**((b*x) % p) for x in mu)
        eta[k] = val
    return g, m, mu, eta, ep

def gauss_sum_table(p, n, g, m):
    # multiplicative character psi of order m: psi(g^t) = exp(2pi i t / m)? 
    # Actually psi should be a character of F_p^*/mu_n ~ Z/m. The chars trivial on mu_n
    # are chi_{n*l}, l=0..m-1 in terms of psi(g^a)=exp(2pi i (n a)/(p-1)) basis... 
    # Build tau(psi^j) for the quotient characters.
    ep = np.exp(2j*np.pi/p)
    # additive char e_p, multiplicative chars chi_j(g^a) = exp(2pi i j a /(p-1)) restricted...
    # quotient char that is trivial on mu_n=<g^m>: chi with chi(g^m)=1 => order divides m.
    # psi(g^a) = exp(2 pi i a / m * (a-th... )) Let's define psi(g^a)=exp(2pi i a/(... ))
    # The m characters of Q=F_p^*/mu_n: phi_j(g^a) = exp(2 pi i j a / (p-1) * n)?? 
    # We want phi_j(g^m)=1 => phi_j(g)= exp(2pi i j /m). So phi_j(g^a)=exp(2pi i j a/m).
    # tau(phi_j) = sum_{a=0}^{p-2} phi_j(g^a) e_p(g^a)
    taus = []
    powg = [pow(g, a, p) for a in range(p-1)]
    for j in range(m):
        s = 0.0+0.0j
        for a in range(p-1):
            s += np.exp(2j*np.pi*j*a/m) * ep**(powg[a])
        taus.append(s)
    return taus

# small test
for (p,n) in [(17,4),(41,8),(73,8),(97,16),(193,16)]:
    if not isprime(p): continue
    g,m,mu,eta,ep = setup(p,n)
    taus = gauss_sum_table(p,n,g,m)
    # verify identity eta_k = (1/m)[ -1 + sum_{j=1}^{m-1} psi(g^k)^{-j} tau(psi^j) ]
    # psi^j(g^k) = exp(2pi i j k/m); psi(b)^{-j} = exp(-2pi i j k/m)
    errs=[]
    for k in range(m):
        rhs = -1.0+0j
        for j in range(1,m):
            rhs += np.exp(-2j*np.pi*j*k/m) * taus[j]
        rhs /= m
        errs.append(abs(rhs - eta[k]))
    # also verify S(w)=m eta+1 family
    # S(w_k) = sum_{j=1}^{m-1} w_k^{-j} a_j, a_j=tau_j/sqrt(p), w_k=exp(2pi i k/m)
    sqp=np.sqrt(p)
    Svals=[]
    for k in range(m):
        S = sum(np.exp(-2j*np.pi*j*k/m)*taus[j]/sqp for j in range(1,m))
        Svals.append(S)
    # claim S(w_k)/?  vs m*eta_k+1 : note a_j=tau/sqrt p so S = (m eta_k +1)/sqrt p
    fam_err = max(abs(Svals[k]*sqp - (m*eta[k]+1)) for k in range(m))
    print(f"p={p} n={n} m={m}: identity_err={max(errs):.2e} family(S*sqrt p = m eta+1)_err={fam_err:.2e} |tau|/sqrt p ={abs(taus[1])/sqp:.4f}")

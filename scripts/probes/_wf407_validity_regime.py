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
    return out,m
def primes_1modN(n, start):
    cand=start|1
    while True:
        if (cand-1)%n==0 and sympy.isprime(cand): return cand
        cand+=2
def dfact(k):
    r=1
    for j in range(1,k+1,2): r*=j
    return r

# The OLD deep-wall claim: E_r at char-0 value (2r-1)!! n^r valid only for p > n^{(r+3)/2}, i.e.
#   r <= r_max = 2 log_n p - 3.  In prize regime p~n^5 => r_max=7, optimum needs r~log m. Wall.
# NEW fixed-index spec: m fixed (~2^128), p~n*m, so log_n p = 1 + log_n m -> 1 as n->inf.
#   THEN r_max = 2 log_n p - 3 = 2(1+log_n m) - 3 = 2 log_n m - 1.  With m=2^128: log_n m=128/log2 n.
# Question: at what r does E_r DEVIATE from (2r-1)!! n^r in the fixed-index regime?
print("=== Where does E_r=V_{2r}/m deviate from Gaussian (2r-1)!! n^r?  fixed-index (m~const) ===")
print("    r_max(old) = 2 log_n p - 3.   r_opt ~ log m needed.")
for n in (16,32,64):
    for mtarget in (64, 256, 1024):
        # find p with m ~ mtarget
        p=primes_1modN(n, n*mtarget)
        m=(p-1)//n
        if m < mtarget//2 or m>mtarget*3: 
            p=primes_1modN(n, n*mtarget); m=(p-1)//n
        per,m=periods(p,n)
        absv=[abs(z) for z in per]
        logn_p=math.log(p)/math.log(n)
        rmax_old=2*logn_p-3
        ropt=math.log(m)  # ln m
        # find smallest r where E_r/gauss < 0.5
        rdev=None
        line=[]
        for r in range(2,11):
            Er=sum(a**(2*r) for a in absv)/m
            ratio=Er/(dfact(2*r-1)*n**r)
            line.append(f"r{r}:{ratio:.2f}")
            if rdev is None and ratio<0.5: rdev=r
        print(f"n={n:3d} m={m:5d} p={p:8d}: log_n p={logn_p:.2f} r_max(old)={rmax_old:.1f} r_opt~lnm={ropt:.1f}  ratios[{' '.join(line)}]")

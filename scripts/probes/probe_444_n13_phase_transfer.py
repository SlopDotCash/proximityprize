import cmath, math
from sympy import isprime, primitive_root
N=128
# moderate-index prime: p ~ N^2.5 so m=(p-1)/N is ~1400 (scannable), all mu_8..mu_128 in F_p
t=int(N**2.5); p=t-(t%N)+1
while not(p>N and isprime(p) and (p-1)%N==0 and (p-1)//N>=2): p+=N
g=primitive_root(p); w=2*math.pi/p; m=(p-1)//N
def mu(n):
    z=pow(g,(p-1)//n,p); e=[]; x=1
    for _ in range(n): e.append(x); x=x*z%p
    return e
def eta(b,muset):
    s=0j
    for xx in muset: s+=cmath.exp(1j*w*((b*xx)%p))
    return s
reps=[]; b=1
for _ in range(m): reps.append(b); b=b*g%p
print(f"p={p} (1 mod {N}, beta~2.5), m={m} cosets")
levels=[8,16,32,64,128]; musets={n:mu(n) for n in levels}; Ms={}; worst={}
for n in levels:
    vals={b:abs(eta(b,musets[n])) for b in reps}
    bw=max(vals,key=lambda b:vals[b]); Ms[n]=vals[bw]; worst[n]=bw
    print(f"  n={n:4d}: M={Ms[n]:8.3f}  M/sqrt(n)={Ms[n]/math.sqrt(n):.3f}")
print("  --- transfer at worst-b of level 2n: cos<0 => phase cancellation; ratio<2 => Ramanujan-side ---")
for i in range(1,len(levels)):
    n=levels[i-1]; n2=levels[i]; bw=worst[n2]; z2=pow(g,(p-1)//n2,p)
    e1=eta(bw,musets[n]); e2=eta((bw*z2)%p,musets[n])
    cos=(e1.real*e2.real+e1.imag*e2.imag)/(abs(e1)*abs(e2)+1e-12)
    r2=(Ms[n2]**2)/(Ms[n]**2)
    print(f"  {n:3d}->{n2:3d}: |e_b|={abs(e1):7.3f} |e_zb|={abs(e2):7.3f} cos={cos:+.3f} ratio M(2n)^2/M(n)^2={r2:.3f} {'RAMANUJAN-side(<2)' if r2<2 else 'no sqrt2 gain (>=2)'}")

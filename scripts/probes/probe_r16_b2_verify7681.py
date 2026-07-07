import numpy as np, math
p,n,deg=7681,64,8
def factor(x):
    fs,d=set(),2
    while d*d<=x:
        while x%d==0: fs.add(d); x//=d
        d+=1
    if x>1: fs.add(x)
    return fs
g=next(g for g in range(2,p) if all(pow(g,(p-1)//q,p)!=1 for q in factor(p-1)))
gm=pow(g,(p-1)//n,p); mun=[]; x=1
for _ in range(n): mun.append(x); x=x*gm%p
gd=pow(g,deg,p); Hs=[]; x=1
for _ in range((p-1)//deg): Hs.append(x); x=x*gd%p
H=np.array(Hs,dtype=np.int64)
th=np.longdouble(2*np.pi)/np.longdouble(p)
# eta_b for b in H: sum over y in mun of exp(-i b y th) -- float128 direct
bH=H.reshape(-1,1); Y=np.array(mun,dtype=np.int64).reshape(1,-1)
ang=np.mod(bH*Y,p).astype(np.longdouble)*th
etaH_re=np.cos(ang).sum(axis=1); etaH_im=(-np.sin(ang)).sum(axis=1)
Sig=float((etaH_re**2+etaH_im**2).sum())
# I(s0) = sum_b conj(eta_b) exp(-i b s0 th)  [match ifft convention: ifft gives sum f(b) e^{+2pi i b s/p}/p *p -> e^{+...}]
# convention check: probe used I=ifft(w)*p => I(s)=sum_b w_b e^{2pi i b s/p}, w_b=conj(eta_b), eta=ifft(ind)*p => eta_b=sum_y e^{2pi i b y/p}
# so recompute with +: eta_b=sum_y e^{+i b y th}; I(s0)=sum_b conj(eta_b) e^{+i b s0 th}
etaH_im=(np.sin(ang)).sum(axis=1)
S2p=np.longdouble(0); S3p=np.longdouble(0)
munset=set(mun)
BLK=64
allS=np.arange(p,dtype=np.int64)
mask=np.ones(p,bool); mask[0]=False
for y in mun: mask[y]=False
Ssel=allS[mask]
for i in range(0,len(Ssel),BLK):
    blk=Ssel[i:i+BLK].reshape(-1,1)
    ang2=np.mod(blk*H.reshape(1,-1),p).astype(np.longdouble)*th
    re=(np.cos(ang2)*etaH_re+np.sin(ang2)*etaH_im).sum(axis=1)
    im=(np.sin(ang2)*etaH_re-np.cos(ang2)*etaH_im).sum(axis=1)
    m2=re**2+im**2
    S2p+=(m2**2).sum(); S3p+=(m2**3).sum()
wick2=np.longdouble(3)*p*np.longdouble(Sig)**2
wick3=np.longdouble(15)*p*np.longdouble(Sig)**3
print("Sig=",Sig)
print("S2'/Wick2 =", float(S2p/wick2))
print("S3'/Wick3 =", float(S3p/wick3))

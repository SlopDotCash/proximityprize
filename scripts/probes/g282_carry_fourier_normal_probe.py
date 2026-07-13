#!/usr/bin/env python3
"""Exact carry-Fourier probe for the #466 weighted relation census.

Uses G278's exact integer-lift carry census.  For each genuine dyadic-subgroup cell,
compute predeclared arithmetic normals of the symmetric carry histogram:
  T2 = sum (-1)^k J_k,
  T3 = sum 2*cos(2*pi*k/3) J_k,
  T4 = sum cos(pi*k/2) J_k,
  T6 = sum 2*cos(pi*k/3) J_k.
All weights are integers. No FFT/floating point enters a sign decision. The complete finite
scan through conductor 128 is extended to all conductors by a support/totient inequality.
"""
from __future__ import annotations
import importlib.util
from pathlib import Path
from math import gcd

G278 = Path(__file__).with_name('g278_integer_lift_carry_exact.py')
spec = importlib.util.spec_from_file_location('g278', G278)
g278 = importlib.util.module_from_spec(spec); spec.loader.exec_module(g278)

def isprime(p):
    if p < 2: return False
    d=2
    while d*d<=p:
        if p%d==0: return False
        d += 1 if d==2 else 2
    return True

def sgn(x): return (x>0)-(x<0)

def mobius(n):
    out=1; d=2
    while d*d<=n:
        if n%d==0:
            n//=d; out=-out
            if n%d==0: return 0
            while n%d==0: n//=d
        d+=1
    return -out if n>1 else out

def phi(n):
    out=n; d=2
    while d*d<=n:
        if n%d==0:
            out-=out//d
            while n%d==0: n//=d
        d+=1
    return out-out//n if n>1 else out

def ramanujan(d,k):
    """Exact integer c_d(k)=sum_{a mod d,(a,d)=1} exp(2*pi*i*a*k/d)."""
    q=d//gcd(d,abs(k))
    return mobius(q)*(phi(d)//phi(q))

def normals(c):
    # Integer representatives of real characters on carry modulo d.
    w3=(2,-1,-1)
    w4=(1,0,-1,0)
    w6=(2,1,-1,-2,-1,1)
    return {
      'T2': sum((1 if k%2==0 else -1)*v for k,v in c.items()),
      'T3': sum(w3[k%3]*v for k,v in c.items()),
      'T4': sum(w4[k%4]*v for k,v in c.items()),
      'T6': sum(w6[k%6]*v for k,v in c.items()),
    }

def main():
    cells=[]
    # Complete n=16 census in the same p-window as G266/G270, both live ranks.
    for p in range(17,2601):
        if (p-1)%16==0 and isprime(p):
            for r in (5,6): cells.append((p,16,r))
    # Add the exact cross-scale late cells from G268/G278.
    cells += [(3617,32,5),(3617,32,6),(70753,32,5),(70753,32,6)]
    rows=[]
    for p,n,r in cells:
        x=g278.carry_census(p,n,r)
        ts=normals(x['carr'])
        rows.append((p,n,r,x['gate'],ts,x['carr']))
        print(f'n={n} p={p} r={r} A={x["gate"]:+d} '+
              ' '.join(f'{k}={v:+d}' for k,v in ts.items()))
    print('\nSUMMARY')
    summaries={}
    for key in ('T2','T3','T4','T6'):
        nz=[z for z in rows if z[4][key]!=0]
        agree=sum(sgn(z[3])==sgn(z[4][key]) for z in nz)
        combos=sorted(set((sgn(z[3]),sgn(z[4][key])) for z in nz))
        summaries[key]=(agree,len(nz),combos)
        print(f'{key}: agree={agree}/{len(nz)} combos={combos}')
    # T2 fluctuates but is completely decoupled from the gate: all four quadrants occur.
    assert len(summaries['T2'][2])==4
    # The other first real carry characters are strictly positive on this complete window,
    # hence fail on every negative gate and cannot be an odd/sign-carrying normal.
    for key in ('T3','T4','T6'):
        assert all(ts[key]>0 for _,_,_,_,ts,_ in rows)
        assert any(A<0 for _,_,_,A,_,_ in rows)
    # Complete low-conductor sweep plus the all-conductor tail argument. Every histogram is
    # supported on |k|<=6. For d>=129 and nonzero |k|<=6, q=d/gcd(d,k)>=22, so phi(q)>=8.
    # Hence c_d(k)>=-phi(d)/8, c_d(0)=phi(d), and
    #   T_d >= phi(d)/8 * (9*J0-J).
    # The exact census has 9*J0-J>0 in every cell, proving T_d>0 for EVERY d>=129.
    maxcarry=max(abs(k) for *_,c in rows for k in c)
    margins=[]
    for p,n,r,A,ts,c in rows:
        J=sum(c.values()); J0=c.get(0,0)
        margins.append((9*J0-J,n,p,r,J0,J))
    assert maxcarry<=6
    assert min(m[0] for m in margins)>0
    ram_min={}
    for d in range(2,4097):
        vals=[sum(ramanujan(d,k)*v for k,v in c.items()) for *_,c in rows]
        ram_min[d]=min(vals)
    assert ram_min[2]<0
    assert all(ram_min[d]>0 for d in range(3,4097))
    # Machine-check the coefficient inequality throughout the large exact scan. The unbounded
    # continuation uses the elementary inverse-totient fact phi(q)>=8 for q>=22.
    for d in range(129,4097):
        for k in range(-maxcarry,maxcarry+1):
            if k:
                q=d//gcd(d,abs(k))
                assert q>=22 and phi(q)>=8
                assert ramanujan(d,k)*8>=-phi(d)
    mmin=min(margins)
    print(f'Ramanujan d=3..128 exact-positive; d>=129 positive by support/totient bound; '
          f'scan through 4096 PASS; max|k|={maxcarry}; min(9J0-J)={mmin[0]} '
          f'at n={mmin[1]} p={mmin[2]} r={mmin[3]}')
    # Hard exact witness values encoded by the companion Lean certificate.
    bykey={(n,p,r):(A,ts) for p,n,r,A,ts,_ in rows}
    assert bykey[(16,193,5)][0]==3843136 and bykey[(16,193,5)][1]['T2']==-163896
    assert bykey[(16,257,5)][0]==-1051408 and bykey[(16,257,5)][1]['T2']==-88764
    assert bykey[(16,433,5)][0]==3425440 and bykey[(16,433,5)][1]['T2']==474180
    assert bykey[(16,1553,5)][0]==-16213712 and bykey[(16,1553,5)][1]=={
        'T2':383316,'T3':809194,'T4':516342,'T6':1581282}
    # Symmetry is exact, hence every odd carry moment through degree 9 vanishes.
    for _,_,_,_,_,c in rows:
        for j in (1,3,5,7,9):
            assert sum((k**j)*v for k,v in c.items())==0
    print(f'G282 EXACT PASS: {len(rows)} cells; T2 realizes all four gate/sign quadrants; '
          'every Ramanujan carry normal d>=3 stays positive across both gate signs; '
          'odd moments 1..9 vanish.')

if __name__=='__main__': main()

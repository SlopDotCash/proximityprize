#!/usr/bin/env python3
"""Independently verify the retained five-clique finite certificate."""
import json,itertools,math
from pathlib import Path
d=json.loads(Path(__file__).with_name('probe-retention-rate-quarter-witnesses-2026-09-06.json').read_text())['five_clique'];p=d['field'];assert all(p%i for i in range(2,math.isqrt(p)+1))
c=d['nonpencil_certificate'];polys=c['polynomial_coefficients'];u=c['received_u0'];v=c['received_u1'];gs=d['labels'];n=d['n'];k=d['k'];assert len(set(gs))==5 and len({tuple(a) for a in polys})==5 and all(len(a)==k for a in polys)
def val(a,x):return sum(t*pow(x,j,p) for j,t in enumerate(a))%p
def rank(mat):
 a=[row[:] for row in mat];r=0
 for j in range(len(a[0])):
  pivot=next((i for i in range(r,len(a)) if a[i][j]%p),None)
  if pivot is None:continue
  a[r],a[pivot]=a[pivot],a[r];z=pow(a[r][j]%p,-1,p);a[r]=[x*z%p for x in a[r]]
  for i in range(r+1,len(a)):
   t=a[i][j]%p;a[i]=[(x-t*y)%p for x,y in zip(a[i],a[r])]
  r+=1
  if r==len(a):break
 return r
supports=[{i for i in range(n) if val(a,i+1)==(u[i]+g*v[i])%p} for g,a in zip(gs,polys)]
assert min(map(len,supports))>=d['agreement_threshold']
assert min(len(supports[i]&supports[j]) for i,j in itertools.combinations(range(5),2))>=k
row_ranks=[]
for support in supports:
 indices=sorted(support);V=[[pow(i+1,j,p) for j in range(k)] for i in indices];rv=rank(V);rr=[rank([row+[w[i]] for row,i in zip(V,indices)]) for w in [u,v]];assert max(rr)>rv;row_ranks.append(rr)
col=[]
for i,j,l in itertools.combinations(range(5),3):
 if all(((polys[j][h]-polys[i][h])*(gs[l]-gs[i])-(polys[l][h]-polys[i][h])*(gs[j]-gs[i]))%p==0 for h in range(k)):col.append([i,j,l])
assert len(col)<10 and col==d['nonpencil_realized']['collinear_triples']
out={'prime_checked_by_trial_division':p,'agreement_sizes':list(map(len,supports)),'minimum_actual_pair_overlap':min(len(supports[i]&supports[j]) for i,j in itertools.combinations(range(5),2)),'augmented_row_ranks':row_ranks,'collinear_triples':col,'not_all_five_collinear':True,'scope':'Independent exact certificate check; finite arbitrary 32-point domain, not the smooth production domain. No absence claim follows from failed general-position sampling.'}
print(json.dumps(out, indent=2))

"""Compressed exact production incidence design using coordinate-sized groups.
Author: Mikhail Izhutkin (@mashingaan)
Exact arithmetic plus algebraic certificate, not a kernel-checked theorem.
"""
from fractions import Fraction
import json

N = 2**30
Q = 2**128
FIELDS = [N*(Q+192)+1, N*(2*Q+13)+1]
GENERATORS = [303645430271030343624574566109998498685964493478,
              192152681249815148642741928588691886362054863855]

def certificate(p,s):
    generator=GENERATORS[FIELDS.index(p)]
    assert pow(generator,N,p)==1
    assert pow(generator,N//2,p)!=1
    common=N//2-2
    group=(N-common)//s
    leftover=N-common-s*group
    core=common+group
    count=s*(N-core)
    assert common+1<N//2<=core
    assert 0<=leftover<s
    assert count*Q>p
    powers={a:pow(a,N,p) for a in range(1,2*s)}
    assert len(set(powers.values()))==len(powers)
    for a,value in powers.items():
        independent=a%p
        for _ in range(30):
            independent=independent*independent%p
        assert independent==value
    for j in range(s):
        for h in range(s+1):
            if h!=j:
                assert Fraction(h*h-j*j,h-j)==h+j
                assert 1<=h+j<2*s
    return dict(field=p,generator=generator,s=s,common=common,group=group,leftover=leftover,
                dimension=N//2,max_head_degree=common+1,
                core_size=core,support_size=core+1,
                radius=str(Fraction(N-core-1,N)),
                bad_count_lower_bound=count,budget=p//Q,
                budget_excess=count-p//Q,
                cross_multiplied_error_excess=count*Q-p,
                coefficient_order_residues=powers)

def finite(s):
    n,k,p,g=128,64,1409,1022
    common=k-2
    group=(n-common)//s
    core_size=common+group
    points=[pow(g,i,p) for i in range(n)]
    assert len(set(points))==n and pow(g,n,p)==1
    def height(i):
        if i<common:
            return s
        return min((i-common)//group,s)
    def z(x):
        result=1
        for i in range(common):
            result=result*(x-points[i])%p
        return result
    zs=[z(x) for x in points]
    hs=[height(i) for i in range(n)]
    row1=[hs[i]*zs[i]%p for i in range(n)]
    row0=[hs[i]**2*zs[i]*points[i]%p for i in range(n)]
    seen=set()
    for j in range(s):
        core=list(range(common))+list(range(common+j*group,common+(j+1)*group))
        assert len(core)==core_size>=k
        basis=core[:k]
        weights=[]
        for i in basis:
            den=1
            for other in basis:
                if other!=i:
                    den=den*(points[i]-points[other])%p
            weights.append(row1[i]*pow(den,-1,p)%p)
        def interpolate(x):
            value=0
            for i,weight in zip(basis,weights):
                num=1
                for other in basis:
                    if other!=i:
                        num=num*(x-points[other])%p
                value=(value+num*weight)%p
            return value
        decoded=[interpolate(x) for x in points]
        assert decoded==[j*v%p for v in zs]
        for i in range(n):
            if i in core:
                continue
            gamma=-(hs[i]+j)*points[i]%p
            assert decoded[i]!=row1[i]
            exact_support=[a for a in range(n)
                           if (j*j*zs[a]*points[a]+gamma*j*zs[a])%p
                           ==(row0[a]+gamma*row1[a])%p]
            assert set(exact_support)==set(core+[i])
            for a in core+[i]:
                assert (j*j*zs[a]*points[a]+gamma*j*zs[a])%p==(row0[a]+gamma*row1[a])%p
            assert gamma not in seen
            seen.add(gamma)
    assert len(seen)==s*(n-core_size)
    return dict(n=n,prime=p,generator=g,s=s,common=common,group=group,
                support=core_size+1,bad_scalars=len(seen),radius=str(Fraction(n-core_size-1,n)))

if __name__=='__main__':
    results=[certificate(FIELDS[0],3),certificate(FIELDS[1],5)]
    for result in results:
        multiplier=result['budget']//N
        minimum_heads=2*multiplier+1
        assert result['s']==minimum_heads
        assert (minimum_heads-1)*(N-N//2)<=result['budget']
        # At maximal allowed common degree, more heads only shrink each core.
        for heads in range(minimum_heads,65):
            candidate_core=N//2-2+(N-(N//2-2))//heads
            assert candidate_core<=result['core_size']
    assert results[0]['budget_excess']==5
    assert results[1]['budget_excess']==12
    print(json.dumps(dict(production=results,finite=[finite(3),finite(5)]),indent=2))

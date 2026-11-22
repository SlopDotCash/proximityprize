#!/usr/bin/env python3
"""Solve the twelve signed terms of the three-pair determinant on all dyadic roots."""
from collections import Counter
from itertools import combinations, permutations, product

def matchings(ids):
    if not ids:
        yield ()
        return
    a = ids[0]
    for k in range(1, len(ids)):
        for tail in matchings(ids[1:k] + ids[k+1:]):
            yield ((a,ids[k]),) + tail

def terms():
    # det of the three rows (1, X_i+Y_i, X_i*Y_i).
    result = []
    for ijk in permutations(range(3)):
        _, j, k = ijk
        sign = sum(a>b for a,b in combinations(ijk,2)) % 2
        for slot in (2*j, 2*j+1):
            exponents = [int(t in (slot,2*k,2*k+1)) for t in range(1,6)]
            result.append((exponents,sign))
    return result

def determinant(matrix):
    """Fraction-free elimination for the independent unimodularity check."""
    data = [row[:] for row in matrix]
    sign, previous = 1, 1
    for k in range(len(data)-1):
        pivot = next((j for j in range(k,len(data)) if data[j][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            data[k],data[pivot] = data[pivot],data[k]
            sign = -sign
        for i in range(k+1,len(data)):
            for j in range(k+1,len(data)):
                numerator = data[k][k]*data[i][j] - data[i][k]*data[k][j]
                quotient, remainder = divmod(numerator, previous)
                assert remainder == 0
                data[i][j] = quotient
        previous = data[k][k]
    return sign*data[-1][-1]


def diagonal(rows):
    # The last column records the right-hand side in half-turns.
    A = [r[:] for r in rows]
    E = [[int(i==j) for j in range(5)] for i in range(5)]
    U = [[int(i==j) for j in range(len(A))] for i in range(len(A))]
    rank = 0
    while rank < 5:
        r = rank
        pivot = min(((abs(A[i][j]),i,j) for i in range(r,len(A)) for j in range(r,5) if A[i][j]),default=None)
        if pivot is None:
            break
        _, i,j = pivot
        A[r],A[i] = A[i],A[r]
        U[r],U[i] = U[i],U[r]
        for row in A+E:
            row[j],row[r] = row[r],row[j]
        while True:
            i=next((i for i in range(r+1,len(A)) if A[i][r]),None)
            if i is not None:
                q=A[i][r]//A[r][r]
                A[i]=[a-q*b for a,b in zip(A[i],A[r])]
                U[i]=[a-q*b for a,b in zip(U[i],U[r])]
                if A[i][r]:
                    A[i],A[r]=A[r],A[i]
                    U[i],U[r]=U[r],U[i]
                continue
            j=next((j for j in range(r+1,5) if A[r][j]),None)
            if j is not None:
                q=A[r][j]//A[r][r]
                for row in A+E:
                    row[j]-=q*row[r]
                if A[r][j]:
                    for row in A+E:
                        row[j],row[r]=row[r],row[j]
                continue
            break
        rank += 1
    assert abs(determinant(E)) == abs(determinant(U)) == 1
    left = [[sum(u*v for u,v in zip(row,col)) for col in zip(*rows)] for row in U]
    for i,row in enumerate(left):
        for j,col in enumerate(zip(*E)):
            assert sum(u*v for u,v in zip(row,col)) == A[i][j]
            if i != j or i >= rank:
                assert A[i][j] == 0
        assert row[-1] == A[i][-1]
    if any(row[-1]%2 for row in A[rank:]):
        return
    factors=[abs(A[i][i]) & -abs(A[i][i]) for i in range(rank)]
    modulus=2*max([1]+factors)
    for t in product(*(range(v) for v in factors)):
        const=[((A[i][-1]%2+2*t[i])*(modulus//(2*factors[i]))) for i in range(rank)]
        X=[(0,)*(6-rank)]
        for row in E:
            X.append((sum(a*b for a,b in zip(row,const))%modulus,*row[rank:]))
        yield modulus,X

def classify(M,X):
    def zero(assignments,half=0):
        v=[sum(k*X[i][u] for i,k in assignments) for u in range(len(X[0]))]
        return (v[0]+half*(M//2))%M==0 and not any(v[1:])
    if len(set(X))<6:
        return 'repeated site'
    if all(zero([(0,1),(1,1),(i,-1),(i+1,-1)]) for i in (2,4)):
        return 'reciprocal'
    if all(zero([(i,1),(i+1,-1)],1) for i in (0,2,4)):
        return 'negation'
    for e,f,g in [(0,2,4),(2,0,4),(4,0,2)]:
        if zero([(e,1),(e+1,-1)],1):
            for j in [0,1]:
                if zero([(e,2),(f,-1),(g+j,-1)]) and zero([(e,2),(f+1,-1),(g+1-j,-1)]):
                    return 'antipodal reflection'
    for es in permutations((0,2,4)):
        for u,v,w in product([0,1],repeat=3):
            a,b=es[0]+u,es[0]+1-u
            c,d=es[1]+v,es[1]+1-v
            e,f=es[2]+w,es[2]+1-w
            if (zero([(d,1),(c,2),(b,-1),(a,-2)]) and zero([(e,1),(b,1),(c,-2)])
                and zero([(f,1),(b,-1),(c,1),(a,-1)],1)):
                return 'quadratic'
    return 'other'

def main():
    T=terms(); count=Counter(); pattern=Counter(); ex={}
    for pairs in matchings(tuple(range(12))):
        rows=[[a-b for a,b in zip(T[i][0],T[j][0])]+[int(T[i][1]==T[j][1])] for i,j in pairs]
        seen=set()
        for modulus, X in diagonal(rows):
            shape=classify(modulus,X); seen.add(shape); count[(shape, len(X[0])-1)]+=1
            if shape=='other':ex.setdefault(len(X[0])-1,(pairs,modulus,X))
        pattern[tuple(sorted(seen))]+=1
    assert sum(pattern.values()) == 10395
    assert not ex, ex
    print(f"All {sum(pattern.values()):,} determinant matchings classified.")
    for shape in sorted({shape for shape,_ in count}):
        total = sum(v for (kind,_),v in count.items() if kind==shape)
        print(f"{shape}: {total:,} components")

if __name__=='__main__':
    main()

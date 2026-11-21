#!/usr/bin/env python3
"""Test the integral cubic's fibers, simultaneous rows and literal four-head witnesses."""

from math import prod
from random import Random

from probe_many_head_locator_attack import at_point, require


PRIME = 730750818665451459101842416358141509841924915201
GENERATOR = 192152681249815148642741928588691886362054863855
FIBERS = ((0, 1, 8), (2, 9, 10), (3, 5, 7))


def parameters(n, k):
    d = 3*k//4
    g = k-2-d
    fixed = k-2
    core = min((n+2*g+3*d+fixed)//4, (2*n+6*d+3*g-1)//7)
    private = core-g-2*d
    fourth = core-fixed
    union = g+3*d+3*private
    holes = n-union-fourth
    labels = union-g+union-fixed+3*fourth+4*holes
    require(min(g, private, fourth, holes) >= 0 and fixed <= union and core >= k, "packing")
    require(labels == 4*n-7*core+6*d+3*g and labels > 2*n, "budget")
    return d, g, fixed, core, private, fourth, union, holes, labels


def cubic(p, w):
    require(pow(w, 8, p) == p-1, "order sixteen")
    a, b, c = [[pow(w, j, p) for j in row] for row in FIBERS]
    def locator(roots, x):
        return prod(x-y for y in roots) % p
    scale = locator(a,c[0])*pow(locator(b,c[0]), -1,p) % p
    def values(x):
        return (0, locator(a,x), scale*locator(b,x) % p)
    for row, pair in ((a,(0,1)), (b,(0,2)), (c,(1,2))):
        for x in row:
            v = values(x)
            require(v[pair[0]] == v[pair[1]] and len(set(v)) == 2, "cubic identity")
    return values


def check_small(n, k):
    p = 998244353
    g0 = pow(3, (p-1)//n, p)
    xs = [pow(g0,i,p) for i in range(n)]
    d, common, fixed, core, private, fourth, union, holes, total = parameters(n,k)
    g = cubic(p, pow(g0,n//16,p))
    values = {x: g(pow(x,k//4,p)) for x in xs}
    pairs = {x for x in xs if len(set(values[x])) == 2}
    require(len(pairs) == 3*d, "lifted pair blocks")
    ordinary = [x for x in xs if x not in pairs]
    shared = ordinary[:common]
    fs = {x: [prod(x-y for y in shared)*v % p for v in values[x]] for x in xs}
    owner = {}
    for x in pairs:
        owner[x] = next(i for i,v in enumerate(fs[x]) if fs[x].count(v) == 2)
    for x in shared:
        owner[x] = 0
    tail = ordinary[common:]
    for i in range(3):
        for x in tail[i*private:(i+1)*private]:
            owner[x] = i
    require(len(owner) == union, "covered sites")
    only = tail[3*private:3*private+fourth]
    rest = tail[3*private+fourth:]
    require(len(rest) == holes, "hole count")
    rng = Random(n+k)
    vset = rng.sample(list(owner),fixed)
    cores = [[x for x,i in owner.items() if fs[x][j] == fs[x][i]] for j in range(3)]
    cores.append(vset+only)
    require(all(len(s) == core for s in cores), "core count")
    baseA = [x*fs[x][owner[x]] % p for x in vset]
    baseB = [fs[x][owner[x]] for x in vset]
    aq = {x: at_point(vset,baseA,x,p) for x in xs}
    bq = {x: at_point(vset,baseB,x,p) for x in xs}
    loc = {x: prod(x-z for z in vset) % p for x in xs}
    for _ in range(1000):
        b = rng.randrange(p)
        w = {x:(bq[x]+b*loc[x]) % p for x in xs}
        if all(w[x] not in fs[x] for x in xs if x not in vset):
            break
    else:
        raise ArithmeticError("second row")
    for _ in range(1000):
        a, c = rng.randrange(p), rng.randrange(p)
        u = {x:(aq[x]+loc[x]*(a+c*x)) % p for x in xs}
        labels = {-x % p:(next(j for j in range(3) if fs[x][i]!=fs[x][j]),x)
                  for x,i in owner.items() if x not in shared}
        for x,i in owner.items():
            if x not in vset:
                z = (u[x]-x*fs[x][i])*pow(fs[x][i]-w[x],-1,p) % p
                labels[z] = (3,x)
        for x in only:
            for i in range(3):
                z = (u[x]-x*fs[x][i])*pow(fs[x][i]-w[x],-1,p) % p
                labels[z] = (i,x)
        if len(labels) == total-4*holes:
            break
    else:
        raise ArithmeticError("first-row pencil")
    heads = {x:[(x*f % p,f) for f in fs[x]]+[(u[x],w[x])] for x in xs}
    received = {x:heads[x][i] for x,i in owner.items()}
    received.update((x,heads[x][3]) for x in only)
    for x in rest:
        v = next(z for z in range(p) if all(z != b for _,b in heads[x]))
        for _ in range(1000):
            a = rng.randrange(p)
            new = [(a-u)*pow(w-v,-1,p) % p for u,w in heads[x]]
            if len(set(new)) == 4 and all(z not in labels for z in new):
                received[x] = (a,v)
                labels.update({z:(i,x) for i,z in enumerate(new)})
                break
        else:
            raise ArithmeticError("hole labels")
    require(len(labels) == total, "final label count")
    for z,(i,x) in labels.items():
        for y in cores[i]+[x]:
            u,b = received[y]
            v,c = heads[y][i]
            require((u+z*b-v-z*c) % p == 0, "fold mismatch")
        base = cores[i][:k]
        fit = at_point(base,[received[y][1] for y in base],x,p)
        require(fit != received[x][1], "jointly explained")
    print(f"n={n}, k={k}, e={n-core-1}, all {total} literal labels verified")


def main():
    for n,k in ((64,8),(64,16),(128,32)):
        check_small(n,k)
    n = 2**30
    require(PRIME//2**128 == 2*n and PRIME > (4*n)**2, "field budget")
    require(pow(GENERATOR,n//2,PRIME) == PRIME-1, "production order")
    cubic(PRIME, pow(GENERATOR,n//16,PRIME))
    for denominator, expected, count in ((8,679477249,2239758344),(4,565631854,2147483651)):
        k = n//denominator
        d, g, fixed, core, private, fourth, union, holes, labels = parameters(n,k)
        require((n-core-1,labels) == (expected,count), "production result")
        print(f"production rate 1/{denominator}, e={expected}, labels={labels}, holes={holes}")


if __name__ == "__main__":
    main()

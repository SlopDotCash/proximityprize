#!/usr/bin/env python3
"""Test literal fresh-site witnesses and report the production error ceilings."""

from random import Random


def require(value, message):
    if not value:
        raise ArithmeticError(message)


def ceiling(a, b):
    return -(-a//b)


def at_point(points, values, wanted, p):
    result = 0
    for i, x in enumerate(points):
        term = values[i]
        for j, y in enumerate(points):
            if i != j:
                term = term*(wanted-y)*pow(x-y,-1,p) % p
        result = (result+term) % p
    return result


def verify_model(n, k, heads):
    p = 65537
    rng = Random(k+heads)
    e = ceiling((heads-1)*(n-k)+heads-2,heads)
    t = n-e
    h = max(0,ceiling(heads*(t-1)-n,heads-1))
    common = list(range(h))
    r = t-1-h
    private = [list(range(h+i*r,h+(i+1)*r)) for i in range(heads)]
    extra = list(range(h+heads*r,n))
    locator = []
    for x in range(n):
        product = 1
        for y in common:
            product = product*(x-y) % p
        locator.append(product)
    b = list(range(1,heads+1))
    for trial in range(1000):
        c = [rng.randrange(p) for i in b]
        def head(i,x):
            return (locator[x]*(b[i]*b[i]*x+c[i]) % p,locator[x]*b[i] % p)
        labels = {}
        rows = {x:(0,0) for x in common}
        for j in range(heads):
            for x in private[j]:
                u,v = rows[x] = head(j,x)
                for i in range(heads):
                    if i!=j:
                        A,B = head(i,x)
                        z = (A-u)*pow(v-B,-1,p) % p
                        labels[z]=(i,x)
        if len(labels) == heads*(heads-1)*r:
            break
    else:
        raise ArithmeticError("no private collision-free labels")
    for x in extra:
        v = 0
        for u in range(p):
            new = [(head(i,x)[0]-u)*pow(v-head(i,x)[1],-1,p) % p for i in range(heads)]
            if len(set(new))==heads and not set(new).intersection(labels):
                break
        else:
            raise ArithmeticError("no unused extra labels")
        rows[x]=(u,v)
        labels.update({z:(i,x) for i,z in enumerate(new)})
    require(len(labels)==heads*(e+1), "unexpected distinct-label count")
    for z,(i,x) in labels.items():
        base = common + private[i]
        require(len(base)==t-1 and len(base)>=k, "defining support")
        for y in base+[x]:
            u,v=rows[y]
            A,B=head(i,y)
            require((u+z*v-A-z*B)%p==0, "fold agreement")
        explained = tuple(at_point(base[:k], [rows[y][j] for y in base[:k]], x, p)
                          for j in (0,1))
        require(explained!=rows[x], "the fresh support has a joint explanation")
    print(f"F_{p}, n={n}, k={k}, heads={heads}, e={e}, literal bad labels={len(labels)}")


def main():
    verify_model(16,4,4)
    verify_model(16,8,5)
    n=2**30
    rows=[]
    for den,l in ((2,5),(4,4),(8,4)):
        k=n//den
        e=ceiling((l-1)*(n-k)+l-2,l)
        require(l*(e+1)>2*n and n-e-1>=k, "production cap")
        rows.append((e,l*(e+1)))
    require(rows==[(429496731,2147483660),(603979777,2415919112),(704643073,2818572296)],
            "production arithmetic")
    print("production (first-failure upper bound, exhibited labels):",rows)


if __name__ == "__main__":
    main()

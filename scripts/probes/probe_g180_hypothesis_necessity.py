"""
When does x^n=1, x^2 != 1 (n=2m) imply x^m = -1?
NOT always: need x to have EVEN order that is a multiple giving x^m order 2.
Counterexample search: x with x^n=1, x^2!=1, but x^m != -1.
"""
from sympy import isprime, primitive_root

found_counter = 0
examples_neg1 = 0
for p in [257, 1297, 7681, 65537, 97]:
    if not isprime(p):
        continue
    g = primitive_root(p)
    for n in [8, 16, 32]:
        if (p - 1) % n:
            continue
        m = n // 2
        # iterate over ALL x with x^n=1 (the subgroup of order dividing n), x^2!=1
        # subgroup of n-th roots of unity:
        h = pow(g, (p - 1) // n, p)  # generator of order n
        for j in range(n):
            x = pow(h, j, p)
            if pow(x, n, p) != 1:
                continue
            if pow(x, 2, p) == 1:
                continue
            xm = pow(x, m, p)
            if xm == p - 1:
                examples_neg1 += 1
            else:
                found_counter += 1
                if found_counter <= 8:
                    # what's the actual order of x?
                    o = 1
                    t = x
                    while t != 1:
                        t = (t * x) % p
                        o += 1
                    print(f"COUNTER p={p} n={n} x={x} order={o} x^m={xm} (not -1={p-1})")

print()
print(f"x^m = -1 examples: {examples_neg1}   counterexamples (x^n=1,x^2!=1,x^m!=-1): {found_counter}")
print("=> plain x^n=1 & x^2!=1 does NOT force x^m=-1. Need: x has order EXACTLY n (n even).")

# Now check: order EXACTLY n even => x^m = -1 always?
print("\nCheck: order exactly n (even) => x^m = -1:")
ok = True
for p in [257, 1297, 7681, 65537, 97, 40961]:
    if not isprime(p):
        continue
    g = primitive_root(p)
    for n in [4, 8, 16, 32]:
        if (p - 1) % n:
            continue
        m = n // 2
        x = pow(g, (p - 1) // n, p)  # order exactly n
        # verify order exactly n
        realorder = 1
        t = x
        while t != 1:
            t = (t * x) % p
            realorder += 1
        if realorder != n:
            continue
        xm = pow(x, m, p)
        if xm != p - 1:
            ok = False
            print(f"  FAIL p={p} n={n} order={realorder} x^m={xm}")
print(f"order-exactly-n-even => x^m=-1 : {ok}")

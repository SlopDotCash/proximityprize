from sympy import isprime, primitive_root

def val_min_abs(z, p):
    z %= p
    return z if z <= p // 2 else z - p

cases = []
for p in [257, 1297, 7681, 65537, 40961, 12289]:
    if not isprime(p):
        continue
    g = primitive_root(p)
    for n in [8, 16, 32, 64]:
        if (p - 1) % n:
            continue
        x = pow(g, (p - 1) // n, p)
        if pow(x, n, p) != 1 or pow(x, 2, p) == 1:
            continue
        cases.append((p, x, n))

allpair = True
allexact = True
for (p, x, n) in cases:
    b = 1
    m = [val_min_abs(b * pow(x, k + 1, p) - b * pow(x, k, p), p) for k in range(n)]
    mags = [abs(v) for v in m]
    half = n // 2
    pair_ok = all(mags[k] == mags[k + half] for k in range(half))
    distinct = len(set(mags))
    exact = (distinct == half)
    allpair = allpair and pair_ok
    allexact = allexact and exact
    xhalf = pow(x, half, p)
    isneg1 = (xhalf == p - 1)
    print(f"p={p:>6} n={n:>3} distinct_mags={distinct:>3} (n/2={half:>3}) "
          f"pair_ok={pair_ok} exact={exact} x^(n/2)==-1:{isneg1}")

print()
print(f"ALL antipodal-paired: {allpair}   ALL exactly n/2 distinct: {allexact}")

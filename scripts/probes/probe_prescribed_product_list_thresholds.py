"""Check the two exact grid crossings and reconstruct small common-locator lists."""
from itertools import combinations
from math import comb, gcd, prod

BLS_FR = 52435875175126190479447740508185965837690552500527637822603658699938581184513
BLS_ROOT = 36007022166693598376559747923784822035233416720563672082740011604939309541707


def check(test, detail):
    if not test:
        raise ArithmeticError(detail)


def counts(n, k, t, h, base_size, field_size):
    budget = field_size // 2**128
    keys = h * base_size ** (t-k-1)
    lower = (comb(n, t) + keys - 1) // keys
    upper = comb(n, k) // comb(t+1, k)
    check(upper <= budget < lower, "strict grid crossing")
    # Johnson's agreement count is sqrt(n * (k - 1)).
    check(t*t < n*(k-1) and t > k, "strictly between Johnson and capacity")
    print(f"[{n},{k}] last_good={n-t-1} first_bad={n-t} budget={budget} "
          f"upper={upper} lower={lower}")


def four_rate_windows(p, extension, n, expected):
    """Independently check matching bounds for each of the four rate indices."""
    q = p ** extension
    budget = q // 2**128
    check((p-1) % n == 0 and 2**128 < q < 2**256, "smooth-domain field window")
    first_bad = []
    for denominator in (2,4,8,16):
        k = n // denominator
        for t in (k+1,k,k-1):
            upper = comb(n,k) // comb(t+1,k)
            if t == k+1:
                lower = (comb(n,t) + n-1) // n
            elif t == k:
                lower = comb(n,k)
            else:
                lower = q
            if upper <= budget < lower:
                first_bad.append(n-t)
                break
    check(tuple(first_bad) == expected, "all four rate thresholds")
    print(f"F_({p}^{extension}) n={n} first_bad={first_bad}")


def poly_value(f, x, p):
    answer = 0
    for coefficient in reversed(f):
        answer = (x * answer + coefficient) % p
    return answer


def locator(points, p):
    coefficients = [1]
    for x in points:
        c = [0] * (len(coefficients) + 1)
        for j,v in enumerate(coefficients):
            c[j] = (c[j] - x*v) % p
            c[j+1] = (c[j+1] + v) % p
        coefficients = c
    return coefficients


def reconstruct(p, generator, n, k, t):
    domain = tuple(pow(generator, j, p) for j in range(n))
    check(len(set(domain)) == n and pow(generator, n, p) == 1, "small subgroup")
    groups = {}
    for subset in combinations(domain, t):
        polynomial = locator(subset, p)
        key = (prod(subset) % p, *polynomial[k+1:t])
        groups.setdefault(key, []).append((subset, polynomial))
    family = max(groups.values(), key=len)
    anchor = family[0][1]
    center = [poly_value(anchor, x, p)*pow(x,-1,p) % p for x in domain]
    words = set()
    for subset, polynomial in family:
        numerator = [(u-v) % p for u,v in zip(anchor, polynomial)]
        check(numerator[0] == 0 and not any(numerator[k+1:]), "coefficient cancellations")
        word = tuple(poly_value(numerator[1:], x, p) for x in domain)
        agreements = {x for x,w,c in zip(domain, word, center) if w == c}
        check(agreements == set(subset), "support of explicit candidate")
        words.add(word)
    check(len(words) == len(family), "distinct candidates")
    check(len(words) * n * p ** (t-k-1) >= comb(n,t), "pigeonhole")


if __name__ == "__main__":
    check(pow(BLS_ROOT, 256, BLS_FR) == 1 and pow(BLS_ROOT, 128, BLS_FR) == BLS_FR-1,
          "order-256 BLS root")
    check(pow(9,128,257) == 1 and pow(9,64,257) == 256, "order-128 prime-field root")
    counts(256, 32, 33, 256, BLS_FR, BLS_FR)
    counts(128, 32, 34, 128, 257, 257**27)
    # Lucas: p-1=5*13*2^239, and 3 has exact order p-1 modulo p.
    prime = 65 * 2**239 + 1
    check(pow(3,prime-1,prime) == 1, "Lucas exponent")
    for divisor in (2,5,13):
        check(gcd(pow(3,(prime-1)//divisor,prime)-1,prime) == 1, "Lucas prime divisor")
    four_rate_windows(prime,1,128,(63,97,113,121))
    four_rate_windows(641,26,128,(63,97,113,121))
    four_rate_windows(673,16,32,(15,24,29,31))
    reconstruct(17,3,16,4,5)
    reconstruct(17,3,16,4,6)

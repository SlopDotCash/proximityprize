def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i*i <= n:
        if n % i == 0: return False
        i += 2
    return True

def find_prime(t, n):
    p = t - (t % n) + 1
    while not (p > 2 and is_prime(p) and (p-1) % n == 0):
        p += n
    return p

def subgroup(p, n):
    m = (p-1)//n
    for a in range(2, p):
        h = pow(a, m, p)
        if pow(h, n, p) == 1:
            nn = n; q = 2; primes = set()
            while nn > 1:
                while nn % q == 0:
                    primes.add(q); nn //= q
                q += 1
            if all(pow(h, n//q, p) != 1 for q in primes):
                S = []; v = 1
                for _ in range(n):
                    S.append(v); v = v*h % p
                return p, S
    return None, None

for n in [8, 16, 32, 64]:
    p, S = subgroup(find_prime(int(n**3.2), n), n)
    Sset = set(S)
    neg_in = (p-1) in Sset
    neg_closed = all((p - x) % p in Sset for x in S)
    print(f"n={n} p={p}  -1 in mu_n: {neg_in}   negation-closed: {neg_closed}")

"""Check every finite scalar of an RS(64,32) cubic-locator MCA example over F73."""

P = 73
N, K, E = 64, 32, 15
L = 6


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def evaluate(coeff, x):
    answer = 0
    for a in reversed(coeff):
        answer = (answer * x + a) % P
    return answer


def vanisher(points):
    coeff = [1]
    for x in points:
        new = [0] * (len(coeff) + 1)
        for i, a in enumerate(coeff):
            new[i] = (new[i] - a * x) % P
            new[i + 1] = (new[i + 1] + a) % P
        coeff = new
    return coeff


def rank(matrix):
    matrix = [row.copy() for row in matrix]
    r = 0
    for j in range(len(matrix[0])):
        pivot = next((i for i in range(r, len(matrix)) if matrix[i][j] % P), None)
        if pivot is None:
            continue
        matrix[pivot], matrix[r] = matrix[r], matrix[pivot]
        inverse = pow(matrix[r][j], -1, P)
        for i in range(r + 1, len(matrix)):
            scale = matrix[i][j] * inverse % P
            matrix[i] = [(a - scale * b) % P for a, b in zip(matrix[i], matrix[r])]
        r += 1
    return r


def main():
    g = 5
    require(len({pow(g, i, P) for i in range(72)}) == 72, "generator has incorrect order")
    core = {pow(g, i + 4 * j, P) for i in range(3) for j in range(18)}
    domain = sorted(core | set(sorted(set(range(P)) - core)[:N - len(core)]))
    require(len(core) == 54 and len(domain) == N, "incorrect core or domain size")
    V = vanisher(domain)
    row0, row1 = V[E:], [(-a) % P for a in V[E + 3:]]
    require(K <= len(row1) - 1 < N - E, "incorrect second-row degree")
    inverse_derivatives = {
        x: pow(evaluate([(i * a) % P for i, a in enumerate(V)][1:], x), -1, P)
        for x in domain
    }

    checked = []
    for t in range(P):
        m = [(int(j == E - 1) - t * int(j == E + 2)) % P for j in range(N - K)]
        mixture = {x: (evaluate(row0, x) + t * evaluate(row1, x)) % P for x in domain}
        measured = [sum(mixture[x] * inverse_derivatives[x] * pow(x, j, P)
                        for x in domain) % P for j in range(N - K)]
        require(m == measured, "Hankel moments disagree with measured syndromes")
        hankel = [m[j:j + E + 1] for j in range(N - K - E)]
        locator = [pow(t, L - 1 - j // 3, P) if j % 3 == 0 else 0 for j in range(E + 1)]
        require(all(sum(a * b for a, b in zip(row, locator)) % P == 0 for row in hankel),
                "locator outside the Hankel kernel")
        require(rank(hankel) == E, "unexpected Hankel rank")
        roots = {x for x in domain if not evaluate(locator, x)}
        if len(roots) != E:
            # Unique degree-E apolar locator; fewer than E errors would give
            # at least two degree-at-most-E kernel polynomials.
            continue
        Q = vanisher(x for x in domain if x not in roots)
        witness = [(-pow(t, L, P) * a) % P for a in Q[E + 3:]]
        require(len(witness) <= K, "witness exceeds the code degree bound")
        require({x for x in domain if evaluate(witness, x) != mixture[x]} == roots,
                "witness error sites disagree with locator roots")
        checked.append(t)

    expected = sorted({pow(x, 3, P) for x in core})
    require(checked == expected and len(checked) == E + 3, "incorrect bad-scalar census")
    print(f"p={P} n={N} k={K} e={E} all {P} scalar decisions checked; "
          f"bad={len(checked)} scalars={checked}")


if __name__ == "__main__":
    main()

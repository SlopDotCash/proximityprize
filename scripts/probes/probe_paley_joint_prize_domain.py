"""Exact classical Paley graph on the smooth domain of FourRateListPrime246.

Run with Python 3. All checks use integers and stay active under python -O.
"""

from math import gcd


P = 65 * 2**239 + 1
G = 17853208868485432014317288845792547206997403552813598151082541291610392869
N = 128


def require(condition, description):
    if not condition:
        raise ArithmeticError(description)


def character(x):
    residue = pow(x % P, (P - 1) // 2, P)
    return -1 if residue == P - 1 else residue


def signed_row():
    # Lucas's primality criterion. The known prime factors exhaust P - 1.
    require(P - 1 == 2**239 * 5 * 13, "factorization")
    require(pow(3, P - 1, P) == 1, "Lucas power")
    for prime in (2, 5, 13):
        require(gcd(pow(3, (P - 1) // prime, P) - 1, P) == 1, "Lucas order")
    require(pow(G, N, P) == 1 and pow(G, N // 2, P) != 1, "generator order")
    require(character(G) == 1 and character(-1) == 1, "square symmetries")
    row = [character(1 - pow(G, j, P)) for j in range(N)]
    require(row[0] == 0 and row.count(1) == 67 and row.count(-1) == 60, "degree")
    require(all(row[j] == row[-j % N] for j in range(N)), "symmetry")
    return row


def verify_spectral_bound(row):
    # If row represents K, cyclic convolution with itself represents K squared.
    # All eigenvalues are real. The trace of K^512 bounds each |lambda|^512.
    power_row = row
    for _ in range(9):
        power_row = [
            sum(power_row[i] * power_row[(j - i) % N] for i in range(N))
            for j in range(N)
        ]
    trace = N * power_row[0]
    require(0 < trace < 30**512, "trace certificate for norm < 30")


def cliques_through_one(row, sign):
    """Count every clique containing the group identity, by cardinality."""
    neighbors = [
        sum(1 << j for j in range(N) if row[(j - i) % N] == sign)
        for i in range(N)
    ]
    counts = [0] * (N + 1)

    def extend(size, candidates):
        counts[size] += 1
        while candidates:
            vertex = candidates & -candidates
            candidates ^= vertex
            index = vertex.bit_length() - 1
            extend(size + 1, candidates & neighbors[index])

    extend(1, neighbors[0])
    return {size: count for size, count in enumerate(counts) if count}


def main():
    row = signed_row()
    verify_spectral_bound(row)
    print(f"degree 67, signed row sum {sum(row)}, double sum {N * sum(row)}")
    print("signed adjacency spectral norm < 30 (exact 512th trace comparison)")
    for sign, size, total in [(1, 10, 2048), (-1, 8, 512)]:
        counts = cliques_through_one(row, sign)
        require(max(counts) == size, "maximum homogeneous set size")
        # Multiplication by G acts transitively. Count vertex/set incidences.
        require(counts[size] * N == total * size, "number of maximum sets")
        print(f"sign {sign:+d}: maximum size {size}, attained by {total} sets")


if __name__ == "__main__":
    main()

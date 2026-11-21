# What pairwise shift intersections can certify about Paley lists

At the prime $p=2^{61}-1$, two common symbol lists of size $(p-1)/2$ have identical pairwise shift intersections. For one list, a set of $2^{30}-1$ coordinates admits exactly $2^{31}-1$ shifts with **perfect agreement**. For the list of genuine nonzero quadratic residues, every coordinate set of that size admits at most $2^{30}+1$ such shifts. The evaluation points, the prime alphabet and the affine Reed–Solomon words $a\mapsto a+b$ are the same in both comparisons. Only the accepted symbols change.

## A cyclic design and its complete shift lists

Identify the additive group of $\mathbb F_p$ with exponents modulo $p$. In the auxiliary field $K=\mathbb F_{2^{61}}$, choose a generator $g$ of $K^\times$ and define
$$
 D=\{i\in\mathbb F_p:\operatorname{Tr}_{K/\mathbb F_2}(g^i)=0\}.
$$
This is the binary Singer difference set. Its trace pairing $\langle u,v\rangle=\operatorname{Tr}(uv)$ is nondegenerate. Indeed, for $u\ne0$, pairing with $u^{-1}$ gives $\operatorname{Tr}(1)=1$, since 61 is odd. For any coordinate set $T\subseteq\mathbb F_p$, let $r(T)$ denote the binary dimension of the span of $\{g^a:a\in T\}$. A shift $b$ satisfies $a+b\in D$ for every $a\in T$ precisely when $g^b$ belongs to the orthogonal complement of this span. Deleting its zero vector gives the exact multishift count
$$
 \left|\bigcap_{a\in T}(D-a)\right|=2^{61-r(T)}-1.
$$
A singleton has rank 1, and any two distinct coordinates have rank 2 because the only nonzero binary scalar is 1. Consequently $k=|D|=2^{60}-1=(p-1)/2$ and $\lambda=|D\cap(D+h)|=2^{59}-1=(p-3)/4$ for every nonzero $h$. [Singer and Paley difference sets, §§4.1–4.2](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v20i1p38/pdf/)

Choose a 30-dimensional binary subspace $U\le K$. Write $A=\log_g(U\setminus\{0\})$ and $B=\log_g(U^\perp\setminus\{0\})$. Then $|A|=2^{30}-1$, $|B|=2^{31}-1$, and $A+B\subset D$. In fact the complete signed agreement distribution for $s_D=2\mathbf1_D-1$ is
$$
 \sum_{a\in A}s_D(a+b)=
 \begin{cases}|A|& b\in B,\\-1& b\notin B.\end{cases}
$$
For $b\notin B$, the corresponding functional is nonzero on $U$. It takes each binary value equally often on $U$, and deleting zero removes one trace-zero value. Thus every threshold from zero through $|A|-1$ has exactly $|B|$ strictly exceptional positive shifts.

## The genuine quadratic list at the same prime

Let $Q\subset\mathbb F_p$ be the nonzero squares and let $\chi(0)=0$. The indicator is $2\mathbf1_Q(x)=1+\chi(x)-\mathbf1_{x=0}$. For $h\ne0$, $\sum_x\chi(x)\chi(x+h)=-1$. The substitution $x\mapsto x/(x+h)$ sends the points other than $-h$ bijectively to the field minus 1 and proves the identity. Expanding the indicators gives
$$
 4|Q\cap(Q+h)|=p-3-\chi(h)-\chi(-h)=p-3
$$
because $p\equiv3\pmod4$. Thus $Q$ and $D$ have the same $k$ and $\lambda$.

For nonempty $A'\subset\mathbb F_p$, let $B_Q(A')=\{b:A'+b\subseteq Q\}$. Hanson and Petridis proved that if $X+Y\subseteq Q\cup\{0\}$, then $|X||Y|\le (p-1)/2+|Y\cap(-X)|$. Apply this with $X=A'$, $Y=B_Q(A')$. The perfection condition excludes zero, so the intersection term vanishes. When $|A'|=2^{30}-1$, this proves
$$
 |B_Q(A')|\le\frac{2^{60}-1}{2^{30}-1}=2^{30}+1 .
$$
Multiplying both coordinate and shift sets by a nonsquare gives the same upper bound for the nonsquare list. This controls perfect agreement. The classical discrepancy conjecture requires control already at a small positive excess above half agreement. [Hanson and Petridis, Theorem 1.2](https://arxiv.org/pdf/1905.09134)

## Which rank information agrees

For either list $E=D,Q$, put $M_E(x,b)=\mathbf1_E(x+b)$. Its row and column sums equal $k$, and its real Gram matrix is
$$
 M_E M_E^{\mathsf T}=(k-\lambda)I+\lambda J,\qquad k-\lambda=(p+1)/4,
$$
where $J$ is the all-ones matrix. Thus the positive-list incidence matrices have identical row Gram matrices and all the same singular values. For $H_E=2M_E-J$, the row sum is $-1$ and $H_E H_E^{\mathsf T}=(p+1)I-J$.

The Legendre matrix $C(x,b)=\chi(x+b)$ has zeros at $x+b=0$, row sum zero, and $CC^{\mathsf T}=pI-J$. Even these last two identities admit a real cyclic model with a fully biased rectangle. Set $K_D=\sqrt{p/(p+1)}(H_D+J/p)$. Centering subtracts its constant component, giving $K_D K_D^{\mathsf T}=pI-J$, and $K_D(x,b)=\sqrt{1+1/p}$ throughout $A\times B$. This last comparison concerns real Gram data. The entries of $K_D$ take two real values, whereas $C$ takes the three values $-1,0,1$.

The example establishes a finite obstruction to deductions from the prime alphabet, degree-one shift words, pair intersections and real Gram data alone. The higher intersections of $D$ depend on binary linear span. For genuine residues, the perfect-list bound uses their additional arithmetic structure. This prime is $3\bmod4$, so the quadratic character defines the directed Paley tournament under differences. The undirected Paley graph uses primes congruent to $1\bmod4$. The asymptotic conjecture quantifies over all sufficiently large primes. The construction gives a comparison at one prime.

## Reproducing the finite parameters

The following Python 3 certificate uses integer arithmetic. It verifies primality, a concrete primitive polynomial, and the rank of the trace equations for the chosen $U=\langle1,g,\ldots,g^{29}\rangle$. The primality check certifies that 37 has order $p-1$ modulo $p$. The factorization of $p-1$ is complete and all listed factors pass trial division, so $\varphi(p)\ge p-1$, forcing primality.

For the auxiliary field, $f(X)=X^{61}+X^5+X^2+X+1$ divides $X^{2^{61}}-X$ by the repeated-squaring check below. The latter polynomial is squarefree and its irreducible factors have degrees dividing 61. Since 61 is prime and $f(0)=f(1)=1$, $f$ is irreducible. Its residue $g=X\bmod f\ne 0,1$ has multiplicative order $p$ because the group has prime order. No discrete logarithms are needed to verify the sizes.

```python
from math import isqrt, prod

p = 2**61 - 1
factors = [2, 3, 3, 5, 5, 7, 11, 13, 31, 41, 61, 151, 331, 1321]
assert prod(factors) == p - 1
assert all(all(q % d for d in range(2, isqrt(q) + 1)) for q in factors)
assert pow(37, p - 1, p) == 1
assert all(pow(37, (p - 1) // q, p) != 1 for q in set(factors))

modulus = (1 << 61) | 0x27

def multiply(x, y):
    result = 0
    while y:
        if y & 1:
            result ^= x
        y >>= 1
        x <<= 1
        if x >> 61:
            x ^= modulus
    return result

def frobenius_trace(x):
    value = x
    trace = 0
    for _ in range(61):
        trace ^= value
        value = multiply(value, value)
    return value, trace

assert frobenius_trace(2)[0] == 2
powers = [1]
for _ in range(89):
    powers.append(multiply(2, powers[-1]))
traces = [frobenius_trace(x)[1] for x in powers]
assert set(traces) <= {0, 1}
pivots = {}
for i in range(30):
    row = sum(traces[i + j] << j for j in range(61))
    while row:
        lead = row.bit_length() - 1
        if lead not in pivots:
            pivots[lead] = row
            break
        row ^= pivots[lead]

a = 2**30 - 1
assert len(pivots) == 30
assert 2**(61 - len(pivots)) - 1 == 2**31 - 1
assert ((p - 1) // 2) // a == 2**30 + 1
print(a, 2**31 - 1, 2**30 + 1)
```

The output gives the coordinate count, the exact Singer perfect-list size, and the upper bound for the genuine quadratic perfect list.

```text
1073741823 2147483647 1073741825
```

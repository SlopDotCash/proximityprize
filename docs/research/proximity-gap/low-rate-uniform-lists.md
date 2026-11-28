# Constant list bounds beyond Johnson at rates one eighth and one sixteenth

For every positive length $n$, every injective evaluation grid, every positive interleaving width, and every field of characteristic zero or characteristic $p>425$, the following two closed-ball bounds hold. The message degree bound in each row is $Rn$. [Exact rational certificate](../../../scripts/probes/probe_low_rate_uniform_lists.py)

| $R$ | Required fraction of agreements $s$ | Relative error allowed | Maximum list size |
|---|---|---|---:|
| $1/8$ | $3533/10000$ | $6467/10000$ | **50,000** |
| $1/16$ | $2499/10000$ | $7501/10000$ | **79,999** |

In both rows $s^2<R$. Thus each list bound is independent of the length at a fixed relative radius beyond its asymptotic Johnson radius. Together with the half-rate theorem this gives three of the four benchmark rates. [Half-rate theorem](half-list-uniform-length.md)

## Changing the normalized weights

Give $X,Y,V$ weights $1/n,R,R$. Write $S_R(w,h)=\sum_{k=0}^h\sum_{j\ge0}(w-R(j+k))_+$. A source monomial of jet degree $j+k$ has $\lceil n(w-R(j+k))_+\rceil$ possible $X$ powers at strict cutoff $w$. The leading-monomial shift from the half-rate proof pairs every positive row of the source for a multiple of $g$ with a row of the full source having the same ceiling correction. Consequently the normalized source difference is at least
$$
                 S_R(rs,h)-S_R(rs-D,h-v)
$$
for every factor of weight $D$ and derivative degree $v$. The verifier uses $S_R(w,h)=2R S_{1/2}(w/(2R),h)$ and checks this against direct summation on small inputs. The local rank $C(r,h)$ does not involve $R$. [Rounding and local quotient argument](half-list-uniform-length.md#a-source-bound-uniform-in-the-length)

The primary derivative cap is two. Write $P=r_0s$, $b_0=\lfloor P/R\rfloor$, and $L$ for the size of a large group. There are at most two positive-derivative factors, and the factors independent of $V$ cost at most $b_0$ words in total. Choose fractional agreements of mass $sn$ per retained word exactly as in the half-rate proof. Since two words can share at most $Rn$ hits, their occupancy vector has mean $s$ and variance bounded by
$$
             \sigma^2=R-s^2+(s-R)/(L-b_0^2).
$$
The regular derivative on a positive-derivative factor gives $\mathbb E[p o]\le s+D-R$ and $0\le o\le D/R+v$. Hence
$$
          \mathbb E o\le 1+(D-R)/s+(D/R+v)\sigma/(2s).
$$

For a linear factor $g=A+BV$, write $e=D-R$, $a=\deg_Y B$, $b=\lfloor D/R\rfloor$, and $K=b+1$. For $A\ne0$ the weighted intersection inequality becomes
$$
          \mathbb E\max(0,o^2-o-1)\le aD+be-abR .
$$
Use the functions $H,Q_j$ of the half-rate proof. Evaluating $\partial_Y^j B$ after removing its vertical content gives bounds $\mathbb E[H+sQ_j]\le e-jR+(\sigma/2)\max Q_j$ for $j<a$, and $\mathbb E[H+Q_a]\le e-aR$. The additional content estimate is unchanged except for $e$:
$$
          [s+(1-s)/2]\mathbb E o\le s+e+(1-s)a/2+\sigma K.
$$
All $Y$-derivatives have orders at most $b_0<p$. When $A=0$, differences of solutions share at most $Rn/p$ hits in characteristic $p$ since they have derivative zero. The occupancy inequality excludes a group of size $L$ on this factor on both rows. In characteristic zero the solutions are constants. [Coefficient and characteristic proofs](half-list-uniform-length.md#mean-order-inequalities)

## Interval certificates

The secondary order is $r=425$. The ordinary derivative estimate excludes quadratic factors over their entire weight range and linear factors at $D\ge uR$ with $u$ in the table. Below $uR$ consider the intervals $bR\le D\le(b+1)R$ for $1\le b<u$ with each possible $a\le b-1$. The verifier bounds $\mathbb E o$ by rational pointwise combinations of the preceding inequalities on the integer orders $0,\ldots,K$, subdividing the weight intervals where necessary. For a fixed affine upper bound and secondary cap, the normalized source surplus is concave in $D$. Both endpoints must pass using that same bound and cap.

| Rate | $r_0$ | $b_0$ | $L$ | $u$ | Primary surplus | Minimum quadratic and high linear surpluses | Low linear intervals and minimum surplus |
|---|---:|---:|---:|---:|---|---|---|
| $1/8$ | 6 | 16 | 24,992 | 8 | $4377/5000$ | 10,850 and 4,180 | 38 intervals, at least 14 |
| $1/16$ | 5 | 19 | 39,990 | 15 | $659/1000$ | 15,577 and 59,126 | 115 intervals, at least 40 |

The generic Bézout cap $b_0\lfloor rs/R\rfloor$ is smaller than $L$ in each case. Thus no positive-derivative factor can carry a large group. The two bounds $2L+b_0$ give the stated list sizes. The geometric argument is written, and the verifier checks all finite inequalities in rational arithmetic.

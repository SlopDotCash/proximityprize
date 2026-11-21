# Classical Paley discrepancy and ordinary binary list decoding

Let $p$ run over odd primes, $\chi$ be the quadratic character of $\mathbb F_p$, and
$$
  S(A,B)=\sum_{b\in B}\sum_{x\in A}\chi(x+b).
$$
Replacing $B$ by $-B$ gives the difference convention. For $U\subseteq\mathbb F_p$, define a binary code of length $u=|U|$ by
$$
 f(0)=1,\qquad f(x)=\chi(x)\ (x\ne0),\qquad
 C_U=\{(f(x+b))_{x\in U}:b\in\mathbb F_p\}\subseteq\{-1,1\}^U.
$$
For $0\le t\le u$, let $L_U(t)$ be the largest number of **distinct codewords** in any Hamming ball of radius $\lfloor(u-t)/2\rfloor$. Equivalently the words have signed inner product at least $t$ with the binary center. Use $L_U(t)=0$ for $t>u$.

The following two statements are equivalent, with all constants independent of the sets and centers. The first is the quadratic-character case of the classical discrepancy conjecture. [Kim, Yip and Yoo, Conjecture 2.12](https://arxiv.org/html/2309.09124v3#S2.SS4)

* For every $0<\alpha<1$ there is an $\eta>0$ such that, for all sufficiently large $p$, every $A,B$ of sizes at least $p^\alpha$ satisfy $|S(A,B)|\le |A||B|p^{-\eta}$.
* For every $0<\alpha<1$ there is a $\beta>0$ such that, for all sufficiently large $p$ and every $U$ of size $u\ge p^\alpha$, the ordinary worst-center list satisfies $L_U(up^{-\beta})<p^{\alpha/2}$.

Thus a list-decoding bound for this particular nonlinear binary code near relative radius $1/2$ would prove discrepancy for the prescribed sets. The quantitative equivalence below is a written proof. Its finite transfer inequalities were also exhaustively checked for $p=3,5,7,11$, totaling 1,669,356 ball thresholds and 39,967,008 rectangle thresholds. The repository separately verifies the two constant-center agreement identities for the affine Reed–Solomon words over the field alphabet. [Affine shift list recovery in Lean](../../../ArkLib/Research/ProximityGap/Frontier/PaleyShiftListRecovery.lean) · [Finite verifier](../../../scripts/probes/probe_paley_row_decoding.py)

## From rectangles to all binary centers

Fix a center $y\in\{-1,1\}^U$, and write $U_+=\{x:y_x=1\}$ and $U_-=U\setminus U_+$. Choose **one shift per distinct codeword** in its list, giving a set $B$ of the same size. Replacing $f(x+b)$ by $\chi(x+b)$ changes a row's correlation by at most one, at $x=-b$. Hence
$$
 (t-1)|B|\le S(U_+,B)-S(U_-,B)\le |S(U_+,B)|+|S(U_-,B)|.
$$
Suppose the discrepancy statement holds at input exponent $\alpha/2$ with saving $\eta$. For $u\ge p^\alpha$ and $|B|\ge p^{\alpha/2}$, apply it to each center part of size at least $p^{\alpha/2}$ and use the trivial bound on each smaller part. This gives
$$
 t/u\le p^{-\eta}+2p^{-\alpha/2}+1/u.
$$
Taking $\beta=\tfrac12\min(\eta,\alpha/2)$ and $t=up^{-\beta}$ contradicts this for sufficiently large $p$. Every binary center is covered.

Unconditionally, the same split defines the signed row $s_y(b)=\sum_{x\in U}y_x\chi(x+b)$. Two-point orthogonality gives $\sum_b s_y(b)^2=pu-(\sum_x y_x)^2$. Thus $L_U(t)\le pu/(t-1)^2$ for $t>1$. For small polynomial $u$ this estimate leaves the required list bound open. [Quadratic two-point identity](../../../ArkLib/Research/ProximityGap/Frontier/_R16LegendreCosetFace.lean)

## Recovering labeled shifts with a small set of coordinates

The projection $b\mapsto(f(x+b))_{x\in A}$ can identify different labels. In fact for $b\ne c$ the character rows agree at exactly $(p-3)/2$ of the $p-2$ coordinates outside $\{-b,-c\}$. Their products sum to $-1$ by two-point orthogonality. They therefore disagree on at least $(p-1)/2$ coordinates even after completing the zeros.

There is a set $T\subseteq\mathbb F_p$ with $|T|\le\lceil2\log_{3/2}p\rceil$ on which all $p$ words are distinct. Among the pairs of shifts still indistinguishable, a uniformly sampled coordinate leaves an expected fraction at most $(p+1)/(2p)\le2/3$ unresolved. Choose a coordinate attaining at most this average at each step. After $k=\lceil2\log_{3/2}p\rceil$ steps the number of unresolved pairs is at most $\binom p2(2/3)^k<1$. The same $T$ works for every $A$.

Set $V=A\cup T$ and $d=|V\setminus A|$. Write $a=|A|$, $m=|B|$. For the constant center with sign $e\in\{-1,1\}$ on $V$, the inner product of word $b$ differs from $e S(A,\{b\})$ by at most $d+1$. The extra sites contribute at most $d$, and the zero on $A$ contributes at most one. Each label with $e S(A,\{b\})\ge t+d+1$ therefore gives a **distinct** codeword in the ball. Choose $e$ to give the sign of $S(A,B)$ and use $|S(A,\{b\})|\le a$ for those exceptional labels. This proves the finite inequality
$$
  |S(A,B)|\le (t+d+1)m+a L_V(t).
$$
Under the binary list statement at exponent $\alpha$, take $t=(a+d)p^{-\beta}$. When $a,m\ge p^\alpha$, the relative bound is at most
$$
  (1+d/a)p^{-\beta}+(d+1)/a+p^{-\alpha/2}.
$$
Since $d=O(\log p)$, this is at most $p^{-\eta}$ for all sufficiently large $p$ with $\eta=\tfrac12\min(\beta,\alpha/2)$.

## What the prize cutoffs and determinant orders detect

On any evaluation set $A$, the dimension-at-least-two Reed–Solomon code contains both lines $u_b(x)=x+b$ and $v_b(x)=b$. Translation by the fixed codeword $x\mapsto-x$ permutes the entire code and carries the first line to the second. Translating the received center by the same word preserves every Hamming list at every radius. For the line MCA event, translating the received pair $(r_0,r_1)$ by any codewords $(h_0,h_1)$ preserves the bad event **for each parameter $b$ and each witness set**. The folded witness $w$ translates to $w+h_0+bh_1$. A joint witness on that very set translates from $(w_0,w_1)$ to $(w_0+h_0,w_1+h_1)$, with inverse given by subtraction. This preserves the absence of a joint witness and thus the fixed-pair bad-parameter probability. Both displayed lines in fact have joint witnesses everywhere at every parameter. [Lean event and probability invariance](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAEquivariance.lean) · [Affine shift MCA witnesses](../../../ArkLib/Research/ProximityGap/Frontier/PaleyShiftListRecovery.lean)

Yet for $A=\mathbb F_p$ the quadratic sum of $u_b$ vanishes for every $b$, whereas that of $v_b$ is $p\chi(b)$. Taking $B$ to be the nonzero squares gives rectangle sums $0$ and $|A||B|$, respectively. The operational Reed–Solomon cutoffs are insensitive to the translation which changes the quadratic test. For $2\le |A|\le(p+1)/2$ the two signed interpolation determinants instead recover the actual row sum as the **difference of their root multiplicities at $b$**. Their total degrees alone supply no bound for the two signed orders on an arbitrary prescribed set of labels. [Exact signed factorization and rectangle identity](../../../ArkLib/Research/ProximityGap/Frontier/PaleySignedFactorization.lean)

Uniform control of an untrimmed sub-Gaussian row moment would be stronger still and is false. Choose $A$ from the nonzero squares. Then $S(A,\{0\})=a$ and, for every fixed $C>0$,
$$
  p^{-1}\sum_b \exp\!\left(S(A,\{b\})^2/(Ca)\right)\ge p^{-1}\exp(a/C).
$$
This is unbounded when $a/\log p\to\infty$. List decoding bounds the **number** of exceptional labels. Even one such label can dominate that exponential average.

## Ordinary lists on the two production subgroups

Let $H$ be the prescribed order-$2^{30}$ subgroup at either production prime, and let $U\subseteq H$, $u=|U|$. Restrict the allowed shift labels to $b\in H$. For any binary center $y$ on $U$ and any integer Hamming radius $r$ with $t=u-2r>1$, the list contains at most
$$
 \min\!\left\{|H|,\left\lfloor\frac{\Lambda^2 u}{(t-1)^2}\right\rfloor\right\}
$$
**shift labels**, so the bound also counts distinct binary codewords even when a puncturing identifies some labels. Here $\Lambda$ is the certified norm of the quadratic difference matrix on $H$. The sum convention causes only a permutation of labels since $-H=H$.

To see this, extend $y$ by zero to $H$ and let $z_b=\sum_{x\in U}y_x\chi(x+b)$. The norm bound gives $\sum_{b\in H}z_b^2\le\Lambda^2u$. A labeled word within distance $r$ has binary inner product at least $t$, so $z_b\ge t-1$ after undoing the zero completion. This also applies with any prescribed subset of the subgroup labels.

At $u=2^{30}$ take $r=\lfloor12u/25\rfloor=515{,}396{,}075$, so $t=42{,}949{,}674$. The respective integer norm upper bounds $197{,}063$ and $146{,}018$ give worst-center list sizes **at most 22,604 and 12,410**. These counts apply to the $2^{30}$ shifts inside the specified subgroup. The equivalence above requires lists over all $p$ field shifts and every puncturing. [Certified production spectra](paley-production-spectrum.md)

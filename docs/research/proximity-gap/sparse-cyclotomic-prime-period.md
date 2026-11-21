# A sparse prime-field period exceeding twice the binary-log scale

Let $n=36960=2^5\cdot3\cdot5\cdot7\cdot11$, let $p=\Phi_{36960}(2)$, and let $H=\langle2\rangle\subset\mathbb F_p^\times$. Then $p$ is a 7681-bit prime, $|H|=n$, $n^2\le p$, and the ordinary additive character at frequency one has
\[
\Re\sum_{x\in H}e^{2\pi i x/p}
\ \ge\ 33750.63425202\ >\ 2\sqrt{n\log_2(p/n)} .
\]
This excludes the absolute constant $2$ in the sparse prime-field estimate quantified over all subgroup orders. It provides a finite lower bound on the unspecified constant in the workbench. Montgomery–Vaughan–Wooley allow an asymptotic correction term, which a single finite example cannot disprove. The subgroup above is 11-smooth in the integer-factorization sense. Sponsor Definition 2.12 requires a multiplicative coset of **power-of-two order**, excluding this example. [Sponsor paper, Definition 2.12](https://eprint.iacr.org/2026/680) · [Montgomery–Vaughan–Wooley](https://www.math.purdue.edu/~twooley/publ/1995%20GSUM.pdf)

## Finite proof and replay

Pomerance's appendix includes the conductor 36960 in a table built with probabilistic prime testing. A separate 304-step PRIMO certificate by Rocke Verser certifies the same integer. The independent `vcert` 0.96 verifier returned `PRIME`. Its source is pinned to `7e1c7d8de544741de7a61ccd6272db49ba164a3b`. The certificate has SHA256 `5629407e2f4fa92922f64fc12eeff5bedcd99fe9a3570c19cbb316d38f1553fe`. The probe reconstructs $p$ from the cyclotomic product, checks equality with the certificate candidate, checks $2^n=1$ and $2^{n/\ell}\ne1$ for the five distinct prime divisors $\ell$ of $n$, and checks $(p-1)/n$ is integral. [Pomerance](https://math.dartmouth.edu/~carlp/cyclotomicprimesjrev.pdf) · [Original certificate](https://factordb.com/cert/1100000000013102704) · [Stored certificate](../../../scripts/probes/certificates/phi36960-primo.cert) · [Pinned checker](https://github.com/MichaelBell/ecpp-dj/blob/7e1c7d8de544741de7a61ccd6272db49ba164a3b/vcert.c)

The probe enumerates $x=2^j\bmod p$, $0\le j<n$. It replaces $t=\min(x,p-x)/p$ by the least multiple $u$ of $1/4096$ above $t$. Both belong to $[0,1/2]$, so $\cos(2\pi t)\ge\cos(2\pi u)$. Taylor's degree-ten polynomial for cosine is a lower bound on this interval by the alternating remainder from degree twelve onward. With $333/106<\pi<355/113$ it uses the lower endpoint for positive terms and upper endpoint for negative terms, then rounds each rational result down to a multiple of $10^{-8}$. Their sum is the displayed certificate. The last strict inequality follows from $p/n<2^{7666}$ and $3375063425202^2-4\cdot36960\cdot7666\cdot10^{16}=57638724136256248740804>0$. This is an integer computation outside Lean. [Exact probe](../../../scripts/probes/probe_sparse_cyclotomic_period.py)

The following commands replay both certificates from the repository root on a system with GMP development headers. Homebrew users may pass the GMP include and library directories shown in the repository's fourth-moment probe instructions.

```sh
python3 -O scripts/probes/probe_sparse_cyclotomic_period.py
curl -fsSL https://raw.githubusercontent.com/MichaelBell/ecpp-dj/7e1c7d8de544741de7a61ccd6272db49ba164a3b/vcert.c -o /tmp/proximity-vcert.c
cc -O3 /tmp/proximity-vcert.c -lgmp -lm -o /tmp/proximity-vcert
/tmp/proximity-vcert scripts/probes/certificates/phi36960-primo.cert
```

## What makes powers of two align

Here is a finite bound independent of any prime-distribution conjecture. Let $s>1$ be squarefree, assume all primes of $m$ divide $s$, and put $n=sm$. Take a primitive prime factor $p$ of $\Phi_n(2)$, so that $2$ has order $n$ modulo $p$, and write $c=\Phi_n(2)/p$. Put $Q_s(X)=(X^s-1)/\Phi_s(X)$ and $A=\max_j|[X^j]Q_s|$. For each $0\le t<m$, all $s$ terms in the corresponding block satisfy
\[
\left\|\frac{2^{am+t}}{p}\right\|_{\mathbb R/\mathbb Z}
\le \frac{c A 2^t}{2^m-1}\qquad(0\le a<s).
\]
Indeed $\Phi_n(2)=\Phi_s(2^m)$. Multiply the numerator of $1/p=cQ_s(2^m)/(2^n-1)$ by $2^{am}$ and reduce the resulting polynomial modulo $X^s-1$ at $X=2^m$. This cyclically permutes $s$ coefficients, each of absolute value at most $A$. Dividing their absolute sum bound $cA(2^{ms}-1)/(2^m-1)$ by $2^n-1$ gives the claimed inequality. The factor $2^t$ supplies the within-block shifts.

For each integer $L$ between zero and $m$, the last $L$ values of $t$ have deficit $1-\cos\le2$. For earlier $t$, use $1-\cos(2\pi u)\le2\pi^2\|u\|^2$, sum the geometric progression in $4^t$, and use $2^m-1\ge2^{m-1}$. Thus
\[
\Re\eta_1\ge n-2sL-\frac{8\pi^2}{3}s(cA)^2 4^{-L}.
\]
Taking $L=\lceil\log_2(cA)\rceil$ when $L\le m$ gives $\Re\eta_1\ge n-O(s(1+\log(cA)))$. In particular, suppose one could find a sequence of such prime factors with $s/\varphi(s)\to\infty$, $m\to\infty$, and $\log(cA)=o(m)$. Along it $\Re\eta_1/n\to1$ and $\log_2 p=m\varphi(s)+O(1)-\log_2 c$, by the uniform cyclotomic height estimate for $\Phi_n(2)$ (Pomerance, equation (2)). These conditions also give $p\ge n^2$ eventually since $\varphi(s)\ge\sqrt{s/2}$. Consequently the binary-log ratio would diverge as $\sqrt{s/\varphi(s)}$. This is a conditional obstruction. The required cofactor estimate is open here. A fixed dyadic radical $s=2$ keeps $s/\varphi(s)=2$. [Cyclotomic height and primitive-factor criteria](https://math.dartmouth.edu/~carlp/cyclotomicprimesjrev.pdf)

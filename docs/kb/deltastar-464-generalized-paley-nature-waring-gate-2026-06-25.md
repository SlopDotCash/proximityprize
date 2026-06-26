# Issue #464: Generalized-Paley Nature / Weak-Waring Gate

Date: 2026-06-25

Status: structural metadata guardrail; not a prize proof.

Source checked: Podesta--Videla, arXiv:2604.06513, *The nature of the spectrum of generalized
Paley graphs and weak Waring numbers over finite fields*.

## Artifact

- Lean:
  `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_GeneralizedPaleyNatureWaringGate.lean`

## Point

The 2026 generalized-Paley paper gives useful classification data:

- real spectrum iff the generalized Paley graph is undirected;
- arithmetic criteria and infinite families for integral spectra;
- directed-period / index-of-imprimitivity structure;
- weak Waring numbers reduced to classical Waring numbers, equivalently diameter information for
  the associated Cayley graphs.

These are structural facts about the generalized Paley graph.  The #464 consumer needs a different
input: a worst non-principal eigenvalue bound

```text
lambda_2 = max_{b != 0} |sum_{x in mu_n} e_p(bx)|
```

at the `sqrt(n log(p/n))` scale.

## Lean Gate

The Lean file abstracts the paper-facing metadata as:

```lean
HasNatureWaringData m :=
  m.weakWaringNumber <= 2 /\ m.realSpectrum /\ m.integralSpectrum
```

and proves:

```lean
generalizedPaley_nature_waring_gate :
  0 <= C ->
  exists m, HasNatureWaringData m /\ not (RamanujanScaleBound C m)
```

The countermodel sets the non-principal radius equal to the degree, with degree `(C + 1)^2`.
Thus even bounded weak-Waring/diameter metadata plus real/integral spectrum data does not imply
`lambda_2 <= C * sqrt(degree)`.

## Consequence For #464

The paper is still relevant because it identifies the generalized-Paley object correctly and
organizes its spectrum/diameter metadata.  But those metadata do not supply the missing analytic
radius estimate.  Any route using this classification still needs a separate theorem controlling
the Gauss-period maximum; otherwise it only relocates the Paley/BGK wall.

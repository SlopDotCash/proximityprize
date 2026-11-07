# Nested polynomial axis conventions

ArkLib represents the trivariate polynomials used by the BCIKS20 development as
`F[Z][X][Y] = Polynomial (Polynomial (Polynomial F))`. The nesting order is:

| Semantic variable | Structural position |
|---|---|
| `Y` | outer polynomial variable |
| `X` | middle polynomial variable |
| `Z` | innermost polynomial variable |

Use the operations in `Trivariate` when the input is trivariate:

- `evalAtX`, `evalAtY`, and `evalAtZ` specialize the variable named in the declaration.
- `degreeInX`, `degreeInY`, and `degreeInZ` measure one named variable.
- `degreeXY` and `degreeYZ` are projected total degrees; `totalDegreeXYZ` includes all three
  variables.
- `D_Y` and `D_YZ` remain the paper-facing names used by the BCIKS20 statements and are wrappers
  around `degreeInY` and `degreeYZ`.

Do not read an operation's axis from its type arguments alone. Applying
`Polynomial.Bivariate` directly to a trivariate value regards it as a bivariate polynomial over
the coefficient ring `F[Z]`. Consequently:

- `Bivariate.evalX (Polynomial.C x) p` does evaluate the semantic middle variable `X`, but
  `Trivariate.evalAtX x p` records that intention explicitly.
- `Bivariate.natDegreeY p` and `Bivariate.degreeX p` are the semantic `Y`- and `X`-degrees,
  respectively, but the trivariate wrappers are preferred in statements.
- `Bivariate.totalDegree p` is only the `(X, Y)` projection and ignores `Z`. Write
  `Trivariate.degreeXY p` for that quantity. It is not the full trivariate total degree and is not
  the `(Y, Z)` projection.

Generic bivariate operations remain appropriate after a trivariate specialization, or on an
actual bivariate coefficient. For example, `Bivariate.totalDegree (p.coeff j)` measures the
`(Z, X)` degree of the `Y ^ j` coefficient, and `Bivariate.totalDegree (Trivariate.evalAtX x p)`
measures the `(Z, Y)` degree after specializing `X`.

When reviewing axis-sensitive code, test with unequal exponents such as `Z ^ 5 * X ^ 7 * Y ^ 3`.
For that monomial, `degreeXY = 10`, `degreeYZ = 8`, and `totalDegreeXYZ = 15`; symmetric examples
can allow an accidental permutation to pass unnoticed.

The upstream integration retires the unused downstream diagnostic
`ProximityGap.D_YZ_triMonomial_of_ne`. Its `j` conclusion for `X ^ i * Y ^ j * Z ^ t`
with `i ≠ j` described an obsolete implementation with reversed coefficient indices that
ignored `t`. The canonical measure gives `j + t`, as proved by the retained extension theorem
`ProximityGap.D_YZ_triMonomial`. The genuine upper bound `D_YZ_le_of_ZdegLE` keeps its
statement and now uses the corrected axes. The retirement and caller audit are recorded in
`scripts/integration/downstream-extension-audit.json`.

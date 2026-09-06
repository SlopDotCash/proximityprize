# Four-line LP assignment validation

The four-line fractional amplifier probe now substitutes the returned rational assignment into every stated LP constraint and verifies that its objective equals the returned optimum. Missing variables receive the same zero default already used by the reporting ledger. A failed check raises an error before any candidate is reported.

This verifies primal feasibility and consistency of the reported objective; it is not an independent optimality certificate. The optimization model, solver and candidate enumeration are unchanged. A mocked all-zero assignment is rejected because it violates the per-fibre mass equation. The full 29-candidate solver review remains pending, so retention remains 71 of 92.

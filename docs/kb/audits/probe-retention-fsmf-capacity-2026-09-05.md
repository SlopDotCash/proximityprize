# Retention mapping: FSMF one-fresh capacity — 2026-09-05

The full replay of `scripts/probes/probe_fsmf_p1_onefresh_capacity.py` passed
and matched `scripts/probes/_out_fsmf_capacity.txt` byte for byte. The header
now distinguishes the encoded capacity model from realizable polynomial
packings. These two artifacts bring the original mapping to 30 of 92, with
62 remaining. No artifacts are deleted.

For m=4,10,16,22,2²⁶, integer calculations return model maxima
58,156,252,348,1073741820 against budgets 64,160,256,352,1073741824.
The last value is four below its fixed P1 budget. Three through five lines use
integer slot counts n2,n3,n4 and shared-root count s; the objective and coverage
constraints are affine in s. Endpoint and boundary candidates implement the
model optimization. Two lines use a separate closed-form expression.

The program does not construct polynomial potentials or prove its structural
premises. In particular, it enumerates no n5 slot variable even when checking
five lines. It also does not establish that every relevant configuration is
represented by these constraints. Its printed feasibility and maxima therefore
refer to this encoded model. They do not certify general geometric feasibility,
exclude all five-line configurations, or close the production problem in #164.
The miniature constructions referenced in the source were not replayed here.

# FSMF m=10 reporting correction — 2026-09-06

The default m=10 probe confirms every witnessed scalar, then samples some
non-witness scalars. It therefore cannot report a complete bad count or
certify the global budget. Sampled mode now reports the verified lower bound,
`complete_census: false`, and null total-count/`holds` fields. Only `--full`
can supply a complete count and bound status.

The deterministic witness construction gives 155 labels, correcting its
old prediction of 154. Covered coordinates yield 150 labels; the prescribed
free labels are 2,4,5,7. The third line adds label 32 at coordinate 157, while
its label 438 at coordinate 158 is already covered. These set/count checks
were replayed directly from the construction and witness census.

Both JSON-report branches passed a stubbed-census check, distinguishing this
reporting validation from mathematical validation. Python compilation and
whitespace checks pass. A full 641-scalar GS run is still pending; neither
this correction nor the archived sampled run is evidence of its completion.
This file does not advance the original retention-review count.

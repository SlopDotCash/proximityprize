# Local library extensions

`ArkLib/ToMathlib/` contains supporting mathematical results not supplied by the
pinned Mathlib dependency. Preserve contributor copyright when reorganizing them.

`ArkLib/ToVCVio/` contains compatibility lemmas for the pinned VCVio API, including
`simulateQ` / `OracleComp` helpers. Before changing dependency pins, compare these
local declarations with the candidate dependency and remove duplicates only after
validating their consumers. The historical README's commit-distance estimate is
not a current pin audit.

All project pushes and pull requests target `SlopDotCash/proximityprize`.
Dependency comparison does not authorize submissions to upstream repositories.

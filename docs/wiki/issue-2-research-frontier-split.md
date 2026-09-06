# Issue 2: Frontier research split

This migration moves 3,090 Lean modules into `Research/ProximityPrize`: the 3,079
Frontier modules, nine dependent ProximityGap modules, the root workbench, and
`TmpCheck` under `Scratch`. The ProximityGap workbench becomes `LegacyWorkbench`;
the root workbench becomes the research library root. Declaration namespaces and
proof bodies are preserved. Imports change to the new module paths.

`ResearchProximityPrize` is a separate Lake library. Its thin namespace root
`Research.ProximityPrize` imports `Research.ProximityPrize.PROXIMITY_PRIZE_WORKBENCH`,
which remains the research entry point. The default single-root build follows
imports instead of an all-submodules glob, preserving the explicit lane exclusions. Its generated `All.lean`
contains 3,084 imports, preserving the four existing expensive-lane exclusions and
excluding the scratch checker and root itself. `ArkLib.lean` contains 1,900 imports
after this slice. Generate both roots after staging added or moved Lean files:

```sh
./scripts/update-lib.sh
python3 scripts/update-research-lib.py
```

This is the first structural slice of issue #2. It does not establish that the
remaining ProximityGap modules are library content. Paper-family classification,
tendrils elsewhere in ArkLib, the remaining research modules, markdown/corpus
relocation and distillation still require review. The research-to-library import
direction must be enforced by CI; ArkLib must never import Research.

Before publication, update all source-path consumers, generated-file checks,
strict token and hole scans, axiom manifests, build scripts and CI for both library
targets. Run both builds and the strict checks. The current migration has not passed
Lean validation and does not close issue #2 or the independent proof gate in #164.

The initial move audit found no non-import changes in the 3,090 modules. The expanded
strict scan then exposed a pre-existing bodyless `opaque qaryEntropyInv` in the root
workbench, which the old ArkLib-only scan did not cover. That one definition is now
a lower generalized inverse given by an infimum of an entropy superlevel set; its
comments explicitly separate the candidate expression from production claims.
This repair is additional to the mechanical move and requires Lean validation.

Citation and declaration extraction now cover both roots by default. The citation
JSON records `lean_roots`, and `--lean-root` accepts one or more directories.
The coverage regression tests check both proof scans, import-boundary parsing, and
citation retention across the two roots.

The existing CI build runs `validate.sh`, whose default Lake build now includes both
library targets. Style-lint input enumeration also includes the research tree.
The full hosted build and lint acceptance remain unverified.

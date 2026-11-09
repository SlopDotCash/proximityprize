/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.Classes.Slice

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-!
# Generic Slice Type Classes

This file defines type classes for slicing operations on collections, inspired by
Python's slice notation.
The notation provides three operations:
- `v⟦:m⟧` takes the first `m` elements (via `SliceLT`)
- `v⟦m:⟧` drops the first `m` elements (via `SliceGE`)
- `v⟦m₁:m₂⟧` takes elements from index `m₁` to `m₂ - 1` (via `Slice`)

Each notation also supports manual proof syntax with `'h`:
- `v⟦:m⟧'h` for explicit proof in `SliceLT`
- `v⟦m:⟧'h` for explicit proof in `SliceGE`
- `v⟦m₁:m₂⟧'h` for explicit proof in `Slice`

The design follows the pattern of `GetElem` from the standard library, with:
- `outParam` annotations for better type inference
- Validity predicates that can be automatically proven by tactics like `omega`
- Dependent types where the result collection type can depend on all parameters

## Type Classes

- `SliceLT`: For "take first n elements" operations
- `SliceGE`: For "drop first n elements" operations
- `Slice`: For "range slice" operations

The type classes are generic and can be implemented for any collection type. This file provides
instances for:
- **Fin tuples**: Available in `ArkLib.Data.Fin.Tuple.Notation` (with proof obligations)
- **Array**: With `True` validity (no proof obligations needed)
- **List**: With `True` validity (no proof obligations needed)
-/

universe u v v' w

/-! ## Sliceable type classes -/

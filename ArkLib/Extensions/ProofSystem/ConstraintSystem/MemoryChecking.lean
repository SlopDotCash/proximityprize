/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.ConstraintSystem.MemoryChecking

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gemini
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Basic

/-!
  # Memory checking relations: read-only and read-write

  This file defines a generic framework for memory checking relations. The goal is to provide a
  flexible API that can be instantiated with various memory models and operation containers.

  ## Main Concepts

  - **`MemoryRead`**, **`MemoryWrite`**: Represent a single read or write operation, containing
    the memory index and the value.

  - **`MemoryOp`**: An inductive type that wraps `MemoryRead` and `MemoryWrite` to represent a
    trace of operations.

  - **`Memory` typeclass**: Abstracts over the memory representation. It provides `read` and
    `write` operations. Instances for dependent functions (`(i : ι) → α i`) and `Vector` are
    provided.

  - **`ReadOnly.relation`**: A relation that holds if a given sequence of read operations is
    consistent with a given memory state.

  - **`ReadWrite.relation`**: A relation that holds if executing a sequence of memory operations
    on a starting memory state results in a given final memory state. Read operations are
    checked for consistency along the way.
-/

universe u v w

namespace MemoryRead

variable {ι : Type u} {α : ι → Type v}

end MemoryRead

namespace MemoryWrite

variable {ι : Type u} {α : ι → Type v}

end MemoryWrite

namespace MemoryOp

variable {ι : Type u} {α : ι → Type v}

end MemoryOp

namespace MemoryChecking

variable {ι : Type u} {α : ι → Type v}

namespace ReadOnly

variable {ι : Type u} {α : ι → Type v} {M : Type w} [Memory ι α M] [∀ i, DecidableEq (α i)]

end ReadOnly

namespace ReadWrite

variable {ι : Type u} {α : ι → Type v} {M : Type w} [Memory ι α M] [∀ i, DecidableEq (α i)]

end ReadWrite

end MemoryChecking

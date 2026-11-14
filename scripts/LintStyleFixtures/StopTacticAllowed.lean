/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: Codex
-/

inductive Choice where
  | stop : Nat → Choice

open Choice in
def multilinePattern : Choice → Nat
  | stop
      n => n

namespace Helpers

def stop (n : Nat) : Nat := n
def all_goals (f : Nat → Nat) : Nat := f 1
def functionArgument : Nat := all_goals stop
def scopedTerm : Nat := set_option maxHeartbeats 10000 in stop 1
def parenthesizedApplication : Nat := (stop 2)
def escapedIdentifier : Nat := «stop» 3
def literal : String := "first | stop done | done"

-- first | stop done | done
#guard_msgs in
example (stop : Nat) : Nat := by exact stop

end Helpers

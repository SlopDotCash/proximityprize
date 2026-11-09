/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: Codex
-/

import Lean

theorem multiline : False := by
  stop
  done

theorem stopInline : False := by stop done

theorem bullet : False ∧ True := by
  constructor
  · stop done
  · trivial

theorem alternatives : False := by
  first | stop done | done

theorem nested : False := by
  all_goals stop done

theorem braces : False := by { stop done }

example : False := by all_goals stop done

theorem deferred (h : False := by all_goals stop done) : False := h

set_option warn.sorry false in
theorem disabledWarning : False := by all_goals stop done

#guard_msgs (drop warning, drop error) in
#guard_msgs (drop warning, drop error) in
theorem capturedMessage : False := by first | stop done | done

#guard_msgs (drop warning, drop error) in
example : False := by { stop done }

open Lean in
theorem quotedGuard : False := by
  let _unused : MacroM (TSyntax `command) := `(command| #guard_msgs in #check Nat)
  all_goals stop done

set_option linter.all false
set_option warn.sorry false in
theorem disabledLinters : False := by all_goals stop done

#exit

/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights
Reserved.  Released under Apache 2.0 license as described in the file
LICENSE.
Author(s): Nathan Wetzler
-/

import Mathlib.Tactic.Sat.FromLRAT

def unsat_4_8_cnf : String :=
  "p cnf 4 8 1 2 -3 0 -1 -2 3 0 2 3 -4 0 -2 -3 4 0 -1 -3 -4 0 1 3 4 0 -1 2 4 0 1 -2 -4 0"

def unsat_4_8_lrat : String :=
  "9 -3 -4 0 5 1 8 0 9 d 5 0 10 3 -4 0 3 2 8 0 10 d 3 0 11 -4 0 9 10 0 12 3 0 11 6 7 2 0 13 -2 0 12 11 4 0 14 1 0 13 12 1 0 15 0 13 14 11 7 0"

lrat_proof unsat_4_8_thm unsat_4_8_cnf unsat_4_8_lrat

-- #check @unsat_4_8_thm
-- Results in:
-- unsat_4_8_thm : ∀ (a a_1 a_2 a_3 : Prop),
--   ((¬a ∧ ¬a_1 ∧ a_2 ∨ a ∧ a_1 ∧ ¬a_2) ∨ ¬a_1 ∧ ¬a_2 ∧ a_3 ∨ a_1 ∧ a_2 ∧ ¬a_3) ∨
--     (a ∧ a_2 ∧ a_3 ∨ ¬a ∧ ¬a_2 ∧ ¬a_3) ∨ a ∧ ¬a_1 ∧ ¬a_3 ∨ ¬a ∧ a_1 ∧ a_3

-- #print unsat_4_8_thm

theorem unsat_4_8_cnf_is_unsat (x1 x2 x3 x4 : Prop) :
  ¬(( x1 ∨  x2 ∨ ¬x3) ∧
    (¬x1 ∨ ¬x2 ∨  x3) ∧
    ( x2 ∨  x3 ∨ ¬x4) ∧
    (¬x2 ∨ ¬x3 ∨  x4) ∧
    (¬x1 ∨ ¬x3 ∨ ¬x4) ∧
    ( x1 ∨  x3 ∨  x4) ∧
    (¬x1 ∨  x2 ∨  x4) ∧
    ( x1 ∨ ¬x2 ∨ ¬x4)) :=
by
  have lrat := from_lrat unsat_4_8_cnf unsat_4_8_lrat
  specialize lrat x1 x2 x3 x4
  simp [or_assoc] at lrat
  -- Solution 1
  simp [not_or, imp_iff_not_or]
  assumption
  -- -- Solution 2
  -- repeat (rw [not_and_or])
  -- repeat (rw [not_or])
  -- repeat (rw [not_not])
  -- assumption

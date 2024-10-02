/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases'`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by
  -- intro hPaQ
  -- cases' hPaQ with hP hQ
  -- exact hP
  rintro ⟨hP, hQ⟩
  exact hP


example : P ∧ Q → Q := by
  rintro ⟨hP, hQ⟩
  exact hQ

example : (P → Q → R) → P ∧ Q → R := by
  rintro hPQR ⟨hP, hQ⟩
  apply hPQR <;> assumption

example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  assumption
  assumption


/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  rintro ⟨hP, hQ⟩
  constructor
  assumption
  assumption


example : P → P ∧ True := by
  intro hP
  constructor
  tauto
  triv

example : False → P ∧ False := by
  intro hF
  tauto

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  rintro ⟨hP, hQ⟩
  rintro ⟨hQ, hR⟩
  constructor
  assumption
  assumption

example : (P ∧ Q → R) → P → Q → R := by
  intro hPaQIR
  intro hP hQ
  apply hPaQIR
  constructor
  repeat assumption
  

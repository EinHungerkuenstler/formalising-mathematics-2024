/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  assumption

example : Q → P ∨ Q := by
  intro hQ
  right
  assumption

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  intro hPR
  intro hQR
  cases' hPoQ with hP hQ
  apply hPR
  assumption
  apply hQR
  assumption

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro hPoQ
  cases' hPoQ with hP hQ
  right
  exact hP
  left
  exact hQ

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  intro hPaQaR
  cases' hPaQaR with hPaQ hPR
  cases' hPaQ with hP hQ
  left
  exact hP
  right
  left
  exact hQ
  right
  right
  exact hPR
  intro hPaQR
  cases' hPaQR with hP hQaR
  left
  left
  exact hP
  cases' hQaR with hQ hR
  left
  right
  exact hQ
  right
  exact hR


example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hPR
  intro hQS
  intro hPaQ
  cases' hPaQ with hP hQ
  constructor
  apply hPR
  assumption
  right
  apply hQS
  assumption

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPQ hPoR
  cases' hPoR with hP hR
  constructor
  apply hPQ
  exact hP
  right
  exact hR

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro hPR hQS
  constructor
  intro hPoQ
  cases' hPoQ with hP hQ
  left
  cases' hPR with hPiR hRiP
  apply hPiR
  exact hP
  right
  cases' hQS with hQiS hSiQ
  apply hQiS
  exact hQ
  intro hRoS
  cases' hRoS with hR hS
  left
  rw [hPR]
  exact hR
  right
  rw [hQS]
  exact hS


-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  intro hnPoQ
  constructor
  intro hP
  apply hnPoQ
  left
  exact hP
  intro hQ
  apply hnPoQ
  right
  exact hQ
  intro hnPonQ
  intro hPoQ
  cases' hnPonQ with hnP hnQ
  cases' hPoQ with hP hQ
  apply hnP
  exact hP
  apply hnQ
  exact hQ

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  intro hnPaQ
  by_cases hP : P
  right
  intro hQ
  apply hnPaQ
  constructor
  repeat assumption
  left
  exact hP
  rintro (hnP | hnQ) ⟨hP, hQ⟩
  contradiction
  contradiction


  -- intro hnPonQ
  -- intro hPaQ
  -- cases' hnPonQ with hnP hnQ
  -- cases' hPaQ with hP hQ
  -- apply hnP
  -- assumption
  -- cases' hPaQ with hP hQ
  -- apply hnQ
  -- assumption

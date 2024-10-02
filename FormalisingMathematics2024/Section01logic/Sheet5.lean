/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl

example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rw [h]

example : (P ↔ Q) ↔ (Q ↔ P) :=
  by {
    constructor <;>
      · intro h
        rw [h]
  }

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
  by {
    intro hPQ hQR
    rwa [hPQ]
  }

example : P ∧ Q ↔ Q ∧ P :=
  by {
    constructor <;>
    · rintro ⟨hP, hQ⟩
      exact ⟨hQ, hP⟩
  }

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  intro hPaQaR
  cases' hPaQaR with hPaQ hR
  cases' hPaQ with hP hQ
  constructor
  assumption
  constructor
  repeat assumption
  intro hPaQaR
  constructor
  cases' hPaQaR with hP hQR
  cases' hQR with hQ hR
  constructor
  repeat assumption
  cases' hPaQaR with hP hQaR
  cases' hQaR with hQ hR
  assumption

example : P ↔ P ∧ True := by
  constructor
  intro hP
  constructor
  assumption
  triv
  intro hPT
  cases' hPT with hP hT
  exact hP


example : False ↔ P ∧ False := by
  constructor
  intro hF
  constructor
  exfalso
  exact hF
  exact hF
  intro hPF
  cases' hPF with hP hF
  exact hF
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hPQ hRS
  constructor
  cases' hPQ with hPiQ hPQ
  intro hPaR
  constructor
  apply hPiQ
  cases' hPaR with hP hR
  exact hP
  cases' hRS with hRiS hSiR
  apply hRiS
  cases' hPaR with hP hR
  exact hR
  intro hQaS
  constructor
  cases' hQaS with hQ hS
  cases' hPQ with hPiQ hQiP
  apply hQiP
  exact hQ
  cases' hRS with hRiS hSiR
  apply hSiR
  cases' hQaS with hQ hS
  exact hS

example : ¬(P ↔ ¬P) := by
  intro h
  have hnP : ¬P := by
    cases' h with hPnP hnPP
    intro hP
    apply hPnP <;>
    assumption
  apply hnP
  rw [h]
  exact hnP

/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 3 : not in (`∉`) and complement `Aᶜ`

The definition in Lean of `x ∉ A` is `¬ (x ∈ A)`. In other words,
`x ∉ A`, `¬ (x ∈ A)` and `(x ∈ A) → False` are all equal *by definition*
in Lean.

The complement of a subset `A` of `X` is the subset `Aᶜ`; it's the terms of
type `X` which aren't in `A`. The *definition* of `x ∈ Aᶜ` is `x ∉ A`.

For example, if you have a hypothesis `h : x ∈ Aᶜ` and your goal
is `False`, then `apply h` will work and will change the goal to `x ∈ A`.
Think a bit about why, it's a good logic exercise.

-/


open Set

variable (X : Type) -- Everything will be a subset of `X`
  (A B C D E : Set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : x ∉ A → x ∈ A → False := by
  intro hnA hA
  apply hnA
  exact hA

example : x ∈ A → x ∉ A → False := by
  intro hA hnA
  apply hnA
  exact hA

example : A ⊆ B → x ∉ B → x ∉ A := by
  intro hAB hnB
  intro hxA
  apply hnB
  apply hAB at hxA
  exact hxA

-- Lean couldn't work out what I meant when I wrote `x ∈ ∅` so I had
-- to give it a hint by telling it the type of `∅`.
example : x ∉ (∅ : Set X) := by
  simp_all only [mem_empty_iff_false, not_false_eq_true]

example : x ∈ Aᶜ → x ∉ A := by
  intro hxAc hxA
  apply hxAc at hxA
  exact hxA

example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ := by
  constructor
  · intro hAxA hExAc
    cases' hExAc with y hy
    apply hy
    apply hAxA at y
    exact y
  · intro hnxAc
    intro z
    by_contra hnzA
    apply hnxAc
    use z
    apply hnzA

example : (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ := by
  aesop

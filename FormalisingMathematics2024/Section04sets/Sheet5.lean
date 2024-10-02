/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal.

## Tactics

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : A ∪ A = A := by
  ext a
  constructor
  · intro haAA
    cases' haAA with haA1 haA2
    exact haA1
    exact haA2
  · intro haA
    left
    exact haA

example : A ∩ A = A := by
  ext a
  constructor
  · intro haAA
    cases' haAA with haA1 haA2
    exact haA1
  · intro haA
    constructor
    repeat exact haA

example : A ∩ ∅ = ∅ := by
  ext a
  constructor
  · intro haAe
    obtain ⟨_, hae⟩ := haAe
    exact hae
  · intro haAe
    constructor
    cases haAe
    exact haAe

example : A ∪ univ = univ := by simp only [union_univ]

example : A ⊆ B → B ⊆ A → A = B := by
  -- intro a a_1
  -- unhygienic ext
  -- apply Iff.intro
  -- · intro a_2
  --   apply a
  --   simp_all only
  -- · intro a_2
  --   apply a_1
  --   simp_all only
  exact fun a a_1 ↦ Subset.antisymm a a_1

example : A ∩ B = B ∩ A := by
  -- ext ab
  -- constructor
  -- · intro habAB
  --   constructor
  --   · obtain ⟨ _, habB⟩ := habAB
  --     exact habB
  --   · obtain ⟨habA, _⟩ := habAB
  --     exact habA
  -- · intro habBA
  --   constructor
  --   · obtain ⟨_, habA⟩ := habBA
  --     exact habA
  --   · obtain ⟨habB, _⟩ := habBA
  --     exact habB
  exact inter_comm A B

example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  symm
  exact inter_assoc A B C

example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  ext s
  constructor
  · rintro (hA | hB | hC)
    · left; left ; assumption
    · left; right; assumption
    · right; assumption
  · rintro ((hA | hB) | hC)
    · left; assumption
    · right; left; assumption
    · right; right; assumption

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  exact union_distrib_left A B C


example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  exact inter_distrib_left A B C

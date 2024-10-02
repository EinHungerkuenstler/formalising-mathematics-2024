/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Jujian Zhang, Kevin Buzzard
-/
import Mathlib.Tactic

namespace Section10sheet1

noncomputable section

/-!

# Topological Spaces in Lean

For any `X : Type`, the type `TopologicalSpace X` is the type of topologies on `X`.
`TopologicalSpace` is a structure; its four fields are one data field `IsOpen : Set X → Prop` (the
predicate on subsets of `X` saying whether or not they're open) and then three proof fields
(`isOpen_univ` saying the whole space is open, `isOpen_inter` saying the intersection of two
opens is open, and `isOpen_sUnion` saying an arbitrary union of opens is open).

Here is a simple example: let's make the discrete topology on a type.
-/

open TopologicalSpace

variable (X : Type)

set_option linter.unusedVariables false -- please stop moaning about unused variables

example : TopologicalSpace X where
  IsOpen (s : Set X) := True -- "Is `s` open? Yes, always"
  isOpen_univ := by
    -- is the whole space open? The goal is `True`
    triv
  isOpen_inter := by
    -- let s and t be two sets
    intros s t
    -- assume they're open
    intros hs ht
    -- Is their intersection open?
    -- By definition, this means "can you prove `True`"?
    triv
  isOpen_sUnion := by
    -- say F is a family of sets
    intro F
    -- say they're all open
    intro hF
    -- Is their union open?
    triv

/-
A much more fiddly challenge is to formalise the indiscrete topology. You will be constantly
splitting into cases in this proof.
-/

example : TopologicalSpace X where
  IsOpen (s : Set X) := s = ∅ ∨ s = Set.univ -- empty set or whole thing
  isOpen_univ := by
    dsimp
    right
    triv
  isOpen_inter := by
    intro x₁ x₂ hx
    cases' hx with hx₁ hx₂
    · intro hx₂
      cases' hx₂ with hx₂₁ hx₂₂
      · left
        rw [hx₁, hx₂₁]
        simp
      · left
        rw [hx₁, hx₂₂]
        simp
    · intro hx₂
      cases' hx₂ with hx₂₁ hx₂₂
      · left
        rw [hx₂, hx₂₁]
        simp
      · right
        rw [hx₂, hx₂₂]
        simp
  isOpen_sUnion := by
    intro F hF
    by_cases h : Set.univ ∈ F
    · right
      aesop
    · left
      have h1 : ∀ s ∈ F, s = ∅ := by
        by_contra! h2
        obtain ⟨x, hx1, hx2⟩ := h2
        specialize hF x hx1
        aesop
      exact Set.sUnion_eq_empty.mpr h1

-- `isOpen_empty` is the theorem that in a topological space, the empty set is open.
-- Can you prove it yourself? Hint: arbitrary unions are open

example (X : Type) [TopologicalSpace X] : IsOpen (∅ : Set X) := by
  convert isOpen_sUnion (s := ∅) ?_ <;> simp

-- The reals are a topological space. Let's check Lean knows this already
#synth TopologicalSpace ℝ

-- Let's make it from first principles.

def Real.IsOpen (s : Set ℝ) : Prop :=
  -- every element of `s` has a neighbourhood (x - δ, x + δ) such that all y in this
  -- neighbourhood are in `s`
  ∀ x ∈ s, ∃ δ > 0, ∀ y : ℝ, x - δ < y ∧ y < x + δ → y ∈ s

-- Now let's prove the axioms
lemma Real.isOpen_univ : Real.IsOpen (Set.univ : Set ℝ) := by
  intro x hx
  use 999
  norm_num

lemma Real.isOpen_inter (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  intro x hx
  obtain ⟨δs, hδs, hs⟩ := hs x (by aesop)
  obtain ⟨δt, hδt, ht⟩ := ht x (by aesop)
  use min δs δt, by positivity
  rintro y ⟨h1, h2⟩
  constructor
  · apply hs
    have foo : min δs δt ≤ δs := min_le_left δs δt
    constructor <;> linarith
  · apply ht
    have foo : min δs δt ≤ δt := min_le_right δs δt
    constructor <;> linarith

lemma Real.isOpen_sUnion (F : Set (Set ℝ)) (hF : ∀ s ∈ F, IsOpen s) : IsOpen (⋃₀ F) := by
  intro x hx
  simp_rw [Set.mem_sUnion] at *
  rcases hx with ⟨t, htF, hxt⟩
  obtain ⟨δ, hδpos, h⟩ := hF t htF x hxt
  use δ, hδpos
  intro y hy
  use t
  constructor
  · assumption
  · apply h
    assumption
  -- peel h with h1 y hyt
  -- use t, htF

-- now we put everything together using the notation for making a structure
example : TopologicalSpace ℝ where
  IsOpen := Real.IsOpen
  isOpen_univ := Real.isOpen_univ
  isOpen_inter := Real.isOpen_inter
  isOpen_sUnion := Real.isOpen_sUnion

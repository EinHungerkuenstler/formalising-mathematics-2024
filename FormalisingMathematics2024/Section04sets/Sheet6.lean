/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 6 : pushforward and pullback

## Pushforward of a set along a map

If `f : X → Y` then given a subset `S : Set X` of `X` we can push it
forward along `f` to make a subset `f(S) : Set Y` of `Y`. The definition
of `f(S)` is `{y : Y | ∃ x : X, x ∈ S ∧ f x = y}`.

However `f(S)` doesn't make sense in Lean, because `f` eats
terms of type `X` and not `S`, which has type `Set X`.
In Lean we use the notation `f '' S` for this. This is notation
for `Set.image` and if you need any API for this, it's likely
to use the word `image`.

## Pullback of a set along a map

If `f : X → Y` then given a subset `T : Set Y` of `Y` we can
pull it back along `f` to make a subset `f⁻¹(T) : Set X` of `X`. The
definition of `f⁻¹(T)` is `{x : X | f x ∈ T}`.

However `f⁻¹(T)` doesn't make sense in Lean either, because
`⁻¹` is notation for `Inv.inv`, whose type in Lean
is `α → α`. In other words, if `x` has a certain type, then
`x⁻¹` *must* have the same type: the notation was basically designed
for group theory. In Lean we use the notation `f ⁻¹' T` for this pullback.

-/

variable (X Y : Type) (f : X → Y) (S : Set X) (T : Set Y)

example : S ⊆ f ⁻¹' (f '' S) := by
  intro s hs
  -- simp only [Set.mem_preimage, Set.mem_image]
  -- use s
  exact ⟨s, hs, rfl⟩


example : f '' (f ⁻¹' T) ⊆ T := by
  -- intro t ht
  -- cases' ht with x hx
  -- obtain ⟨h1, h2⟩ := hx
  -- exact Set.mem_of_eq_of_mem (id h2.symm) h1
  rintro _ ⟨x, hx, rfl⟩
  exact hx
  -- exact Set.image_preimage_subset f T


-- `library_search` will do this but see if you can do it yourself.
example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
  constructor
  · intro a
    simp_all only [Set.image_subset_iff]
  · intro a
    simp_all only [Set.image_subset_iff]
    -- · intro fST
  --   intro s hs
  --   simp only [Set.mem_preimage]
  --   apply fST
  --   exact Set.mem_image_of_mem f hs
  -- · intro SIfT
  --   intro y hy
  --   cases' hy with x hx
  --   obtain ⟨hxS, hfxy⟩ := hx
  --   simp only [Set.mem_preimage] at SIfT
  --   exact Set.mem_of_eq_of_mem (id hfxy.symm) (SIfT hxS)


-- Pushforward and pullback along the identity map don't change anything
-- pullback is not so hard
example : id ⁻¹' S = S := by
  rfl

-- pushforward is a little trickier. You might have to `ext x, split`.
example : id '' S = S := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact hs
  · intro hx
    use x
    constructor
    exact hx
    triv

-- Now let's try composition.
variable (Z : Type) (g : Y → Z) (U : Set Z)

-- preimage of preimage is preimage of comp
example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by
  exact rfl


-- preimage of preimage is preimage of comp
example : g ∘ f '' S = g '' (f '' S) := by
  -- ext z
  -- constructor
  -- · rintro ⟨x, hx, rfl⟩
  --   simp only [Function.comp_apply, Set.mem_image, exists_exists_and_eq_and]
  --   use x
  -- · rintro ⟨y, ⟨x, hxS, rfl⟩,rfl⟩
  --   exact ⟨x, hxS, rfl⟩
  simp_all only [Function.comp_apply]
  unhygienic ext
  simp_all only [Set.mem_image, exists_exists_and_eq_and]

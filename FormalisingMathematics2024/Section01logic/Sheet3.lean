/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro hNT
  change True → False at hNT
  apply hNT
  trivial

example : False → ¬True := by
  intro hF
  change True → False
  intro hT
  exact hF

example : ¬False → True := by
  intro hNF
  triv

example : True → ¬False := by
  intro hT
  change False → False
  intro hF
  exact hF


example : False → ¬P := by
  intro hF
  change P → False
  intro hP
  exact hF

example : P → ¬P → False := by
  intro hP
  intro hNP
  apply hNP
  exact hP

example : P → ¬¬P := by
  intro hP
  change ¬P → False
  intro hNP
  apply hNP
  exact hP

example : (P → Q) → ¬Q → ¬P := by
  intro hPQ
  intro hNQ
  change P → False
  intro hP
  apply hPQ at hP
  apply hNQ at hP
  exact hP

example : ¬¬False → False := by
  intro hNNF
  change ¬ False → False at hNNF
  apply hNNF
  change False → False
  intro hF
  exact hF

example : ¬¬P → P := by
  intro hNNP
  change ¬P → False at hNNP
  by_contra hNP
  apply hNNP
  exact hNP

example : (¬Q → ¬P) → P → Q := by
  intro hNQNP
  intro hP
  by_contra hNQ
  apply hNQNP at hNQ
  apply hNQ at hP
  exact hP

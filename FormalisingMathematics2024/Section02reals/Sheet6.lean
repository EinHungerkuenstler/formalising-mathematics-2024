/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics2024.Solutions.Section02reals.Sheet5 -- import a bunch of previous stuff

namespace Section2sheet6

open Section2sheet3solutions Section2sheet5solutions

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in class,
so if you like you can try some of them and then watch me
solving them.

Good luck!
-/
/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tendsTo_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ 37 * a n) (37 * t) := by
    rw [tendsTo_def] at *
    intro ε hε
    specialize h (ε / 37) (by linarith)
    cases' h with N hN
    use N
    intro n hn
    specialize hN n hn
    rw [← mul_sub, abs_mul, abs_of_nonneg]
    linarith
    norm_num

/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
    rw [tendsTo_def] at *
    intro ε hε
    obtain ⟨N, hN⟩ := h (ε / c) (div_pos hε hc)
    use N
    intro n hn
    specialize hN n hn
    rw [← mul_sub, abs_mul, abs_of_pos hc]
    exact (lt_div_iff' hc).mp hN

/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
    rw [tendsTo_def] at *
    intro ε hε
    have hc1 : 0 < -c := neg_pos.mpr hc
    obtain ⟨N, hN⟩ := h (ε / (-c)) (div_pos hε hc1)
    use N
    intro n hn
    specialize hN n hn
    rw [← mul_sub, abs_mul, abs_of_neg hc]
    exact (lt_div_iff' hc1).mp hN

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
    obtain hc | rfl | hc := lt_trichotomy 0 c
    · exact tendsTo_pos_const_mul h hc
    · simpa using tendsTo_const 0
    · exact tendsTo_neg_const_mul h hc

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by
    simpa [mul_comm] using tendsTo_const_mul c h

-- another proof of this result
theorem tendsTo_neg' {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simpa using tendsTo_const_mul (-1) ha

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by
    simpa using tendsTo_add h1 h2

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsTo_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 := by
    constructor
    · intro h1
      simpa using tendsTo_sub h1 (tendsTo_const t)
    · intro h2
      simpa using tendsTo_add h2 (tendsTo_const t)


/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsTo_zero_mul_tendsTo_zero {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by
    intro ε hε
    obtain ⟨N, hN⟩ := ha ε hε
    obtain ⟨M, hM⟩ := hb 1 zero_lt_one
    use max N M
    intro n hn
    specialize hN n (le_of_max_le_left hn)
    specialize hM n (le_of_max_le_right hn)
    simpa [abs_mul] using mul_lt_mul'' hN hM

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
    rw [tendsTo_sub_lim_iff] at *
    have h : ∀ n, a n * b n - t * u = (a n - t) * (b n - u) + t * (b n - u) + (a n - t) * u := by
      intro n
      ring
    simp [h]
    have h1 : 0 = 0 + t * 0 + 0 * u := by simp
    rw [h1]
    refine' tendsTo_add (tendsTo_add _ _) _
    · exact tendsTo_zero_mul_tendsTo_zero ha hb
    · exact tendsTo_const_mul t hb
    · exact tendsTo_mul_const u ha


-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  by_contra h
  wlog h2 : s < t
  · cases' Ne.lt_or_lt h with h3 h3
    · contradiction
    · apply this _ _ _ ht hs _ h3
      exact ne_comm.mp h
  set ε := t - s with hε
  have hε: 0 < ε := sub_pos.mpr h2
  obtain ⟨X, hX⟩ := hs (ε / 2) (by linarith)
  obtain ⟨Y, hY⟩ := ht (ε / 2) (by linarith)
  set N := max X Y with hN
  specialize hX N (le_max_left X Y)
  specialize hY N (le_max_right X Y)
  rw [abs_lt] at hX hY
  linarith
end Section2sheet6

import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import Library.Tactic.ModEq
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

--# Exercise 3

--Slides 18, Page 25
example (h : ∃x : Type, ∀y : Type, (x = y)) : (∀x : Type, ∀y : Type, (x = y)) := by
  intro a b
  obtain ⟨c, hc⟩ := h
  have h1 : a = c := by rw [hc]
  have h2 : b = c := by rw [hc]
  have h3 : a = b := by rw [h1, h2]
  apply h3

--Slides 29 Part III, Page 8
example : (∃x : Type, ∀y : Type, (x = y)) → (∀v : Type, ∀w : Type, (v = w)) := by
  intro ha a b
  obtain ⟨c, hc⟩ := ha
  have h1 : a = c := by rw [hc]
  have h2 : b = c := by rw [hc]
  have h3 : a = b := by rw [h1, h2]
  apply h3

--# Exercise 4

--Exercise 5.3.6.9
example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intros t
  obtain h | h := lt_or_le t 5
  · right
    apply h
  · left
    calc
      4 < 5 := by numbers
      _ ≤ t := by rel [h]

--Example 6.1.2
example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k IH
  · -- base case
    left; dsimp[Even]; use 0; numbers
  · -- inductive step
    obtain ⟨x, hx⟩ | ⟨x, hx⟩ := IH
    · right; dsimp[Odd]; use x; rw[hx]; ring
    · left; dsimp[Even]; use x + 1; rw[hx]; ring

--Example 6.1.6

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * k ^ 2 := by rel [IH]
      _ = k ^ 2 + k * k := by ring
      _ ≥ k ^ 2 + 4 * k := by rel [hk]
      _ = k ^ 2 + 2 * k + 2 * k := by ring
      _ ≥ k ^ 2 + 2 * k + 2 * 4 := by rel [hk]
      _ = (k + 1) ^ 2 + 7 := by ring
      _ ≥ (k + 1) ^ 2 := by extra

--# Problem 2

--Exercise 5.3.6.12

example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  push_neg
  intro a
  use 2 * (a ^ 2)
  calc
    2 * a ^ 3 = 2 * a ^ 2 * a := by ring
    _ < 2 * a ^ 2 * a + 7 := by extra

--Exercise 6.1.7.2

example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k IH
  · --base case
    calc
      (1 + a) ^ 0 = 1 + 0 * a := by ring
      _ ≥ 1 + 0 * a := by extra
  · -- inductive step
    have ha' : 0 ≤ 1 + a := by addarith[ha]
    calc
      (1 + a) ^ (k + 1) = (1 + a) * (1 + a) ^ k := by ring
      _ ≥ (1 + a) * (1 + k * a) := by rel [IH]
      _ = 1 + (k + 1) * a + k * a ^ 2 := by ring
      _ ≥ 1 + (k + 1) * a := by extra

--Exercise 6.1.7.3

example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
    obtain hk | hk := IH
    · right
      calc
        5 ^ (k + 1) = 5 * 5 ^ k := by ring
        _ ≡ 5 * 1 [ZMOD 8] := by rel [hk]
        _ = 5 := by numbers
    · left
      calc
        5 ^ (k + 1) = 5 * 5 ^ k := by ring
        _ ≡ 5 * 5 [ZMOD 8] := by rel [hk]
        _ = 3 * 8 + 1 := by numbers
        _ ≡ 1 [ZMOD 8] := by extra

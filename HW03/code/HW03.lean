import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- # Exercise 3

/-2 points-/
theorem exercise2_3_6_2 {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain hx | hy := h
  calc
    x ^ 2 - 3 * x + 2 = 1 ^ 2 - 3 * 1 + 2 := by rw [hx]
    _ = 0 := by ring
  calc
    x ^ 2 - 3 * x + 2 = 2 ^ 2 - 3 * 2 + 2 := by rw [hy]
    _ = 0 := by ring

/-2 points-/
theorem exercise2_3_6_3 {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain hx | hy := h
  calc
    t ^ 2 - t - 6 = (-2) ^ 2 - (-2) - 6 := by rw [hx]
    _ = 0 := by ring
  calc
    t ^ 2 - t - 6 = (3) ^ 2 - (3) - 6 := by rw [hy]
    _ = 0 := by ring

/-2 points-/
theorem exercise2_3_6_4 {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain hx | hy := h
  calc
    x * y + 2 * x = 2 * y + 2 * 2 := by rw [hx]
    _ = 2 * y + 4 := by ring
  calc
    x * y + 2 * x = x * -2 + 2 * x := by rw [hy]
    _ = 0 := by ring
    _ = 2 * (-2) + 4 := by ring
    _ = 2 * y + 4 := by rw [hy]


-- # Exercise 4

/-2 points-/
theorem exercise2_3_6_12 {x : ℤ} : 2 * x ≠ 3 := by
  have hn := le_or_succ_le x 1
  obtain hn | hn := hn
  apply ne_of_lt
  calc
    2 * x ≤ 2 * 1 := by rel [hn]
    _ < 3 := by numbers
  apply ne_of_gt
  calc
    3 < 2 * 2 := by numbers
    _ ≤ 2 * x := by rel[hn]


-- /-2 points-/
theorem exercise2_4_5_1 {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2 * a + b = a + a + b := by ring
    _ ≤ 1 + a + b := by rel [h1]
    _ = 1 + (a + b) := by ring
    _ ≤ 1 + 3 := by rel [h2]
    _ ≤ 4 := by numbers


/-2 points-/
theorem exercise2_4_5_6 {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1, h2⟩ := h
  have ht := by
      calc
      x + y + y = x + 2 * y := by ring
      _ = 7 := by rw [h2]
  have hy := by
    calc
      y = 7 - x - y := by addarith[ht]
      _ = 7 - (x + y) := by ring
      _ = 7 - 5 := by rw [h1]
      _ = 2 := by ring
  constructor
  calc
    x = 5 - y := by addarith [h1]
    _ = 5 - 2 := by rw [hy]
    _ = 3 := by ring
  apply hy

-- # Problem 2

/-2 points-/
theorem exercise2_3_6_10 {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  sorry

/-2 points-/
theorem exercise2_3_6_14 {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  sorry

/-2 points-/
theorem exercise2_4_5_7 {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) : a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
  sorry

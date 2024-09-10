import Mathlib.Data.Real.Basic
import Library.Basic

-- Example 1.3.4
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
  calc
    w = ((3 * w + 1) / 3) - (1 / 3) := by ring
    _ = (4 / 3) - 1 / 3 := by rw [h1]
    _ = 1 := by ring


-- Example 1.3.9
example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
  calc
    a ^ 2 - a + 3 = ((a - 3) ^ 2 + 6 * a - 9) - a + 3 := by ring
    _ = (a - 3) ^ 2 + 5 * a - 6 := by ring
    _ = (a - 3) ^ 2 + 5 * ((a - 3) + 3) - 6 := by ring
    _ = (a - 3) ^ 2 + 5 * (a - 3) + 9 := by ring
    _ = (2 * b) ^ 2 + 5 * (2 * b) + 9 := by rw [h1]
    _ = 4 * b ^ 2 + 10 * b + 9 := by ring

-- Section 1.3.11 - Exercise 7
example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3)
    (h3 : c = 1) : a = 2 :=
  calc
    a = (a + 2 * b + 3 * c) - 2 * b - 3 * c := by ring
    _ = 7 - 2 * b - 3 * c := by rw [h1]
    _ = 7 - (b + 2 * c) - b - c := by ring
    _ = 7 - 3 - b - 1 := by rw [h2, h3]
    _ = - b - 2 * c + 2 * c + 3 := by ring
    _ = - (b + 2 * c) + 2 * c + 3 := by ring
    _ = - 3 + 2 * 1 + 3 := by rw [h2, h3]
    _ = 2 := by ring

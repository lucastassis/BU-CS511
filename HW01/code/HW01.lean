import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

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

import Mathlib.Data.Real.Basic
import Library.Basic
import AutograderLib

math2001_init

--Example 2.5.5
@[autograded 2]
theorem exercise3a : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6
  use 5
  numbers

--Example 2.5.6
@[autograded 2]
theorem exercise3b (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use (a + 1)
  use a
  ring

--Example 2.5.7
@[autograded 2]
theorem exercise3c {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  calc
    p = (p + p) / 2 := by ring
    _ < (p + q) / 2 := by rel [h]
  calc
    (p + q) / 2 < (q + q) / 2 := by rel [h]
    _ = q := by ring

--Exercise 3.1.10.3
@[autograded 2]
theorem exercise4a {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  use a + b
  calc
    n + m = (b + b) + (2 * a + 1) := by rw [ha, hb]
    _ = 2 * (a + b) + 1 := by ring

--Exercise 4.1.10.1
@[autograded 2]
theorem exercise4b {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by
  calc
    a ≥ -3 + 4 * 2 - 2 ^ 2 := by apply h
    _ = 1 := by numbers

--Example 4.1.3
@[autograded 2]
theorem exercise4c {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have hn : (a + b) / 2 ≥ a ∨ (a + b) / 2 ≤ b := by apply h
  obtain h1 | h2 := hn
  calc
    b = 2 * ((a + b) / 2) - a := by ring
    _ ≥ 2 * a - a := by rel [h1]
    _ = a := by ring
  calc
    a = 2 * ((a + b) / 2) - b := by ring
    _ ≤ 2 * b - b := by rel [h2]
    _ = b := by ring

--Exercise 3.2.9.2
@[autograded 2]
theorem problem2a : ¬(3 : ℤ) ∣ -10 := by
  dsimp [(.∣.)]
  apply Int.not_dvd_of_exists_lt_and_lt
  use -4
  constructor
  numbers
  numbers

--Exercise 3.2.9.5
@[autograded 2]
theorem problem2b {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  dsimp [(.∣.)] at *
  obtain ⟨k, hk⟩ := hab
  use k * (2 * (a * k) ^ 2 - (a * k) + 3)
  calc
    2 * b ^ 3 - b ^ 2 + 3 * b = b * (2 * b ^ 2 - b + 3) := by ring
    _ = a * k * (2 * (a * k) ^ 2 - (a * k) + 3) := by rw [hk]
    _ = a * (k * (2 * (a * k) ^ 2 - (a * k) + 3)) := by ring


--Exercise 3.2.9.6
@[autograded 2]
theorem problem2c {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  dsimp [(.∣.)] at *
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x ^ 3 * y
  calc
    m = l ^ 3 * y := by rw [hy]
    _ = (k * x) ^ 3 * y := by rw [hx]
    _ = k ^ 3 * x ^ 3 * y := by ring
    _ = k ^ 3 * (x ^ 3 * y) := by ring

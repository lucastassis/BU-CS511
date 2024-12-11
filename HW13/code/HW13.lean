import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init

/-# Exercise 3-/

--Exercise 10.1.5.4

section
local infix:50 "∼" => fun (x y : ℤ) ↦ y ≡ x + 1 [ZMOD 5]

example : Reflexive (· ∼ ·) := by
  sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use 0
  intro contra
  numbers at contra

example : Symmetric (· ∼ ·) := by
  sorry

example : ¬ Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  push_neg
  use 1, 2
  constructor
  · numbers
  · intro contra
    numbers at contra

example : AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  intro x y hy hx
  obtain ⟨k , hk⟩ := hy
  have hk' : y = 5 * k + (x + 1) := by addarith [hk]
  rw [hk'] at hx
  conv at hx => ring
  have h := by
    calc
      x ≡ 2 + k * 5 + x [ZMOD 5] := by rel [hx]
      _ ≡ 2 + x [ZMOD 5] := by extra
  dsimp [Int.ModEq] at h
  conv at h => ring
  apply Int.not_dvd_of_exists_lt_and_lt at h
  · contradiction
  · use -1
    constructor
    · numbers
    · numbers

example : ¬ AntiSymmetric (· ∼ ·) := by
  sorry

example : Transitive (· ∼ ·) := by
  sorry

example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 0, 1, 2
  constructor
  · numbers
  · constructor
    · numbers
    · intro contra
      numbers at contra

end

/-# Exercise 4-/

--Exercise 10.1.5.5

section
local infix:50 "∼" => fun (x y : ℤ) ↦ x + y ≡ 0 [ZMOD 3]

example : Reflexive (· ∼ ·) := by
  sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use 1
  intro contra
  numbers at contra

example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y h
  calc
    y + x = x + y := by ring
    _ ≡ 0 [ZMOD 3] := by rel [h]

example : ¬ Symmetric (· ∼ ·) := by
  sorry

example : AntiSymmetric (· ∼ ·) := by
  sorry

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use 0, 3
  constructor
  · use 1; numbers
  · constructor
    · use 1; numbers
    · numbers

example : Transitive (· ∼ ·) := by
  sorry

example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 1, 2, 1
  constructor
  · use 1; numbers
  · constructor
    · use 1; numbers
    · intro contra
      numbers at contra

end

/-# Problem 2-/

--Exercise 10.1.5.6

example : Reflexive ((· : Set ℕ) ⊆ ·) := by
  dsimp [Reflexive]
  dsimp [Set.subset_def]
  intro s a h
  apply h

example : ¬ Reflexive ((· : Set ℕ) ⊆ ·) := by
  sorry

example : Symmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : ¬ Symmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp [Symmetric]
  push_neg
  use {1}, {1, 2}
  constructor
  · dsimp [Set.subset_def]
    exhaust
  · dsimp [Set.subset_def]
    push_neg
    use 2
    constructor
    · right; numbers
    · numbers

example : AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp [AntiSymmetric]
  intros x y h1 h2
  ext a
  constructor
  · intro h; apply h1; apply h
  · intro h; apply h2; apply h

example : ¬ AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : Transitive ((· : Set ℕ) ⊆ ·) := by
  dsimp [Transitive]
  intros x y z h1 h2
  dsimp [Set.subset_def] at *
  intros a h
  apply h2
  apply h1
  apply h

example : ¬ Transitive ((· : Set ℕ) ⊆ ·) := by
  sorry

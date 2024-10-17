import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs
import Library.Tactic.ModEq
import Library.Theory.ParityModular
import AutograderLib

math2001_init

--# Exercise 3.4.5.6

@[autograded 3]
theorem exercise_3a (n : ℤ) : 5 * n ^ 2 + 3 * n + 7 ≡ 1 [ZMOD 2] := by
  mod_cases h : n % 2
  calc
    5 * n ^ 2 + 3 * n + 7 ≡ 5 * 0 ^ 2 + 3 * 0 + 7 [ZMOD 2] := by rel[h]
    _ = 1 + 3 * 2 := by numbers
    _ ≡ 1 [ZMOD 2] := by extra
  calc
    5 * n ^ 2 + 3 * n + 7 ≡ 5 * 1 ^ 2 + 3 * 1 + 7 [ZMOD 2] := by rel[h]
    _ = 1 + 7 * 2 := by numbers
    _ ≡ 1 [ZMOD 2] := by extra

--# Exercise 3.4.5.7

@[autograded 3]
theorem exercise_3b {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  mod_cases hx : x % 5
  calc
    x ^ 5 ≡ 0 ^ 5 [ZMOD 5] := by rel[hx]
    _ = 0 := by numbers
    _ ≡ x [ZMOD 5] := by rel [hx]
  calc
    x ^ 5 ≡ 1 ^ 5 [ZMOD 5] := by rel[hx]
    _ = 1 := by numbers
    _ ≡ x [ZMOD 5] := by rel [hx]
  calc
    x ^ 5 ≡ 2 ^ 5 [ZMOD 5] := by rel [hx]
    _ = 2 + 5 * 6 := by numbers
    _ ≡ 2 [ZMOD 5] := by extra
    _ ≡ x [ZMOD 5] := by rel [hx]
  calc
    x ^ 5 ≡ 3 ^ 5 [ZMOD 5] := by rel [hx]
    _ = 3 + 5 * 48 := by numbers
    _ ≡ 3 [ZMOD 5] := by extra
    _ ≡ x [ZMOD 5] := by rel [hx]
  calc
    x ^ 5 ≡ 4 ^ 5 [ZMOD 5] := by rel [hx]
    _ = 4 + 5 * 204 := by numbers
    _ ≡ 4 [ZMOD 5] := by extra
    _ ≡ x [ZMOD 5] := by rel [hx]

--# Exercise 4.4.6.2

@[autograded 3]
theorem exercise_4a (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases h : n % 5
  ·
    left
    have H :=
      calc 0 ≡ 0 + 5 * 0 [ZMOD 5] := by extra
      _ = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 5] := by rel[h]
      _ ≡ 4 [ZMOD 5] := by rel [hn]
    numbers at H
  ·
    left
    have H :=
      calc 1 ≡ 1 + 5 * 0 [ZMOD 5] := by extra
      _ = 1 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 5] := by rel[h]
      _ ≡ 4 [ZMOD 5] := by rel [hn]
    numbers at H
  ·
    left
    apply h
  ·
    right
    apply h
  ·
    left
    have H :=
      calc
        1 ≡ 1 + 5 * 3 [ZMOD 5]:= by extra
        _ = 4 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 5] := by rel[h]
        _ ≡ 4 [ZMOD 5] := by rel [hn]
    numbers at H

--# Exercise 4.4.6.3

@[autograded 3]
theorem exercise_4b : Prime 7 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 3
    constructor <;> numbers
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers

--# Example 4.5.4

@[autograded 2]
theorem problem_2a : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h
  obtain ⟨n, h⟩ := h
  obtain h1 | h2 := le_or_succ_le n 1
  · have hc :=
    calc
      2 = n ^ 2 := by rw [h]
      _ ≤ 1 ^ 2 := by rel [h1]
    numbers at hc
  · have hc :=
      calc
      2 = n ^ 2 := by rw [h]
      _ ≥ 2 ^ 2 := by rel [h2]
    numbers at hc

--# Example 4.5.5

@[autograded 2]
theorem problem_2b (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · intro h1 h2
    rw [Int.odd_iff_modEq] at h1
    rw [Int.even_iff_modEq] at h2
    have h :=
      calc 0 ≡ n [ZMOD 2] := by rel [h2]
      _ ≡ 1 [ZMOD 2] := by rel [h1]
    numbers at h
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · contradiction
    · apply h2

--# Example 4.5.6

@[autograded 2]
theorem problem_2c (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h2 :=
      calc
        1 = 1 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
        _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h2 -- contradiction!
  · have h3 :=
      calc
        1 ≡ 1 + 3 * 1 [ZMOD 3] := by extra
        _ = 2 ^ 2 := by numbers
        _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
        _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h3 -- contradiction!

import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Exhaust

math2001_init

open Set Function Nat


/-# Exercise 4-/
--Exercise 6.4.3.1

theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  obtain h | h := even_or_odd n
  · dsimp [Even] at h
    obtain ⟨k, hk⟩ := h
    rw [hk] at hn
    cancel 2 at hn
    have IH : ∃ a x, Odd x ∧ k = 2 ^ a * x  := extract_pow_two k hn
    obtain ⟨a, ha⟩ := IH
    obtain ⟨x, hx⟩ := ha
    use a + 1
    use x
    obtain ⟨h1, h2⟩ := hx
    constructor
    · apply h1
    · rw [hk, h2]; ring
  · use 0
    use n
    constructor
    · apply h
    · ring

/-# Exercise 5-/

------------------------------------------------------------------------------------
--Exercise 9.1.10.1

example : 4 ∈ {a : ℚ | a < 3} := by
  sorry

example : 4 ∉ {a : ℚ | a < 3} := by
  dsimp
  numbers

------------------------------------------------------------------------------------
--Exercise 9.1.10.2

example : 6 ∈ {n : ℕ | n ∣ 42} := by
  dsimp
  use 7
  numbers

example : 6 ∉ {n : ℕ | n ∣ 42} := by
  sorry

------------------------------------------------------------------------------------
--Exercise 9.1.10.3

example : 8 ∈ {k : ℤ | 5 ∣ k} := by
  sorry

example : 8 ∉ {k : ℤ | 5 ∣ k} := by
  dsimp
  apply Int.not_dvd_of_exists_lt_and_lt
  use 1
  constructor
  numbers
  numbers


/-# Exercise 6-/
------------------------------------------------------------------------------------
--Exercise 9.1.10.6

example : {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x} := by
  dsimp [Set.subset_def]
  intros a ha
  obtain ⟨k, hk⟩ := ha
  use 4 * k
  rw [hk]
  ring

example : {a : ℕ | 20 ∣ a} ⊈ {x : ℕ | 5 ∣ x} := by
  sorry

------------------------------------------------------------------------------------
--Exercise 9.1.10.7

example : {a : ℕ | 5 ∣ a} ⊆ {x : ℕ | 20 ∣ x} := by
  sorry

example : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  dsimp [Set.subset_def]
  push_neg
  use 5
  constructor
  · use 1; numbers
  · apply Nat.not_dvd_of_exists_lt_and_lt
    use 0
    constructor
    numbers
    numbers

------------------------------------------------------------------------------------
--Exercise 9.2.8.5

example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  dsimp [Set.subset_def]
  intros a ha
  constructor
  · dsimp [Int.ModEq] at *
    obtain ⟨k, hk⟩ := ha
    have hk' : a = 10 * k + 7 := by addarith [hk]
    use 5 * k + 3
    rw [hk']
    ring
  · dsimp [Int.ModEq] at *
    obtain ⟨k, hk⟩ := ha
    have hk' : a = 10 * k + 7 := by addarith [hk]
    use 2 * k + 1
    rw [hk']
    ring

/-# Problem 2-/
--Exercise 9.2.8.6
example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  dsimp [Set.subset_def]
  intro n h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨b, hb⟩ := h1
  obtain ⟨a, ha⟩ := h2
  dsimp [· ∣ ·]
  use -3 * a + 2 * b
  calc
    n = -15 * n + 16 * n := by ring
    _ = -15 * (8 * a) + 16 * n := by rw [ha]
    _ = -15 * (8 * a) + 16 * (5 * b) := by rw [hb]
    _ = 40 * (-3 * a + 2 * b) := by ring

--Exercise 9.3.6.1
def r (s : Set ℕ) : Set ℕ := s ∪ {3}

example : ¬ Injective r := by
  dsimp [Injective]
  push_neg
  use ∅, {3}
  constructor
  · dsimp [r]
    ext n
    dsimp
    exhaust
  · ext
    push_neg
    use 3
    dsimp
    exhaust

import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int

--# Exercise 3

--Exercise 6.2.7.1
def c : ℕ → ℤ
  | 0 => 7
  | n + 1 => 3 * c n - 10

example (n : ℕ) : Odd (c n) := by
  simple_induction n with k hk
  · -- base case
    use 3; rw [c]; numbers
  · -- induction step
    dsimp [Odd] at *
    obtain ⟨x, hx⟩ := hk
    use 3 * x - 4
    rw [c]; rw [hx]; ring

--Exercise 6.2.7.2
example (n : ℕ) : c n = 2 * 3 ^ n + 5 := by
  simple_induction n with k hk
  · -- base step
    rw [c]; numbers
  · -- induction step
    rw [c]; rw [hk]; ring

--Exercise 6.2.7.3
def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2

example (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  simple_induction n with k hk
  · -- base case
    rw [y]; numbers
  · -- induction step
    rw [y]; rw [hk]; ring

--# Exercise 4

--Exercise 6.3.6.1
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * b (n + 1) - 6 * b n

example (n : ℕ) : b n = 3 ^ n - 2 ^ n := by
  two_step_induction n with k IH1 IH2
  · rw [b]; numbers
  · rw [b]; numbers
  · rw [b]; rw [IH1, IH2]; ring

--Exercise 6.3.6.2
def c' : ℕ → ℤ
  | 0 => 3
  | 1 => 2
  | n + 2 => 4 * c' n

example (n : ℕ) : c' n = 2 * 2 ^ n + (-2) ^ n := by
  two_step_induction n with k IH1 IH2
  · rw [c']; numbers
  · rw [c']; numbers
  · rw [c']; rw [IH1]; ring

--Exercise 6.3.6.3
def t : ℕ → ℤ
  | 0 => 5
  | 1 => 7
  | n + 2 => 2 * t (n + 1) - t n

example (n : ℕ) : t n = 2 * n + 5 := by
  two_step_induction n with k IH1 IH2
  · rw [t]; numbers
  · rw [t]; numbers
  · rw [t]; rw [IH1, IH2]; ring

--# Problem 2

--Exercise 6.3.6.5
def s : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 2 * s (n + 1) + 3 * s n

example (m : ℕ) : s m ≡ 2 [ZMOD 5] ∨ s m ≡ 3 [ZMOD 5] := by
  have H : ∀ n : ℕ, 0 ≤ n → (s n ≡ 2 [ZMOD 5] ∧ s (n + 1) ≡ 3 [ZMOD 5]) ∨ (s n ≡ 3 [ZMOD 5] ∧ s (n + 1) ≡ 2 [ZMOD 5])
  · intros n hn
    induction_from_starting_point n, hn with k hk IH
    · left
      constructor
      · rw [s]; extra
      · rw [s]; extra
    · obtain ⟨IH1, IH2⟩ | ⟨IH1, IH2⟩ :=  IH
      · right
        constructor
        · apply IH2
        · calc
            s (k + 2) = 2 * s (k + 1) + 3 * s k := by rw [s]
            _ ≡ 2 * 3 + 3 * 2 [ZMOD 5] := by rel [IH1, IH2]
            _ = 5 * 2 + 2 := by ring
            _ ≡ 2 [ZMOD 5] := by extra
      · left
        constructor
        · apply IH2
        · calc
            s (k + 2) = 2 * s (k + 1) + 3 * s k := by rw [s]
            _ ≡ 2 * 2 + 3 * 3 [ZMOD 5] := by rel [IH1, IH2]
            _ = 5 * 2 + 3 := by ring
            _ ≡ 3 [ZMOD 5] := by extra
  have hm : 0 ≤ m := by extra
  obtain ⟨H1, H2⟩ | ⟨H1, H2⟩ := H m hm
  · left; apply H1
  · right; apply H1

--Exercise 6.3.6.7
def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

example : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  dsimp
  use 7
  intros n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
  · dsimp [r]; numbers
  · dsimp [r]; numbers
  · calc
      r (k + 2) = 2 * r (k + 1) + r k := by rw [r]
      _ ≥ 2 * 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
      _ = 2 ^ (k + 2) + 2 ^ k := by ring
      _ ≥ 2 ^ (k + 2) := by extra

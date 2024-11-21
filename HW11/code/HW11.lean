import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Theory.InjectiveSurjective
import Library.Tactic.ModEq

math2001_init
set_option pp.funBinderTypes true

open Function

/-# Exercise 3-/

--Exercise 8.3.10.2
def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := (x - 1) / 5

example : Inverse u v := by
  dsimp [Inverse]
  constructor
  · ext x
    dsimp [u, v]
    ring
  · ext x
    dsimp [u, v]
    ring

--Exercise 8.3.10.3
example {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  dsimp [Injective] at *
  intros a1 a2 ha
  have : f a1 = f a2 := hg ha
  have : a1 = a2 := hf this
  apply this

--Exercise 8.3.10.4
example {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  dsimp [Surjective] at *
  choose u hu using hf
  choose w hw using hg
  intros x
  have hw' : g (w x) = x := hw x
  have hu' : f (u (w x)) = w x := hu (w x)
  use u (w x)
  rw [hu']
  apply hw'

/-# Exercise 4-/

--Exercise 8.4.10.1
example : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r - s)) := by
  rw [bijective_iff_exists_inverse]
  use fun (a, b) ↦ (a + b, a)
  constructor
  · ext ⟨r, s⟩
    dsimp
    ring
  · ext ⟨a, b⟩
    dsimp
    ring

--Exercise 8.4.10.2.1
example : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Injective]
  push_neg
  use (0, 0), (2, 1)
  constructor
  · numbers
  · numbers

--Exercise 8.4.10.2.2
example : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Surjective]
  intro a
  use (3 * a + 1, a)
  dsimp
  ring

/-# Problem 2-/

--Exercise 8.3.10.5
example {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  dsimp [Surjective] at *
  choose g hg using hf
  use g
  ext x
  calc
    (f ∘ g) x = f (g x) := by rfl
    _ = x := by apply hg
    _ = id x := by rfl

--Exercise 8.3.10.7
example {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by
  dsimp [Inverse] at *
  obtain ⟨h11, h12⟩ := h1
  obtain ⟨h21, h22⟩ := h2
  ext x
  calc
    g1 x = id (g1 x) := by rfl
    _ = (g2 ∘ f) (g1 x) := by rw [h21]
    _ = g2 (f (g1 x)) := by rfl
    _ = g2 ((f ∘ g1) x) := by rfl
    _ = g2 (id x) := by rw [h12]
    _ = g2 x := by rfl

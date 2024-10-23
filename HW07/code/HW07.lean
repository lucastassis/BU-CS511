import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

--Exercise 5.1.7.6

@[autograded 2]
example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro hl
    constructor
    obtain ⟨p, r⟩ := hl
    have hq : Q := h1 p
    apply hq
    obtain ⟨p, r⟩ := hl
    apply r
  · intro hr
    constructor
    obtain ⟨q, r⟩ := hr
    have hp : P := h2 q
    apply hp
    obtain ⟨q, r⟩ := hr
    apply r

--Exercise 5.1.7.8

@[autograded 2]
example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  · intro hl
    obtain hp | hq := hl
    right; apply hp
    left; apply hq
  · intro hr
    obtain hq | hp := hr
    right; apply hq
    left; apply hp

--Exercise 5.1.7.9

@[autograded 2]
example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  · intro hl
    constructor
    intro hp
    have H : P ∨ Q := by left; apply hp
    contradiction
    intro hq
    have H : P ∨ Q := by right; apply hq
    contradiction
  · intro hr
    obtain ⟨hp', hq'⟩ := hr
    intro hg
    obtain hp | hq := hg
    contradiction
    contradiction

--Exercise 5.1.7.11

@[autograded 2]
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · intro hl
    obtain ⟨a, ha⟩ := hl
    have h1 : P a ↔ Q a := h a
    obtain ⟨hpa, hqa⟩ := h1
    have h2 : Q a := hpa ha
    use a; apply h2
  · intro hr
    obtain ⟨a, ha⟩ := hr
    have h1 : P a ↔ Q a := h a
    obtain ⟨hpa, hqa⟩ := h1
    have h2 : P a := hqa ha
    use a; apply h2

--Exercise 5.1.7.12

@[autograded 2]
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  · intro hl
    obtain ⟨a, b, h⟩ := hl
    use b; use a; apply h
  · intro hr
    obtain ⟨b, a , h⟩ := hr
    use a; use b; apply h

--Exercise 5.1.7.13

@[autograded 2]
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  · intros hl b a
    have h := hl a b
    apply h
  · intros hr a b
    have h := hr b a
    apply h

--Exercise 5.1.7.14

@[autograded 3]
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · intros hl
    obtain ⟨hq, q⟩ := hl
    obtain ⟨a, ha⟩ := hq
    use a; constructor; apply ha; apply q
  · intros hr
    obtain ⟨a, hq⟩ := hr
    obtain ⟨pa, q⟩ := hq
    constructor
    use a; apply pa
    apply q

--Exercise 5.2.7.2

@[autograded 3]
example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  constructor
  · intros hl hq
    by_cases hp : P
    · apply hp
    · have hq : ¬Q := hl hp; contradiction
  · intros hr hp
    by_cases hq : Q
    · have hp : P := hr hq; contradiction
    · apply hq

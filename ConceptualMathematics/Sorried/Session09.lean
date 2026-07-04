import ConceptualMathematics.Sorried.Article2
import Mathlib.CategoryTheory.Retract
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise 9.1 (p. 99)
-/
namespace Ex9_1

-- working in the category of types, so 𝒞 = Type and ⟶ is →
def AtLeastOne (A B : Type) := Nonempty (A → B)
def Point (Y : Type) := Unit → Y
theorem AtLeastOne_of_nonempty (A B : Type) : AtLeastOne A B ↔ ¬ (Nonempty (Point A) ∧ IsEmpty (Point B)) := by
  constructor
  · intro h
    rw [AtLeastOne] at h
    push Not
    intro h2
    rw [Point] at h2 ⊢
    obtain ⟨f⟩ := h2
    obtain ⟨g⟩ := h
    exact ⟨g ∘ f⟩
  · push Not
    intro h1
    rw [AtLeastOne]
    by_cases hA : Nonempty (Point A)
    · have := h1 hA
      obtain ⟨b⟩ := this
      rw [Point] at b
      let f : A → B := by
        intro a
        exact b () -- () is unit
      use f
    · let f : A → B := by
        intro a
        exfalso
        rw [Point] at hA
        simp only [nonempty_fun, not_isEmpty_of_nonempty, false_or, not_nonempty_iff] at hA
        obtain ⟨f⟩ := hA
        exact f a
      use f

end Ex9_1
/-!
Exercise 9.2 (p. 100)
-/
namespace Ex9_2

variable {𝒞 : Type u} [Category.{v, u} 𝒞] {A B C : 𝒞}

example : Retract A A := ⟨
  𝟙 A,
  𝟙 A,
  by simp
⟩

example (h₁ : Retract A B) (h₂ : Retract B C) : Retract A C := ⟨
  h₂.i ⊚ h₁.i,
  h₁.r ⊚ h₂.r,
  by rw [← Category.assoc, Category.assoc h₁.i, h₂.retract, Category.comp_id, h₁.retract]
⟩

end Ex9_2

/-!
Splitting
-/
structure Splitting {𝒞 : Type u} [Category.{v, u} 𝒞] {B : 𝒞}
    (e : B ⟶ B) [IsIdempotent e] where
  A : 𝒞
  s : A ⟶ B
  r : B ⟶ A
  rs : r ⊚ s = 𝟙 A
  sr : s ⊚ r = e

/-!
Exercise 9.3 (p. 102)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] {B : 𝒞}
    {e : B ⟶ B} [IsIdempotent e]
    (hsr : Splitting e) (hsr' : Splitting e)
    : Iso hsr.A hsr'.A := ⟨
  hsr'.r ⊚ hsr.s,
  hsr.r ⊚ hsr'.s,
  by
    rw [← Category.assoc, Category.assoc hsr.s, hsr'.sr]
    simp only [← hsr.sr, Category.assoc]
    rw [hsr.rs, Category.comp_id, hsr.rs],
  by
    rw [← Category.assoc, Category.assoc hsr'.s, hsr.sr]
    simp only [← hsr'.sr, Category.assoc]
    rw [hsr'.rs, Category.comp_id, hsr'.rs]
⟩

end CM

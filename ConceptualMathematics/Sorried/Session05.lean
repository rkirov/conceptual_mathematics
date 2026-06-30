import ConceptualMathematics.Sorried.Article1
import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise 5.1 (p. 70)
-/
example {A B C : Type} {f : A ⟶ B} {h : A ⟶ C}
    (hg : ∃ g : B ⟶ C, h = g ⊚ f)
    : ∀ a₁ a₂ : Point A, f ⊚ a₁ = f ⊚ a₂ → h ⊚ a₁ = h ⊚ a₂ :=
  sorry

example {A B C : Type} {f : A ⟶ B} {h : A ⟶ C}
    (H : ∀ a₁ a₂ : Point A, f ⊚ a₁ = f ⊚ a₂ → h ⊚ a₁ = h ⊚ a₂)
    (hfsurj : Function.Surjective f)
    : ∃ g : B ⟶ C, h = g ⊚ f :=
  sorry

open Classical in
example {A B C : Type} [Nonempty C] {f : A ⟶ B} {h : A ⟶ C}
    (H : ∀ a₁ a₂ : Point A, f ⊚ a₁ = f ⊚ a₂ → h ⊚ a₁ = h ⊚ a₂)
    : ∃ g : B ⟶ C, h = g ⊚ f :=
  sorry

/-!
IsConstantMap
-/
def IsConstantMap {A C : Type} (h : A ⟶ C) :=
  ∃ (f : A ⟶ One) (g : One ⟶ C), h = g ⊚ f

/-!
Exercise 5.2 (p. 71)
-/
example {A B C : Type} {g : B ⟶ C} {h : A ⟶ C}
    (hf : ∃ f : A ⟶ B, g ⊚ f = h)
    : ∀ a : A, ∃ b : B, h a = g b :=
  sorry

example {A B C : Type} {g : B ⟶ C} {h : A ⟶ C}
    (H : ∀ a : A, ∃ b : B, h a = g b)
    : ∃ f : A ⟶ B, g ⊚ f = h :=
  sorry

/-!
Exercise 5.3 (p. 75)
-/
namespace Ex5_3

inductive A
  | a₁₁ | a₁₂ | a₁₃ | a₁₄ | a₂₁ | a₂₂
  deriving Fintype

inductive B
  | b₁ | b₂
  deriving Fintype

def f : A ⟶ B
  | A.a₁₁ => B.b₁
  | A.a₁₂ => B.b₁
  | A.a₁₃ => B.b₁
  | A.a₁₄ => B.b₁
  | A.a₂₁ => B.b₂
  | A.a₂₂ => B.b₂

def s₁ : B ⟶ A :=
  sorry

example : f ⊚ s₁ = 𝟙 B :=
  sorry

def s₂ : B ⟶ A :=
  sorry

example : f ⊚ s₂ = 𝟙 B :=
  sorry

def s₃ : B ⟶ A :=
  sorry

example : f ⊚ s₃ = 𝟙 B :=
  sorry

def s₄ : B ⟶ A :=
  sorry

example : f ⊚ s₄ = 𝟙 B :=
  sorry

def s₅ : B ⟶ A :=
  sorry

example : f ⊚ s₅ = 𝟙 B :=
  sorry

def s₆ : B ⟶ A :=
  sorry

example : f ⊚ s₆ = 𝟙 B :=
  sorry

def s₇ : B ⟶ A :=
  sorry

example : f ⊚ s₇ = 𝟙 B :=
  sorry

def s₈ : B ⟶ A :=
  sorry

example : f ⊚ s₈ = 𝟙 B :=
  sorry

end Ex5_3

end CM

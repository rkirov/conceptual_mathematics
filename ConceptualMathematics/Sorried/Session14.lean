import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

namespace Ex14_1_3

variable (X Y : Type) (α : End X) (β : End Y)
         (f : X ⟶ Y) (hf_comm : f ⊚ α = β ⊚ f)

/-!
Exercise 14.1 (p. 170)
-/
example (x₁ x₂ : X) (y₁ y₂ : Y)
    (hy₁ : y₁ = f x₁) (hy₂ : y₂ = f x₂) (hα : α x₁ = α x₂)
    : β y₁ = β y₂ :=
  sorry

/-!
Exercise 14.2 (p. 170)
-/
example (x₁ x₂ : X) (y₁ y₂ : Y)
    (hy₁ : y₁ = f x₁) (hy₂ : y₂ = f x₂) (h : x₂ = (α ^ 5) x₁)
    : y₂ = (β ^ 5) y₁ :=
  sorry

open Function
lemma _root_.pow_comm {X Y : Type} (f : X ⟶ Y)
    (α : End X) (β : End Y)
    (hf_comm : f ⊚ α = β ⊚ f) (n : ℕ)
    : f ⊚ (α^[n]) = (β^[n]) ⊚ f :=
  have hf_semiconj : Semiconj f α β :=
    semiconj_iff_comp_eq.mpr hf_comm
  have hf_pow_semiconj : Semiconj f (α^[n]) (β^[n]) :=
    Semiconj.iterate_right hf_semiconj n
  semiconj_iff_comp_eq.mp hf_pow_semiconj

example (x₁ x₂ : X) (y₁ y₂ : Y)
    (hy₁ : y₁ = f x₁) (hy₂ : y₂ = f x₂) (h : x₂ = (α ^ 5) x₁)
    : y₂ = (β ^ 5) y₁ :=
  sorry

/-!
Exercise 14.3 (p. 170)
-/
example (x : X) (y : Y) (hy : y = f x) (h : α x = x) : β y = y :=
  sorry

end Ex14_1_3

/-!
Exercise 14.4 (p. 171)
-/
namespace Ex14_4

inductive X
  | x₁ | x₂
  deriving DecidableEq

inductive Y
  | y₁

def α : X ⟶ X :=
  sorry

def β : Y ⟶ Y :=
  sorry

variable (f : X ⟶ Y) (hf_comm : f ⊚ α = β ⊚ f)

example : ¬(α X.x₁ = X.x₁) ∧ β (f X.x₁) = f X.x₁ :=
  sorry

end Ex14_4

/-!
Exercise 14.5 (p. 171)
-/
namespace Ex14_5

example (X Y : Type) (α : End X) (β : End Y)
    (f : X ⟶ Y) (hf_comm : f ⊚ α = β ⊚ f)
    (x : X) (y : Y)
    (hy : y = f x) (h : (α ^ 4) x = x)
    : (β ^ 4) y = y :=
  sorry

inductive X
  | x₁ | x₂ | x₃ | x₄

inductive Y
  | y₁ | y₂

def α : End X :=
  sorry

def β : End Y :=
  sorry

def f : X ⟶ Y :=
  sorry

example (x : X) (y : Y) (hy : y = f x)
    : (α ^ 4) x = x ∧ ¬((α ^ 2) x = x)
      ∧
      (β ^ 2) y = y ∧ ¬(β y = y) :=
  sorry

end Ex14_5

end CM

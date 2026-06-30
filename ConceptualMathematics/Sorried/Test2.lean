import ConceptualMathematics.Sorried.Article3
import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Problem Test 2.1 (p. 204)
-/
example (X Y : SetWithEndomap) (f : X ⟶ Y) :
    (∃ x : X.carrier, X.toEnd x = x) →
    (∃ y : Y.carrier, Y.toEnd y = y) :=
  sorry

/-!
Problem Test 2.2 (p. 204)
-/
namespace Test2_2

inductive A₁
  | a | b

inductive D₁
  | p | q | r

def G₁ : IrreflexiveGraph := {
  carrierA := A₁
  carrierD := D₁
  toSrc := fun
    | A₁.a => D₁.p
    | A₁.b => D₁.q
  toTgt := fun
    | A₁.a => D₁.r
    | A₁.b => D₁.r
}

inductive A₂
  | c | d

inductive D₂
  | v | w

def G₂ : IrreflexiveGraph := {
  carrierA := A₂
  carrierD := D₂
  toSrc := fun
    | A₂.c => D₂.w
    | A₂.d => D₂.v
  toTgt := fun
    | A₂.c => D₂.w
    | A₂.d => D₂.w
}

def f₁ : G₁ ⟶ G₂ :=
  sorry

def f₂ : G₁ ⟶ G₂ :=
  sorry

def f₃ : G₁ ⟶ G₂ :=
  sorry

def f₄ : G₁ ⟶ G₂ :=
  sorry

end Test2_2

/-!
Problem Test 2.3 (p. 204)
-/
namespace Test2_3

inductive X
  | x₁ | x₂ | x₃

def α : End X :=
  sorry

example : α ^ 2 = α ^ 3 ∧ α ≠ α ^ 2 :=
  sorry

example : α ^ 2 = α ^ 3 ∧ α ≠ α ^ 2 :=
  sorry

end Test2_3

end CM

import ConceptualMathematics.Article2
import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Problem Quiz.1 (p. 108)
-/
namespace Quiz_1

inductive A
  | a
  deriving Fintype

inductive B
  | b₁ | b₂
  deriving Fintype

def f : A ⟶ B :=
  sorry

def r : B ⟶ A :=
  sorry

example : IsRetraction f :=
  sorry

example : ¬(IsSection f) :=
  sorry

end Quiz_1

/-!
Problem Quiz.2 (p. 108)
-/
namespace Quiz_2

variable {𝒞 : Type u} [Category.{v, u} 𝒞] {C D : 𝒞}
         (p : C ⟶ D) (q : D ⟶ C) (hpq : p ⊚ q ⊚ p = p)

example : IsIdempotent (p ⊚ q) :=
  sorry

example : IsIdempotent (q ⊚ p) :=
  sorry

end Quiz_2

/-!
Problem Quiz_2* (p. 108)
-/
namespace «Quiz_2*»

variable {𝒞 : Type u} [Category.{v, u} 𝒞] {C D : 𝒞}
         (p : C ⟶ D) (q : D ⟶ C) (hpq : p ⊚ q ⊚ p = p)

example : ∃ q', p ⊚ q' ⊚ p = p ∧ q' ⊚ p ⊚ q' = q' :=
  sorry

end «Quiz_2*»

/-!
Problem Quiz_1* (p. 108)
-/
namespace «Quiz_1*»

abbrev A := ℕ
abbrev B := ℝ

def f : A ⟶ B :=
  sorry

noncomputable def r : B ⟶ A :=
  sorry

example : IsRetraction f :=
  sorry

example : ¬(IsSection f) :=
  sorry

end «Quiz_1*»

end CM

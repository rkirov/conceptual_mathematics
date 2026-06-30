import ConceptualMathematics.Sorried.Article2
import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise 9.1 (p. 99)
-/
/-!
Exercise 9.2 (p. 100)
-/
namespace Ex9_2

variable {𝒞 : Type u} [Category.{v, u} 𝒞] {A B C : 𝒞}

example : Retract A A :=
  sorry

example (h₁ : Retract A B) (h₂ : Retract B C) : Retract A C :=
  sorry

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
    : Iso hsr.A hsr'.A :=
  sorry

end CM

import ConceptualMathematics.Sorried.Article2
import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Problem Test 1.1 (p. 119)
-/
namespace Test1_1

inductive A
  | Mara | Aurelio | Andrea
  deriving Fintype

def f : A ⟶ A :=
  sorry

def finv : A ⟶ A :=
  sorry

example : IsIso f :=
  sorry

def e : A ⟶ A :=
  sorry

instance : IsIdempotent e :=
  sorry

inductive B
  | b
  deriving Fintype

def r : A ⟶ B :=
  sorry

def s : B ⟶ A :=
  sorry

example : r ⊚ s = 𝟙 B ∧ s ⊚ r = e :=
  sorry

end Test1_1

/-!
Problem Test 1.2 (p. 119)
-/
example (f : ℝ ⟶ ℝ) (hf : ∀ x : ℝ, f x = 4 * x - 7)
    : ∃ g, ∀ x : ℝ, (g ⊚ f) x = x ∧ (f ⊚ g) x = x :=
  sorry

end CM

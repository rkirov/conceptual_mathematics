import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
open CategoryTheory
open Limits
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise 28.1 (p. 298)
-/
namespace Ex28_1_a

def A : Pointed :=
  sorry

example [HasInitial Pointed] [HasBinaryProduct (⊥_ Pointed) A] :
    IsEmpty ((⊥_ Pointed) ≅ (⊥_ Pointed) ⨯ A) :=
  sorry

end Ex28_1_a

namespace Ex28_1_b

def A : Pointed :=
  sorry

def B₁ : Pointed :=
  sorry

def B₂ : Pointed :=
  sorry

example [HasBinaryProduct A B₁] [HasBinaryProduct A B₂]
    [HasBinaryCoproduct (A ⨯ B₁) (A ⨯ B₂)]
    [HasBinaryCoproduct B₁ B₂] [HasBinaryProduct A (B₁ ⨿ B₂)] :
    IsEmpty ((A ⨯ B₁) ⨿ (A ⨯ B₂) ≅ A ⨯ (B₁ ⨿ B₂)) :=
  sorry

end Ex28_1_b

/-!
Exercise 28.2 (p. 298)
-/
namespace Ex28_2

def A : Pointed :=
  sorry

def B : Pointed :=
  sorry

example [HasZeroMorphisms Pointed]
    [HasBinaryProduct A B] [HasBinaryCoproduct A B] :
    IsEmpty (IsIso
        (coprod.desc (prod.lift (𝟙 A) 0) (prod.lift 0 (𝟙 B)))) :=
  sorry

end Ex28_2

end CM

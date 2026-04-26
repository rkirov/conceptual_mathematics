import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise 3.1 (p. 36)
-/
namespace Ex3_1

variable {𝒞 : Type u} [Category.{v, u} 𝒞] {A B C : 𝒞}
         (f : A ⟶ B) (g : B ⟶ A) (h : A ⟶ C) (k : C ⟶ B)

#check k ⊚ h ⊚ g ⊚ f

#check f ⊚ g

#check g ⊚ f ⊚ g ⊚ k ⊚ h

end Ex3_1

end CM

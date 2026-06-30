import ConceptualMathematics.Sorried.Article4
import Mathlib
open CategoryTheory
open Limits
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Problem Test 3.1 (p. 299)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] [HasTerminal 𝒞] (X : 𝒞) :
    ∀ f : ⊤_ 𝒞 ⟶ X, ∃! g : X ⟶ ⊤_ 𝒞, g ⊚ f = 𝟙 (⊤_ 𝒞) :=
  sorry

/-!
Problem Test 3.2 (p. 299)
-/
noncomputable
example {𝒞 : Type u} [Category.{v, u} 𝒞] [HasTerminal 𝒞]
    (C : 𝒞) (Cx1 : BinaryFan C (⊤_ 𝒞)) (lim_Cx1 : IsLimit Cx1) :
    Cx1.pt ≅ C :=
  sorry

/-!
Problem Test 3.3 (p. 299)
-/
namespace Test3_3

def AAA : IrreflexiveGraph :=
  sorry

open IrreflexiveGraph in
example
    (coneAAA : Fan (fun _ ↦ A : Fin 3 → IrreflexiveGraph))
    (limitAAA : IsLimit coneAAA)
    (coconeA6D : Cofan (fun
      | 0 => A | 1 => D | 2 => D | 3 => D | 4 => D | 5 => D | 6 => D :
        Fin 7 → IrreflexiveGraph))
    (colimitA6D : IsColimit coconeA6D) :
  coneAAA.pt ≅ coconeA6D.pt :=
  sorry

end Test3_3

end CM

import ConceptualMathematics.Article3
import ConceptualMathematics.Article4
import ConceptualMathematics.Session21
import Mathlib
open CategoryTheory
open Limits
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise 24.1 (p. 266)
-/
theorem uniqueness_of_sums
    {𝒞 : Type u} [Category.{v, u} 𝒞] (B₁ B₂ : 𝒞)
    (coconeS coconeT : BinaryCofan B₁ B₂)
    (sumS : IsColimit coconeS) (sumT : IsColimit coconeT)
    : ∃! f : coconeS.pt ⟶ coconeT.pt,
        (coconeT.ι.app ⟨WalkingPair.left⟩ =
            f ⊚ coconeS.ι.app ⟨WalkingPair.left⟩ ∧
         coconeT.ι.app ⟨WalkingPair.right⟩ =
            f ⊚ coconeS.ι.app ⟨WalkingPair.right⟩)
        ∧ IsIso f :=
  sorry

theorem uniqueness_of_sums'
    {𝒞 : Type u} [Category.{v, u} 𝒞] (B₁ B₂ S T : 𝒞)
    (j₁ : B₁ ⟶ S) (j₂ : B₂ ⟶ S)
    (hS : ∀ (X : 𝒞) (f₁ : B₁ ⟶ X) (f₂ : B₂ ⟶ X),
        (∃! f : S ⟶ X, f₁ = f ⊚ j₁ ∧ f₂ = f ⊚ j₂))
    (k₁ : B₁ ⟶ T) (k₂ : B₂ ⟶ T)
    (hT : ∀ (X : 𝒞) (f₁ : B₁ ⟶ X) (f₂ : B₂ ⟶ X),
        (∃! f : T ⟶ X, f₁ = f ⊚ k₁ ∧ f₂ = f ⊚ k₂))
    : Nonempty (S ≅ T) :=
  sorry

/-!
Exercise 24.2 (p. 267)
-/
namespace Ex24_2

def IG2 : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 2
  toSrc := fun x ↦ x
  toTgt := fun x ↦ x
}

open IrreflexiveGraph in
noncomputable
example {sumDD prod2D : IrreflexiveGraph}
    (j₁ : D ⟶ sumDD) (j₂ : D ⟶ sumDD)
    (h_sumDD : ∀ (X : IrreflexiveGraph) (f₁ : D ⟶ X) (f₂ : D ⟶ X),
        (∃! f : sumDD ⟶ X, f₁ = f ⊚ j₁ ∧ f₂ = f ⊚ j₂))
    (p₁ : prod2D ⟶ IG2) (p₂ : prod2D ⟶ D)
    (h_prod2D : ∀ (Y : IrreflexiveGraph) (g₁ : Y ⟶ IG2) (g₂ : Y ⟶ D),
        (∃! g : Y ⟶ prod2D, g₁ = p₁ ⊚ g ∧ g₂ = p₂ ⊚ g))
    : sumDD ≅ prod2D :=
  sorry

open IrreflexiveGraph in
noncomputable
example {prodDD : IrreflexiveGraph}
    (p₁ : prodDD ⟶ D) (p₂ : prodDD ⟶ D)
    (h_prodDD : ∀ (Y : IrreflexiveGraph) (g₁ : Y ⟶ D) (g₂ : Y ⟶ D),
        (∃! g : Y ⟶ prodDD, g₁ = p₁ ⊚ g ∧ g₂ = p₂ ⊚ g))
    : prodDD ≅ D :=
  sorry

open IrreflexiveGraph in
noncomputable
example {prodAD sumDD : IrreflexiveGraph}
    (p₁ : prodAD ⟶ A) (p₂ : prodAD ⟶ D)
    (h_prodAD : ∀ (Y : IrreflexiveGraph) (g₁ : Y ⟶ A) (g₂ : Y ⟶ D),
        (∃! g : Y ⟶ prodAD, g₁ = p₁ ⊚ g ∧ g₂ = p₂ ⊚ g))
    (j₁ : D ⟶ sumDD) (j₂ : D ⟶ sumDD)
    (h_sumDD : ∀ (X : IrreflexiveGraph) (f₁ : D ⟶ X) (f₂ : D ⟶ X),
        (∃! f : sumDD ⟶ X, f₁ = f ⊚ j₁ ∧ f₂ = f ⊚ j₂))
    : prodAD ≅ sumDD :=
  sorry

end Ex24_2

end CM

import ConceptualMathematics.Article3
import ConceptualMathematics.Article4
import Mathlib
open CategoryTheory
open Limits
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise 22.1 (p. 250)
-/
open IrreflexiveGraph in
example
    (P B₁ B₂ : IrreflexiveGraph) (p₁ : P ⟶ B₁) (p₂ : P ⟶ B₂)
    -- Satisfies fragment of definition of product for X = A
    (hA : ∀ (fAP₁ : A ⟶ B₁) (fAP₂ : A ⟶ B₂),
        ∃! fAP : A ⟶ P, p₁ ⊚ fAP = fAP₁ ∧ p₂ ⊚ fAP = fAP₂)
    -- Satisfies fragment of definition of product for X = D
    (hD : ∀ (fDP₁ : D ⟶ B₁) (fDP₂ : D ⟶ B₂),
        ∃! fDP : D ⟶ P, p₁ ⊚ fDP = fDP₁ ∧ p₂ ⊚ fDP = fDP₂)
    : ∀ (X : IrreflexiveGraph) (f₁ : X ⟶ B₁) (f₂ : X ⟶ B₂),
        ∃! f : X ⟶ P, p₁ ⊚ f = f₁ ∧ p₂ ⊚ f = f₂ :=
  sorry

/-!
Exercise 22.2 (p. 252)
-/
namespace Ex22_2

abbrev A₂ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 3
  toSrc := fun
    | 0 => 0
    | 1 => 1
  toTgt := fun
    | 0 => 1
    | 1 => 2
}

def FigA₂ (X : IrreflexiveGraph) := A₂ ⟶ X

def FigA₂.IsSingular {X : IrreflexiveGraph} (f : FigA₂ X) : Prop :=
  ¬(Function.Injective f.val.1 ∧ Function.Injective f.val.2)

example {X : IrreflexiveGraph} (f : FigA₂ X)
    (h : f.val.1 0 = f.val.1 1) : f.IsSingular :=
  sorry

example {X : IrreflexiveGraph} (f : FigA₂ X)
    (h : f.val.2 0 = f.val.2 1) : f.IsSingular :=
  sorry

example {X : IrreflexiveGraph} (f : FigA₂ X)
    (h : f.val.2 0 = f.val.2 2) : f.IsSingular :=
  sorry

example {X : IrreflexiveGraph} (f : FigA₂ X)
    (h : f.val.2 1 = f.val.2 2) : f.IsSingular :=
  sorry

end Ex22_2

end CM

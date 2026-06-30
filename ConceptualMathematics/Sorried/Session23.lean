import ConceptualMathematics.Sorried.Article4
import Mathlib
open CategoryTheory
open Limits
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise 23.1 (p. 256)
-/
namespace Ex23_1

variable {𝒞 : Type u} [Category.{v, u} 𝒞]

structure PairOfMaps (B₁ B₂ : 𝒞) where
  carrier : 𝒞
  p₁ : carrier ⟶ B₁
  p₂ : carrier ⟶ B₂

instance {B₁ B₂ : 𝒞} : Category (PairOfMaps B₁ B₂) where
  Hom X Y := sorry
  id X := sorry
  comp f g := sorry

example {B₁ B₂ : 𝒞} {T : PairOfMaps B₁ B₂} (hT : IsTerminal T) :
    ∀ (X : 𝒞) (f₁ : X ⟶ B₁) (f₂ : X ⟶ B₂),
        ∃! f : X ⟶ T.carrier, T.p₁ ⊚ f = f₁ ∧ T.p₂ ⊚ f = f₂ :=
  sorry

example {B₁ B₂ : 𝒞} {T₁ T₂ : PairOfMaps B₁ B₂}
    (hT₁ : IsTerminal T₁) (hT₂ : IsTerminal T₂) :
    Nonempty (T₁.carrier ≅ T₂.carrier) :=
  sorry

end Ex23_1

/-!
Exercise 23.2 (p. 260)
-/
namespace Ex23_2

variable {𝒞 : Type u} [Category.{v, u} 𝒞]

structure CategorySum (B₁ B₂ : 𝒞) where
  carrier : 𝒞
  j₁ : B₁ ⟶ carrier
  j₂ : B₂ ⟶ carrier
  h_univ : ∀ (Y : 𝒞) (g₁ : B₁ ⟶ Y) (g₂ : B₂ ⟶ Y),
      ∃! g : carrier ⟶ Y, g ⊚ j₁ = g₁ ∧ g ⊚ j₂ = g₂

example {B₁ B₂ : Type} : CategorySum B₁ B₂ := {
  carrier := Sum B₁ B₂
  j₁ := Sum.inl
  j₂ := Sum.inr
  h_univ Y g₁ g₂:= sorry
}

def IGSum (B₁ B₂ : IrreflexiveGraph) : IrreflexiveGraph := {
  carrierA := Sum B₁.carrierA B₂.carrierA
  carrierD := Sum B₁.carrierD B₂.carrierD
  toSrc := fun
    | Sum.inl a₁ => Sum.inl (B₁.toSrc a₁)
    | Sum.inr a₂ => Sum.inr (B₂.toSrc a₂)
  toTgt := fun
    | Sum.inl a₁ => Sum.inl (B₁.toTgt a₁)
    | Sum.inr a₂ => Sum.inr (B₂.toTgt a₂)
}

def IGSum.inl {B₁ B₂ : IrreflexiveGraph} : B₁ ⟶ IGSum B₁ B₂ := ⟨
  (Sum.inl, Sum.inl), by constructor <;> rfl
⟩

def IGSum.inr {B₁ B₂ : IrreflexiveGraph} : B₂ ⟶ IGSum B₁ B₂ := ⟨
  (Sum.inr, Sum.inr), by constructor <;> rfl
⟩

example {B₁ B₂ : IrreflexiveGraph} : CategorySum B₁ B₂ := {
  carrier := IGSum B₁ B₂
  j₁ := IGSum.inl
  j₂ := IGSum.inr
  h_univ Y g₁ g₂:= sorry
}

end Ex23_2

end CM

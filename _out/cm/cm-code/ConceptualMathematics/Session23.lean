import ConceptualMathematics.Article4
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
  Hom X Y := {
    f : X.carrier ⟶ Y.carrier //
        Y.p₁ ⊚ f = X.p₁ ∧ Y.p₂ ⊚ f = X.p₂
  }
  id X := ⟨𝟙 X.carrier, by constructor <;> rw [Category.id_comp]⟩
  comp f g := ⟨g.val ⊚ f.val, by
    constructor
    · rw [Category.assoc, g.property.1, f.property.1]
    · rw [Category.assoc, g.property.2, f.property.2]⟩

example {B₁ B₂ : 𝒞} {T : PairOfMaps B₁ B₂} (hT : IsTerminal T) :
    ∀ (X : 𝒞) (f₁ : X ⟶ B₁) (f₂ : X ⟶ B₂),
        ∃! f : X ⟶ T.carrier, T.p₁ ⊚ f = f₁ ∧ T.p₂ ⊚ f = f₂ := by
  intro X f₁ f₂
  let XP : PairOfMaps B₁ B₂ := {
    carrier := X
    p₁ := f₁
    p₂ := f₂
  }
  let fP := hT.from XP
  use fP.val
  constructor
  · exact fP.property
  · intro f hf
    let fP' : XP ⟶ T := ⟨f, hf⟩
    exact congr_arg Subtype.val (hT.hom_ext fP' fP)

example {B₁ B₂ : 𝒞} {T₁ T₂ : PairOfMaps B₁ B₂}
    (hT₁ : IsTerminal T₁) (hT₂ : IsTerminal T₂) :
    Nonempty (T₁.carrier ≅ T₂.carrier) := by
  obtain ⟨t, ⟨ht_iso, _⟩⟩ := uniqueness_of_terminal_objects hT₁ hT₂
  apply Nonempty.intro
  exact {
    hom := t.val
    inv := (inv t).val
    hom_inv_id := congr_arg Subtype.val (IsIso.hom_inv_id t)
    inv_hom_id := congr_arg Subtype.val (IsIso.inv_hom_id t)
  }

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
  h_univ Y g₁ g₂:= by
    use fun
      | Sum.inl b₁ => g₁ b₁
      | Sum.inr b₂ => g₂ b₂
    constructor
    · constructor <;> rfl
    · intro g ⟨hg₁, hg₂⟩
      funext x
      cases x with
      | inl b₁ => exact congrFun hg₁ b₁
      | inr b₂ => exact congrFun hg₂ b₂
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
  h_univ Y g₁ g₂:= by
    use ⟨
      (fun
         | Sum.inl a₁ => g₁.val.1 a₁
         | Sum.inr a₂ => g₂.val.1 a₂,
       fun
         | Sum.inl d₁ => g₁.val.2 d₁
         | Sum.inr d₂ => g₂.val.2 d₂),
      by
        constructor <;> funext x
        · cases x with
          | inl a₁ => exact congrFun g₁.property.1 a₁
          | inr a₂ => exact congrFun g₂.property.1 a₂
        · cases x with
          | inl a₁ => exact congrFun g₁.property.2 a₁
          | inr a₂ => exact congrFun g₂.property.2 a₂
    ⟩
    constructor
    · constructor <;> rfl
    · intro g ⟨hg₁, hg₂⟩
      obtain ⟨hg₁1, hg₁2⟩ := IrreflexiveGraph.hom_ext_iff.mp hg₁
      obtain ⟨hg₂1, hg₂2⟩ := IrreflexiveGraph.hom_ext_iff.mp hg₂
      apply IrreflexiveGraph.hom_ext <;> funext x
      · cases x with
        | inl a₁ => exact congrFun hg₁1 a₁
        | inr a₂ => exact congrFun hg₂1 a₂
      · cases x with
        | inl d₁ => exact congrFun hg₁2 d₁
        | inr d₂ => exact congrFun hg₂2 d₂
}

end Ex23_2

end CM


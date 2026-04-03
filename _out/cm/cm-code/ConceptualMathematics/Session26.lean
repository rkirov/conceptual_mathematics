import Mathlib
open CategoryTheory
open Limits
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise 26.1 (p. 280)
-/
namespace Ex26_1

noncomputable def matrix2x2 {𝒞 : Type u} [Category.{v, u} 𝒞]
    [HasZeroMorphisms 𝒞] [HasBinaryBiproducts 𝒞]
    {C₁ C₂ A B : 𝒞}
    (f₁₁ : C₁ ⟶ A) (f₁₂ : C₁ ⟶ B)
    (f₂₁ : C₂ ⟶ A) (f₂₂ : C₂ ⟶ B) :
    C₁ ⊞ C₂ ⟶ A ⊞ B :=
  biprod.lift (biprod.desc f₁₁ f₂₁) (biprod.desc f₁₂ f₂₂)

example {𝒞 : Type u} [Category.{v, u} 𝒞]
    [Preadditive 𝒞] [HasBinaryBiproducts 𝒞]
    {A B X Y U V : 𝒞}
    (fAX : A ⟶ X) (fAY : A ⟶ Y) (fBX : B ⟶ X) (fBY : B ⟶ Y)
    (gXU : X ⟶ U) (gXV : X ⟶ V) (gYU : Y ⟶ U) (gYV : Y ⟶ V) :
    matrix2x2 gXU gXV gYU gYV ⊚ matrix2x2 fAX fAY fBX fBY =
    matrix2x2
    ((gXU ⊚ fAX) + (gYU ⊚ fAY)) ((gXV ⊚ fAX) + (gYV ⊚ fAY))
    ((gXU ⊚ fBX) + (gYU ⊚ fBY)) ((gXV ⊚ fBX) + (gYV ⊚ fBY)) := by
  apply biprod.hom_ext
      <;> apply biprod.hom_ext' <;> unfold matrix2x2
  · rw [Category.assoc]
    rw [biprod.lift_fst]
    rw [biprod.lift_desc]
    rw [Preadditive.comp_add]
    rw [← Category.assoc]
    rw [biprod.inl_desc]
    rw [← Category.assoc]
    rw [biprod.inl_desc]
    rw [biprod.lift_fst]
    rw [biprod.inl_desc]
  · simp
  · simp
  · simp

end Ex26_1

/-!
Exercise 26.2 (p. 280)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    [HasInitial 𝒞] [HasTerminal 𝒞] :
    Nonempty (HasZeroMorphisms 𝒞) ↔ Nonempty (⊥_ 𝒞 ≅ ⊤_ 𝒞) := by
  constructor
  · intro ⟨hZero⟩
    constructor
    exact {
      hom := 0
      inv := 0
      hom_inv_id :=
          initial.hom_ext (0 ⊚ 0 : ⊥_ 𝒞 ⟶ ⊥_ 𝒞) (𝟙 (⊥_ 𝒞))
      inv_hom_id :=
          terminal.hom_ext (0 ⊚ 0 : ⊤_ 𝒞 ⟶ ⊤_ 𝒞) (𝟙 (⊤_ 𝒞))
    }
  · intro ⟨hIso⟩
    constructor
    exact {
      zero X Y := ⟨initial.to Y ⊚ hIso.inv ⊚ terminal.from X⟩
      comp_zero := by
        intros X Y f Z
        change (initial.to Z ⊚ hIso.inv ⊚ terminal.from Y) ⊚ f =
            initial.to Z ⊚ hIso.inv ⊚ terminal.from X
        repeat rw [← Category.assoc]
        rw [terminal.hom_ext (terminal.from Y ⊚ f)]
      zero_comp := by
        intros X Y Z f
        change f ⊚ (initial.to Y ⊚ hIso.inv ⊚ terminal.from X) =
            initial.to Z ⊚ hIso.inv ⊚ terminal.from X
        rw [Category.assoc]
        rw [initial.hom_ext (f ⊚ initial.to Y)]
    }

end CM


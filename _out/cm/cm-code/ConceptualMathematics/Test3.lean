import ConceptualMathematics.Article4
import Mathlib
open CategoryTheory
open Limits
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Problem Test 3.1 (p. 299)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] [HasTerminal 𝒞] (X : 𝒞) :
    ∀ f : ⊤_ 𝒞 ⟶ X, ∃! g : X ⟶ ⊤_ 𝒞, g ⊚ f = 𝟙 (⊤_ 𝒞) := by
  intro f
  use terminal.from X
  constructor
  · exact terminal.hom_ext _ _
  · intro g' h
    exact terminal.hom_ext _ _

/-!
Problem Test 3.2 (p. 299)
-/
noncomputable
example {𝒞 : Type u} [Category.{v, u} 𝒞] [HasTerminal 𝒞]
    (C : 𝒞) (Cx1 : BinaryFan C (⊤_ 𝒞)) (lim_Cx1 : IsLimit Cx1) :
    Cx1.pt ≅ C := by
  let p₁ := 𝟙 C
  let p₂ := terminal.from C
  let Cx1' : BinaryFan C (⊤_ 𝒞) := BinaryFan.mk p₁ p₂
  have lim_Cx1' : IsLimit Cx1' := BinaryFan.isLimitMk
    (fun s ↦ s.fst)
    (fun s ↦ Category.comp_id _)
    (fun s ↦ terminal.hom_ext _ _)
    (fun s m h₁ h₂ ↦ by rw [← Category.comp_id m, h₁])
  exact IsLimit.conePointUniqueUpToIso lim_Cx1 lim_Cx1'

/-!
Problem Test 3.3 (p. 299)
-/
namespace Test3_3

def AAA : IrreflexiveGraph := {
  carrierA := Unit
  carrierD := Fin 8
  toSrc := fun _ ↦ 0
  toTgt := fun _ ↦ 7
}

open IrreflexiveGraph in
example
    (coneAAA : Fan (fun _ ↦ A : Fin 3 → IrreflexiveGraph))
    (limitAAA : IsLimit coneAAA)
    (coconeA6D : Cofan (fun
      | 0 => A | 1 => D | 2 => D | 3 => D | 4 => D | 5 => D | 6 => D :
        Fin 7 → IrreflexiveGraph))
    (colimitA6D : IsColimit coconeA6D) :
  coneAAA.pt ≅ coconeA6D.pt := by
    -- Improve readability
    set AAA : IrreflexiveGraph := coneAAA.pt with hAAA
    set A6D : IrreflexiveGraph := coconeA6D.pt with hA6D
    set p₁ := coneAAA.π.app ⟨0⟩ with hp₁ -- 𝐀×A×A ⟶ A
    set p₂ := coneAAA.π.app ⟨1⟩ with hp₂ -- A×𝐀×A ⟶ A
    set p₃ := coneAAA.π.app ⟨2⟩ with hp₃ -- A×A×𝐀 ⟶ A
    set j₁ := coconeA6D.ι.app ⟨0⟩ with hj₁ -- A ⟶ 𝐀+6D
    set j₂ := coconeA6D.ι.app ⟨1⟩ with hj₂ -- D ⟶ A+6𝐃
    set j₃ := coconeA6D.ι.app ⟨2⟩ with hj₃ -- D ⟶ A+6𝐃
    set j₄ := coconeA6D.ι.app ⟨3⟩ with hj₄ -- D ⟶ A+6𝐃
    set j₅ := coconeA6D.ι.app ⟨4⟩ with hj₅ -- D ⟶ A+6𝐃
    set j₆ := coconeA6D.ι.app ⟨5⟩ with hj₆ -- D ⟶ A+6𝐃
    set j₇ := coconeA6D.ι.app ⟨6⟩ with hj₇ -- D ⟶ A+6𝐃
    dsimp at p₁ p₂ p₃ j₁ j₂ j₃ j₄ j₅ j₆ j₇
    let d₀ : Fin 2 := 0 -- first dot of A
    let d₁ : Fin 2 := 1 -- second dot of A
    -- Construct morphism f : A×A×A ⟶ A+6D
    let f : AAA ⟶ A6D :=
      let fA : AAA.carrierA ⟶ A6D.carrierA := fun _ ↦ j₁.val.1 ()
      let fD : AAA.carrierD ⟶ A6D.carrierD := fun x ↦
        match ((p₁.val.2 x, p₂.val.2 x, p₃.val.2 x) :
            Fin 2 × Fin 2 × Fin 2) with
        | (0, 0, 0) => j₁.val.2 d₀
        | (0, 0, 1) => j₂.val.2 ()
        | (0, 1, 0) => j₃.val.2 ()
        | (0, 1, 1) => j₄.val.2 ()
        | (1, 0, 0) => j₅.val.2 ()
        | (1, 0, 1) => j₆.val.2 ()
        | (1, 1, 0) => j₇.val.2 ()
        | (1, 1, 1) => j₁.val.2 d₁
      ⟨(fA, fD), by
        constructor
        · -- Show that source commutes
          funext x
          dsimp [fA, fD]
          -- lhs (fD ⊚ AAA.toSrc = j₁.val.2)
          have hl₁ : p₁.val.2 (AAA.toSrc x) = d₀ :=
            congr_fun p₁.property.1 x
          have hl₂ : p₂.val.2 (AAA.toSrc x) = d₀ :=
            congr_fun p₂.property.1 x
          have hl₃ : p₃.val.2 (AAA.toSrc x) = d₀ :=
            congr_fun p₃.property.1 x
          -- rhs (j₁.val.2 = A6D.toSrc ⊚ fA)
          have hr : j₁.val.2 d₀ = A6D.toSrc (j₁.val.1 ()) :=
            congr_fun j₁.property.1 ()
          rw [hl₁, hl₂, hl₃, hr]
        · -- Show that target commutes
          funext x
          dsimp [fA, fD]
          -- lhs (fD ⊚ AAA.toTgt = j₁.val.2)
          have hl₁ : p₁.val.2 (AAA.toTgt x) = d₁ :=
            congr_fun p₁.property.2 x
          have hl₂ : p₂.val.2 (AAA.toTgt x) = d₁ :=
            congr_fun p₂.property.2 x
          have hl₃ : p₃.val.2 (AAA.toTgt x) = d₁ :=
            congr_fun p₃.property.2 x
          -- rhs (j₁.val.2 = A6D.toTgt ⊚ fA)
          have hr : j₁.val.2 d₁ = A6D.toTgt (j₁.val.1 ()) :=
            congr_fun j₁.property.2 ()
          rw [hl₁, hl₂, hl₃, hr]⟩
    -- Construct s which maps unique dot of D to first dot of A
    let s : D ⟶ A := ⟨
      (Empty.elim, fun _ ↦ d₀), ⟨rfl, funext fun e ↦ Empty.elim e⟩
    ⟩
    -- Construct t which maps unique dot of D to second dot of A
    let t : D ⟶ A := ⟨
      (Empty.elim, fun _ ↦ d₁), ⟨funext fun e ↦ Empty.elim e, rfl⟩
    ⟩
    -- Construct cocone over A, 6D with vertex A×A×A
    let coconeAAA : Cofan (fun
      | 0 => A | 1 => D | 2 => D | 3 => D | 4 => D | 5 => D | 6 => D :
        Fin 7 → IrreflexiveGraph) :=
      Cofan.mk coneAAA.pt (fun
        | 0 => limitAAA.lift (Fan.mk A (fun _ ↦ 𝟙 A))
        | 1 => limitAAA.lift
            (Fan.mk D (fun | 0 => s | 1 => s | 2 => t))
        | 2 => limitAAA.lift
            (Fan.mk D (fun | 0 => s | 1 => t | 2 => s))
        | 3 => limitAAA.lift
            (Fan.mk D (fun | 0 => s | 1 => t | 2 => t))
        | 4 => limitAAA.lift
            (Fan.mk D (fun | 0 => t | 1 => s | 2 => s))
        | 5 => limitAAA.lift
            (Fan.mk D (fun | 0 => t | 1 => s | 2 => t))
        | 6 => limitAAA.lift
            (Fan.mk D (fun | 0 => t | 1 => t | 2 => s)))
    -- Construct morphism f⁻¹ : A+6D ⟶ A×A×A
    let finv : A6D ⟶ AAA := colimitA6D.desc coconeAAA
    exact {
      hom := f
      inv := finv
      hom_inv_id := by
        apply limitAAA.hom_ext
        rintro ⟨i⟩
        fin_cases i
        · -- Show that p₁ ⊚ finv ⊚ f = p₁ ⊚ 𝟙 AAA
          apply IrreflexiveGraph.hom_ext
          · -- Case fA (morphisms for arrows)
            rfl
          · -- Case fD (morphisms for dots)
            funext x
            change (p₁ ⊚ finv).val.2 (f.val.2 x) = p₁.val.2 x
            dsimp [f]
            generalize p₁.val.2 x = x₁, p₂.val.2 x = x₂,
                p₃.val.2 x = x₃
            change Fin 2 at x₁ x₂ x₃
            fin_cases x₁ <;> fin_cases x₂ <;> fin_cases x₃
            · change (p₁ ⊚ finv ⊚ j₁).val.2 d₀ = d₀
              erw [colimitA6D.fac coconeAAA ⟨0⟩,
                   limitAAA.fac _ ⟨0⟩]; rfl
            · change (p₁ ⊚ finv ⊚ j₂).val.2 () = d₀
              erw [colimitA6D.fac coconeAAA ⟨1⟩,
                   limitAAA.fac _ ⟨0⟩]; rfl
            · change (p₁ ⊚ finv ⊚ j₃).val.2 () = d₀
              erw [colimitA6D.fac coconeAAA ⟨2⟩,
                   limitAAA.fac _ ⟨0⟩]; rfl
            · change (p₁ ⊚ finv ⊚ j₄).val.2 () = d₀
              erw [colimitA6D.fac coconeAAA ⟨3⟩,
                   limitAAA.fac _ ⟨0⟩]; rfl
            · change (p₁ ⊚ finv ⊚ j₅).val.2 () = d₁
              erw [colimitA6D.fac coconeAAA ⟨4⟩,
                   limitAAA.fac _ ⟨0⟩]; rfl
            · change (p₁ ⊚ finv ⊚ j₆).val.2 () = d₁
              erw [colimitA6D.fac coconeAAA ⟨5⟩,
                   limitAAA.fac _ ⟨0⟩]; rfl
            · change (p₁ ⊚ finv ⊚ j₇).val.2 () = d₁
              erw [colimitA6D.fac coconeAAA ⟨6⟩,
                   limitAAA.fac _ ⟨0⟩]; rfl
            · change (p₁ ⊚ finv ⊚ j₁).val.2 d₁ = d₁
              erw [colimitA6D.fac coconeAAA ⟨0⟩,
                   limitAAA.fac _ ⟨0⟩]; rfl
        · -- Show that p₂ ⊚ finv ⊚ f = p₂ ⊚ 𝟙 AAA
          apply IrreflexiveGraph.hom_ext
          · -- Case fA (morphisms for arrows)
            rfl
          · -- Case fD (morphisms for dots)
            funext x
            change (p₂ ⊚ finv).val.2 (f.val.2 x) = p₂.val.2 x
            dsimp [f]
            generalize p₁.val.2 x = x₁, p₂.val.2 x = x₂,
                p₃.val.2 x = x₃
            change Fin 2 at x₁ x₂ x₃
            fin_cases x₁ <;> fin_cases x₂ <;> fin_cases x₃
            · change (p₂ ⊚ finv ⊚ j₁).val.2 d₀ = d₀
              erw [colimitA6D.fac coconeAAA ⟨0⟩,
                   limitAAA.fac _ ⟨1⟩]; rfl
            · change (p₂ ⊚ finv ⊚ j₂).val.2 () = d₀
              erw [colimitA6D.fac coconeAAA ⟨1⟩,
                   limitAAA.fac _ ⟨1⟩]; rfl
            · change (p₂ ⊚ finv ⊚ j₃).val.2 () = d₁
              erw [colimitA6D.fac coconeAAA ⟨2⟩,
                   limitAAA.fac _ ⟨1⟩]; rfl
            · change (p₂ ⊚ finv ⊚ j₄).val.2 () = d₁
              erw [colimitA6D.fac coconeAAA ⟨3⟩,
                   limitAAA.fac _ ⟨1⟩]; rfl
            · change (p₂ ⊚ finv ⊚ j₅).val.2 () = d₀
              erw [colimitA6D.fac coconeAAA ⟨4⟩,
                   limitAAA.fac _ ⟨1⟩]; rfl
            · change (p₂ ⊚ finv ⊚ j₆).val.2 () = d₀
              erw [colimitA6D.fac coconeAAA ⟨5⟩,
                   limitAAA.fac _ ⟨1⟩]; rfl
            · change (p₂ ⊚ finv ⊚ j₇).val.2 () = d₁
              erw [colimitA6D.fac coconeAAA ⟨6⟩,
                   limitAAA.fac _ ⟨1⟩]; rfl
            · change (p₂ ⊚ finv ⊚ j₁).val.2 d₁ = d₁
              erw [colimitA6D.fac coconeAAA ⟨0⟩,
                   limitAAA.fac _ ⟨1⟩]; rfl
        · -- Show that p₃ ⊚ finv ⊚ f = p₃ ⊚ 𝟙 AAA
          apply IrreflexiveGraph.hom_ext
          · -- Case fA (morphisms for arrows)
            rfl
          · -- Case fD (morphisms for dots)
            funext x
            change (p₃ ⊚ finv).val.2 (f.val.2 x) = p₃.val.2 x
            dsimp [f]
            generalize p₁.val.2 x = x₁, p₂.val.2 x = x₂,
                p₃.val.2 x = x₃
            change Fin 2 at x₁ x₂ x₃
            fin_cases x₁ <;> fin_cases x₂ <;> fin_cases x₃
            · change (p₃ ⊚ finv ⊚ j₁).val.2 d₀ = d₀
              erw [colimitA6D.fac coconeAAA ⟨0⟩,
                   limitAAA.fac _ ⟨2⟩]; rfl
            · change (p₃ ⊚ finv ⊚ j₂).val.2 () = d₁
              erw [colimitA6D.fac coconeAAA ⟨1⟩,
                   limitAAA.fac _ ⟨2⟩]; rfl
            · change (p₃ ⊚ finv ⊚ j₃).val.2 () = d₀
              erw [colimitA6D.fac coconeAAA ⟨2⟩,
                   limitAAA.fac _ ⟨2⟩]; rfl
            · change (p₃ ⊚ finv ⊚ j₄).val.2 () = d₁
              erw [colimitA6D.fac coconeAAA ⟨3⟩,
                   limitAAA.fac _ ⟨2⟩]; rfl
            · change (p₃ ⊚ finv ⊚ j₅).val.2 () = d₀
              erw [colimitA6D.fac coconeAAA ⟨4⟩,
                   limitAAA.fac _ ⟨2⟩]; rfl
            · change (p₃ ⊚ finv ⊚ j₆).val.2 () = d₁
              erw [colimitA6D.fac coconeAAA ⟨5⟩,
                   limitAAA.fac _ ⟨2⟩]; rfl
            · change (p₃ ⊚ finv ⊚ j₇).val.2 () = d₀
              erw [colimitA6D.fac coconeAAA ⟨6⟩,
                   limitAAA.fac _ ⟨2⟩]; rfl
            · change (p₃ ⊚ finv ⊚ j₁).val.2 d₁ = d₁
              erw [colimitA6D.fac coconeAAA ⟨0⟩,
                   limitAAA.fac _ ⟨2⟩]; rfl
      inv_hom_id := by
        apply colimitA6D.hom_ext
        rintro ⟨j⟩
        fin_cases j
        · -- Show that f ⊚ finv ⊚ j₁ = 𝟙 A6D ⊚ j₁
          apply IrreflexiveGraph.hom_ext
          · -- Case fA (morphisms for arrows)
            rfl
          · -- Case fD (morphisms for dots)
            funext x
            change f.val.2 ((finv ⊚ j₁).val.2 x) = j₁.val.2 x
            dsimp [f]
            change Fin 2 at x
            have h₁ : (p₁ ⊚ finv ⊚ j₁).val.2 x = x := by
              erw [colimitA6D.fac coconeAAA ⟨0⟩,
                   limitAAA.fac _ ⟨0⟩]; rfl
            have h₂ : (p₂ ⊚ finv ⊚ j₁).val.2 x = x := by
              erw [colimitA6D.fac coconeAAA ⟨0⟩,
                   limitAAA.fac _ ⟨1⟩]; rfl
            have h₃ : (p₃ ⊚ finv ⊚ j₁).val.2 x = x := by
              erw [colimitA6D.fac coconeAAA ⟨0⟩,
                   limitAAA.fac _ ⟨2⟩]; rfl
            erw [h₁, h₂, h₃]
            fin_cases x <;> rfl
        · -- Show that f ⊚ finv ⊚ j₂ = 𝟙 A6D ⊚ j₂
          apply IrreflexiveGraph.hom_ext
          · -- Case fA (morphisms for arrows)
            exact funext fun e ↦ Empty.elim e
          · -- Case fD (morphisms for dots)
            funext x
            change f.val.2 ((finv ⊚ j₂).val.2 x) = j₂.val.2 x
            dsimp [f]
            have h₁ : (p₁ ⊚ finv ⊚ j₂).val.2 x = d₀ := by
              erw [colimitA6D.fac coconeAAA ⟨1⟩,
                   limitAAA.fac _ ⟨0⟩]; rfl
            have h₂ : (p₂ ⊚ finv ⊚ j₂).val.2 x = d₀ := by
              erw [colimitA6D.fac coconeAAA ⟨1⟩,
                   limitAAA.fac _ ⟨1⟩]; rfl
            have h₃ : (p₃ ⊚ finv ⊚ j₂).val.2 x = d₁ := by
              erw [colimitA6D.fac coconeAAA ⟨1⟩,
                   limitAAA.fac _ ⟨2⟩]; rfl
            erw [h₁, h₂, h₃]; rfl
        · -- Show that f ⊚ finv ⊚ j₃ = 𝟙 A6D ⊚ j₃
          apply IrreflexiveGraph.hom_ext
          · -- Case fA (morphisms for arrows)
            exact funext fun e ↦ Empty.elim e
          · -- Case fD (morphisms for dots)
            funext x
            change f.val.2 ((finv ⊚ j₃).val.2 x) = j₃.val.2 x
            dsimp [f]
            have h₁ : (p₁ ⊚ finv ⊚ j₃).val.2 x = d₀ := by
              erw [colimitA6D.fac coconeAAA ⟨2⟩,
                   limitAAA.fac _ ⟨0⟩]; rfl
            have h₂ : (p₂ ⊚ finv ⊚ j₃).val.2 x = d₁ := by
              erw [colimitA6D.fac coconeAAA ⟨2⟩,
                   limitAAA.fac _ ⟨1⟩]; rfl
            have h₃ : (p₃ ⊚ finv ⊚ j₃).val.2 x = d₀ := by
              erw [colimitA6D.fac coconeAAA ⟨2⟩,
                   limitAAA.fac _ ⟨2⟩]; rfl
            erw [h₁, h₂, h₃]; rfl
        · -- Show that f ⊚ finv ⊚ j₄ = 𝟙 A6D ⊚ j₄
          apply IrreflexiveGraph.hom_ext
          · -- Case fA (morphisms for arrows)
            exact funext fun e ↦ Empty.elim e
          · -- Case fD (morphisms for dots)
            funext x
            change f.val.2 ((finv ⊚ j₄).val.2 x) = j₄.val.2 x
            dsimp [f]
            have h₁ : (p₁ ⊚ finv ⊚ j₄).val.2 x = d₀ := by
              erw [colimitA6D.fac coconeAAA ⟨3⟩,
                   limitAAA.fac _ ⟨0⟩]; rfl
            have h₂ : (p₂ ⊚ finv ⊚ j₄).val.2 x = d₁ := by
              erw [colimitA6D.fac coconeAAA ⟨3⟩,
                   limitAAA.fac _ ⟨1⟩]; rfl
            have h₃ : (p₃ ⊚ finv ⊚ j₄).val.2 x = d₁ := by
              erw [colimitA6D.fac coconeAAA ⟨3⟩,
                   limitAAA.fac _ ⟨2⟩]; rfl
            erw [h₁, h₂, h₃]; rfl
        · -- Show that f ⊚ finv ⊚ j₅ = 𝟙 A6D ⊚ j₅
          apply IrreflexiveGraph.hom_ext
          · -- Case fA (morphisms for arrows)
            exact funext fun e ↦ Empty.elim e
          · -- Case fD (morphisms for dots)
            funext x
            change f.val.2 ((finv ⊚ j₅).val.2 x) = j₅.val.2 x
            dsimp [f]
            have h₁ : (p₁ ⊚ finv ⊚ j₅).val.2 x = d₁ := by
              erw [colimitA6D.fac coconeAAA ⟨4⟩,
                   limitAAA.fac _ ⟨0⟩]; rfl
            have h₂ : (p₂ ⊚ finv ⊚ j₅).val.2 x = d₀ := by
              erw [colimitA6D.fac coconeAAA ⟨4⟩,
                   limitAAA.fac _ ⟨1⟩]; rfl
            have h₃ : (p₃ ⊚ finv ⊚ j₅).val.2 x = d₀ := by
              erw [colimitA6D.fac coconeAAA ⟨4⟩,
                   limitAAA.fac _ ⟨2⟩]; rfl
            erw [h₁, h₂, h₃]; rfl
        · -- Show that f ⊚ finv ⊚ j₆ = 𝟙 A6D ⊚ j₆
          apply IrreflexiveGraph.hom_ext
          · -- Case fA (morphisms for arrows)
            exact funext fun e ↦ Empty.elim e
          · -- Case fD (morphisms for dots)
            funext x
            change f.val.2 ((finv ⊚ j₆).val.2 x) = j₆.val.2 x
            dsimp [f]
            have h₁ : (p₁ ⊚ finv ⊚ j₆).val.2 x = d₁ := by
              erw [colimitA6D.fac coconeAAA ⟨5⟩,
                   limitAAA.fac _ ⟨0⟩]; rfl
            have h₂ : (p₂ ⊚ finv ⊚ j₆).val.2 x = d₀ := by
              erw [colimitA6D.fac coconeAAA ⟨5⟩,
                   limitAAA.fac _ ⟨1⟩]; rfl
            have h₃ : (p₃ ⊚ finv ⊚ j₆).val.2 x = d₁ := by
              erw [colimitA6D.fac coconeAAA ⟨5⟩,
                   limitAAA.fac _ ⟨2⟩]; rfl
            erw [h₁, h₂, h₃]; rfl
        · -- Show that f ⊚ finv ⊚ j₇ = 𝟙 A6D ⊚ j₇
          apply IrreflexiveGraph.hom_ext
          · -- Case fA (morphisms for arrows)
            exact funext fun e ↦ Empty.elim e
          · -- Case fD (morphisms for dots)
            funext x
            change f.val.2 ((finv ⊚ j₇).val.2 x) = j₇.val.2 x
            dsimp [f]
            have h₁ : (p₁ ⊚ finv ⊚ j₇).val.2 x = d₁ := by
              erw [colimitA6D.fac coconeAAA ⟨6⟩,
                   limitAAA.fac _ ⟨0⟩]; rfl
            have h₂ : (p₂ ⊚ finv ⊚ j₇).val.2 x = d₁ := by
              erw [colimitA6D.fac coconeAAA ⟨6⟩,
                   limitAAA.fac _ ⟨1⟩]; rfl
            have h₃ : (p₃ ⊚ finv ⊚ j₇).val.2 x = d₀ := by
              erw [colimitA6D.fac coconeAAA ⟨6⟩,
                   limitAAA.fac _ ⟨2⟩]; rfl
            erw [h₁, h₂, h₃]; rfl
    }

end Test3_3

end CM


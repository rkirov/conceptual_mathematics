import ConceptualMathematics.Sorried.Article3
import ConceptualMathematics.Sorried.Article4
import Mathlib
open CategoryTheory
open Limits
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

def IrreflexiveGraph.TwoD : IrreflexiveGraph := {
  carrierA := Fin 4
  carrierD := Fin 2
  toSrc := fun
    | 0 => 0 -- a
    | 1 => 1 -- b
    | 2 => 0 -- u
    | 3 => 1 -- v
  toTgt := fun
    | 0 => 1 -- a
    | 1 => 0 -- b
    | 2 => 0 -- u
    | 3 => 1 -- v
}

/-!
Exercise 25.1 (p. 271)
-/
def IrreflexiveGraph.TwoA : IrreflexiveGraph :=
  sorry

/-!
Exercise 25.2 (p. 272)
-/
namespace Ex25_2

example (B₁ B₂ S : Type) (j₁ : B₁ ⟶ S) (j₂ : B₂ ⟶ S)
    (hS : ∀ (f₁ : B₁ ⟶ Two) (f₂ : B₂ ⟶ Two),
        (∃! f : S ⟶ Two, f₁ = f ⊚ j₁ ∧ f₂ = f ⊚ j₂))
    : ∀ (Y : Type) (g₁ : B₁ ⟶ Y) (g₂ : B₂ ⟶ Y),
        (∃! g : S ⟶ Y, g₁ = g ⊚ j₁ ∧ g₂ = g ⊚ j₂) :=
  sorry

open IrreflexiveGraph

example (B₁ B₂ S : IrreflexiveGraph) (j₁ : B₁ ⟶ S) (j₂ : B₂ ⟶ S)
    (hS₁ : ∀ (f₁ : B₁ ⟶ TwoA) (f₂ : B₂ ⟶ TwoA),
        (∃! f : S ⟶ TwoA, f₁ = f ⊚ j₁ ∧ f₂ = f ⊚ j₂))
    (hS₂ : ∀ (f₁ : B₁ ⟶ TwoD) (f₂ : B₂ ⟶ TwoD),
        (∃! f : S ⟶ TwoD, f₁ = f ⊚ j₁ ∧ f₂ = f ⊚ j₂))
    : ∀ (Y : IrreflexiveGraph) (g₁ : B₁ ⟶ Y) (g₂ : B₂ ⟶ Y),
        (∃! g : S ⟶ Y, g₁ = g ⊚ j₁ ∧ g₂ = g ⊚ j₂) :=
  sorry

end Ex25_2

/-!
Exercise 25.3 (p. 273)
-/
namespace Ex25_3

inductive Tricolour
  | white | red | green

def IsTricolouring (X : IrreflexiveGraph)
    (c : X.carrierD ⟶ Tricolour) : Prop :=
  ∀ a : X.carrierA, c (X.toSrc a) ≠ c (X.toTgt a)

def inducedColouring {Y X : IrreflexiveGraph} (f : Y ⟶ X)
    (c : X.carrierD ⟶ Tricolour) : Y.carrierD ⟶ Tricolour :=
  c ⊚ f.val.2

example {Y X : IrreflexiveGraph} (f : Y ⟶ X)
    (c : X.carrierD ⟶ Tricolour) (h : IsTricolouring X c) :
    IsTricolouring Y (inducedColouring f c) :=
  sorry

def Dot (X : IrreflexiveGraph) := IrreflexiveGraph.D ⟶ X

def srcDot {X : IrreflexiveGraph} (a : X.carrierA) : Dot X := ⟨
  (Empty.elim, fun _ ↦ X.toSrc a),
  ⟨by funext x; exact Empty.elim x,
   by funext x; exact Empty.elim x⟩
⟩

def tgtDot {X : IrreflexiveGraph} (a : X.carrierA) : Dot X := ⟨
  (Empty.elim, fun _ ↦ X.toTgt a),
  ⟨by funext x; exact Empty.elim x,
   by funext x; exact Empty.elim x⟩
⟩

def IsTricolouring' (X : IrreflexiveGraph)
    (c : Dot X ⟶ Tricolour) : Prop :=
  ∀ a : X.carrierA, c (srcDot a) ≠ c (tgtDot a)

def inducedColouring' {Y X : IrreflexiveGraph} (f : Y ⟶ X)
    (c : Dot X ⟶ Tricolour) : Dot Y ⟶ Tricolour :=
  fun y ↦ c (f ⊚ y)

example {Y X : IrreflexiveGraph} (f : Y ⟶ X)
    (c : Dot X ⟶ Tricolour) (h : IsTricolouring' X c) :
    IsTricolouring' Y (inducedColouring' f c) :=
  sorry

def F : IrreflexiveGraph := {
  carrierA := { p : Tricolour × Tricolour // p.1 ≠ p.2 }
  carrierD := Tricolour
  toSrc := fun p ↦ p.val.1
  toTgt := fun p ↦ p.val.2
}

example : IsTricolouring F (𝟙 F.carrierD) :=
  sorry

example {Y : IrreflexiveGraph}
    (c : Y.carrierD ⟶ Tricolour) (h : IsTricolouring Y c) :
    ∃! g : Y ⟶ F, inducedColouring g (𝟙 F.carrierD) = c :=
  sorry

end Ex25_3

/-!
Exercise 25.4 (p. 273)
-/
abbrev IrreflexiveGraph.Zero : IrreflexiveGraph := emptyIG

def IrreflexiveGraph.A₂ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 3
  toSrc := fun
    | 0 => 0
    | 1 => 1
  toTgt := fun
    | 0 => 1
    | 1 => 2
}

open IrreflexiveGraph in
example : ∀ X : IrreflexiveGraph,
    Xor' (Nonempty (X ⟶ Zero)) (Nonempty (D ⟶ X)) :=
  sorry

open IrreflexiveGraph in
example : ∀ X : IrreflexiveGraph,
    Xor' (Nonempty (X ⟶ D)) (Nonempty (A ⟶ X)) :=
  sorry

open IrreflexiveGraph in
example : ∀ X : IrreflexiveGraph,
    Xor' (Nonempty (X ⟶ A)) (Nonempty (A₂ ⟶ X)) :=
  sorry

/-!
Exercise 25.5 (p. 274)
-/
namespace Ex25_5

def B : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 3
  toSrc := fun
    | 0 => 0
    | 1 => 1
  toTgt := fun
    | 0 => 1
    | 1 => 2
}

def C : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 3
  toSrc := fun
    | 0 => 0
    | 1 => 1
  toTgt := fun
    | 0 => 1
    | 1 => 0
}

example : IsEmpty (B ≅ C) :=
  sorry

end Ex25_5

def IrreflexiveGraph.prodObj (X Y : IrreflexiveGraph) :
    IrreflexiveGraph := {
  carrierA := X.carrierA × Y.carrierA
  carrierD := X.carrierD × Y.carrierD
  toSrc := fun p ↦ (X.toSrc p.1, Y.toSrc p.2)
  toTgt := fun p ↦ (X.toTgt p.1, Y.toTgt p.2)
}

def IrreflexiveGraph.fstHom (X Y : IrreflexiveGraph) :
    prodObj X Y ⟶ X := ⟨(Prod.fst, Prod.fst), ⟨rfl, rfl⟩⟩

def IrreflexiveGraph.sndHom (X Y : IrreflexiveGraph) :
    prodObj X Y ⟶ Y := ⟨(Prod.snd, Prod.snd), ⟨rfl, rfl⟩⟩

def IrreflexiveGraph.binaryFan (X Y : IrreflexiveGraph) :
    BinaryFan X Y := BinaryFan.mk (fstHom X Y) (sndHom X Y)

def IrreflexiveGraph.isLimit (X Y : IrreflexiveGraph) :
    IsLimit (binaryFan X Y) :=
  BinaryFan.isLimitMk
    (fun s ↦ ⟨
      (fun a ↦ (s.fst.val.1 a, s.snd.val.1 a),
       fun d ↦ (s.fst.val.2 d, s.snd.val.2 d)),
      by
        constructor <;> (funext a; apply Prod.ext)
        · exact congr_fun s.fst.property.1 a
        · exact congr_fun s.snd.property.1 a
        · exact congr_fun s.fst.property.2 a
        · exact congr_fun s.snd.property.2 a⟩)
    (fun _ ↦ by apply hom_ext <;> rfl)
    (fun _ ↦ by apply hom_ext <;> rfl)
    (fun _ _ hm₁ hm₂ ↦ by
      apply hom_ext <;> (funext x; apply Prod.ext)
      · exact congr_fun (congr_arg (fun k ↦ k.val.1) hm₁) x
      · exact congr_fun (congr_arg (fun k ↦ k.val.1) hm₂) x
      · exact congr_fun (congr_arg (fun k ↦ k.val.2) hm₁) x
      · exact congr_fun (congr_arg (fun k ↦ k.val.2) hm₂) x)

open IrreflexiveGraph in
instance (X Y : IrreflexiveGraph) : HasBinaryProduct X Y :=
  HasLimit.mk ⟨binaryFan X Y, isLimit X Y⟩

namespace Ex25_5

open IrreflexiveGraph in
noncomputable example : A ⨯ B ≅ A ⨯ C :=
  sorry

end Ex25_5

/-!
Exercise 25.6 (p. 275)
-/
noncomputable example {𝒞 : Type u} [Category.{v, u} 𝒞] {X B₁ B₂ : 𝒞}
    [HasBinaryProducts 𝒞] [HasBinaryCoproducts 𝒞] :
    (X ⨯ B₁) ⨿ (X ⨯ B₂) ⟶ X ⨯ (B₁ ⨿ B₂) :=
  sorry

end CM

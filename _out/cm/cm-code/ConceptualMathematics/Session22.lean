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
-- Establish equivalence between Hom(A, X) and arrows of X
def homAEquiv (X : IrreflexiveGraph) : (A ⟶ X) ≃ X.carrierA where
  toFun fAX := fAX.val.1 ()
  invFun xA := ⟨(fun _ ↦ xA, (fun
      | 0 => X.toSrc xA
      | 1 => X.toTgt xA
      : Fin 2 → X.carrierD)),
    by
      constructor <;> (funext; rfl)
  ⟩
  left_inv fAX := by
    apply IrreflexiveGraph.hom_ext
    · funext; rfl
    · funext i
      change Fin 2 at i
      fin_cases i
      · exact (congr_fun fAX.property.1 ()).symm
      · exact (congr_fun fAX.property.2 ()).symm
  right_inv xA := rfl

open IrreflexiveGraph in
-- Establish equivalence between Hom(D, X) and dots of X
def homDEquiv (X : IrreflexiveGraph) : (D ⟶ X) ≃ X.carrierD where
  toFun fDX := fDX.val.2 ()
  invFun xD := ⟨(Empty.elim, fun _ ↦ xD),
    by
      constructor <;> (funext e; exact Empty.elim e)
  ⟩
  left_inv fDX := by
    apply IrreflexiveGraph.hom_ext
    · funext e; exact Empty.elim e
    · funext; rfl
  right_inv xD := rfl

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
        ∃! f : X ⟶ P, p₁ ⊚ f = f₁ ∧ p₂ ⊚ f = f₂ := by
  intro X f₁ f₂

  -- For each arrow in X, get equivalent morphism fAX : A ⟶ X
  let fAX (xA : X.carrierA) : A ⟶ X := (homAEquiv X).symm xA
  -- For each dot in X, get equivalent morphism fDX : D ⟶ X
  let fDX (xD : X.carrierD) : D ⟶ X := (homDEquiv X).symm xD
  -- Construct fA : X.carrierA ⟶ P.carrierA
  let fA (xA : X.carrierA) : P.carrierA :=
    -- Compose fAX with pair f₁, f₂ to obtain A ⟶ B₁, A ⟶ B₂
    let h_uniq := hA (f₁ ⊚ fAX xA) (f₂ ⊚ fAX xA)
    -- which we then use to find unique arrow in P
    (homAEquiv P) (Classical.choose h_uniq)
  -- Construct fD : X.carrierD ⟶ P.carrierD (cf. fA)
  let fD (xD : X.carrierD) : P.carrierD :=
    let h_uniq := hD (f₁ ⊚ fDX xD) (f₂ ⊚ fDX xD)
    (homDEquiv P) (Classical.choose h_uniq)
  -- For each arrow in P, get morphism fAP : A ⟶ P
  let fAP (pA : P.carrierA) : A ⟶ P := (homAEquiv P).symm pA
  -- For each dot in P, get morphism fDP : D ⟶ P
  let fDP (pD : P.carrierD) : D ⟶ P := (homDEquiv P).symm pD

  -- Show that p₁ ⊚ fAP = f₁ ⊚ fAX ∧ p₂ ⊚ fAP = f₂ ⊚ fAX
  have hA_proj : ∀ xA : X.carrierA,
      p₁ ⊚ fAP (fA xA) = f₁ ⊚ fAX xA ∧
      p₂ ⊚ fAP (fA xA) = f₂ ⊚ fAX xA := by
    intro xA
    dsimp [fAX, fAP]
    rw [Equiv.symm_apply_apply]
    exact (Classical.choose_spec (hA _ _)).1
  -- Show that p₁ ⊚ fDP = f₁ ⊚ fDX ∧ p₂ ⊚ fDP = f₂ ⊚ fDX
  have hD_proj : ∀ xD : X.carrierD,
      p₁ ⊚ fDP (fD xD) = f₁ ⊚ fDX xD ∧
      p₂ ⊚ fDP (fD xD) = f₂ ⊚ fDX xD := by
    intro xD
    dsimp [fDX, fDP]
    rw [Equiv.symm_apply_apply]
    exact (Classical.choose_spec (hD _ _)).1

  -- Show that P.toSrc ⊚ fA = fD ⊚ X.toSrc
  have hSrc_comm :
      ∀ xA : X.carrierA, P.toSrc (fA xA) = fD (X.toSrc xA) := by
    intro xA
    -- Show that p₁ ⊚ fDP = f₁ ⊚ fDX
    have hp₁ : p₁ ⊚ fDP (P.toSrc (fA xA)) =
               f₁ ⊚ fDX (X.toSrc xA) := by
      -- Transform goal from map equality to dot equality
      apply (homDEquiv B₁).injective
      calc (p₁.val.2 ⊚ P.toSrc) (fA xA)
        _ = (B₁.toSrc ⊚ p₁.val.1) (fA xA) := by rw [p₁.property.1]
        _ = B₁.toSrc ((p₁ ⊚ fAP (fA xA)).val.1 ())
                                           := rfl
        _ = B₁.toSrc ((f₁ ⊚ fAX xA).val.1 ())
                                           := by rw [(hA_proj xA).1]
        _ = (B₁.toSrc ⊚ f₁.val.1) xA      := rfl
        _ = (f₁.val.2 ⊚ X.toSrc) xA       := by rw [f₁.property.1]
    -- Show that p₂ ⊚ fDP = f₂ ⊚ fDX
    have hp₂ : p₂ ⊚ fDP (P.toSrc (fA xA)) =
               f₂ ⊚ fDX (X.toSrc xA) := by
      -- Transform goal from map equality to dot equality
      apply (homDEquiv B₂).injective
      calc (p₂.val.2 ⊚ P.toSrc) (fA xA)
        _ = (B₂.toSrc ⊚ p₂.val.1) (fA xA) := by rw [p₂.property.1]
        _ = B₂.toSrc ((p₂ ⊚ fAP (fA xA)).val.1 ())
                                           := rfl
        _ = B₂.toSrc ((f₂ ⊚ fAX xA).val.1 ())
                                           := by rw [(hA_proj xA).2]
        _ = (B₂.toSrc ⊚ f₂.val.1) xA      := rfl
        _ = (f₂.val.2 ⊚ X.toSrc) xA       := by rw [f₂.property.1]
    -- Transform goal from dot equality to map equality
    apply (homDEquiv P).symm.injective
    change fDP (P.toSrc (fA xA)) = fDP (fD (X.toSrc xA))
    -- Get unique witness for D ⟶ P
    have h_uniq := (Classical.choose_spec (hD (f₁ ⊚ fDX (X.toSrc xA))
        (f₂ ⊚ fDX (X.toSrc xA)))).2
    -- Show that lhs and rhs both equal unique witness
    have h_left := h_uniq (fDP (P.toSrc (fA xA))) ⟨hp₁, hp₂⟩
    have h_right := h_uniq (fDP (fD (X.toSrc xA)))
        (hD_proj (X.toSrc xA))
    rw [h_left, h_right]

  -- Show that P.toTgt ⊚ fA = fD ⊚ X.toTgt (cf. hSrc_comm)
  have hTgt_comm :
      ∀ xA : X.carrierA, P.toTgt (fA xA) = fD (X.toTgt xA) := by
    intro xA
    have hp₁ : p₁ ⊚ fDP (P.toTgt (fA xA)) =
               f₁ ⊚ fDX (X.toTgt xA) := by
      apply (homDEquiv B₁).injective
      calc (p₁.val.2 ⊚ P.toTgt) (fA xA)
        _ = (B₁.toTgt ⊚ p₁.val.1) (fA xA) := by rw [p₁.property.2]
        _ = B₁.toTgt ((p₁ ⊚ fAP (fA xA)).val.1 ())
                                           := rfl
        _ = B₁.toTgt ((f₁ ⊚ fAX xA).val.1 ())
                                           := by rw [(hA_proj xA).1]
        _ = (B₁.toTgt ⊚ f₁.val.1) xA      := rfl
        _ = (f₁.val.2 ⊚ X.toTgt) xA       := by rw [f₁.property.2]
    have hp₂ : p₂ ⊚ fDP (P.toTgt (fA xA)) =
               f₂ ⊚ fDX (X.toTgt xA) := by
      apply (homDEquiv B₂).injective
      calc (p₂.val.2 ⊚ P.toTgt) (fA xA)
        _ = (B₂.toTgt ⊚ p₂.val.1) (fA xA) := by rw [p₂.property.2]
        _ = B₂.toTgt ((p₂ ⊚ fAP (fA xA)).val.1 ())
                                           := rfl
        _ = B₂.toTgt ((f₂ ⊚ fAX xA).val.1 ())
                                           := by rw [(hA_proj xA).2]
        _ = (B₂.toTgt ⊚ f₂.val.1) xA      := rfl
        _ = (f₂.val.2 ⊚ X.toTgt) xA       := by rw [f₂.property.2]
    apply (homDEquiv P).symm.injective
    change fDP (P.toTgt (fA xA)) = fDP (fD (X.toTgt xA))
    have h_uniq := (Classical.choose_spec (hD (f₁ ⊚ fDX (X.toTgt xA))
        (f₂ ⊚ fDX (X.toTgt xA)))).2
    have h_left := h_uniq (fDP (P.toTgt (fA xA))) ⟨hp₁, hp₂⟩
    have h_right := h_uniq (fDP (fD (X.toTgt xA)))
        (hD_proj (X.toTgt xA))
    rw [h_left, h_right]

  -- Bundle fA and fD into morphism f : X ⟶ P
  let f : X ⟶ P := ⟨
    (fA, fD),
    by
      constructor <;> funext x
      · exact (hSrc_comm x).symm
      · exact (hTgt_comm x).symm
  ⟩

  -- Show that f satisfies commutativity and uniqueness conditions
  use f
  constructor <;> dsimp
  -- Show that the triangles commute
  · constructor
    -- Show that p₁ ⊚ f = f₁
    · apply IrreflexiveGraph.hom_ext
      · funext xA
        have h := (hA_proj xA).1
        apply_fun (fun k => k.val.1 ()) at h
        exact h
      · funext xD
        have h := (hD_proj xD).1
        apply_fun (fun k => k.val.2 ()) at h
        exact h
    -- Show that p₂ ⊚ f = f₂
    · apply IrreflexiveGraph.hom_ext
      · funext xA
        have h := (hA_proj xA).2
        apply_fun (fun k => k.val.1 ()) at h
        exact h
      · funext xD
        have h := (hD_proj xD).2
        apply_fun (fun k => k.val.2 ()) at h
        exact h
  -- Prove uniqueness of f
  · intro f' ⟨hf'₁, hf'₂⟩
    apply IrreflexiveGraph.hom_ext
    -- Show that arrow maps are equal
    · funext xA
      have hp₁ : p₁ ⊚ fAP (f'.val.1 xA) = f₁ ⊚ fAX xA := by
        apply (homAEquiv B₁).injective
        apply_fun (fun k => k.val.1 xA) at hf'₁
        exact hf'₁
      have hp₂ : p₂ ⊚ fAP (f'.val.1 xA) = f₂ ⊚ fAX xA := by
        apply (homAEquiv B₂).injective
        apply_fun (fun k => k.val.1 xA) at hf'₂
        exact hf'₂
      apply (homAEquiv P).symm.injective
      change fAP (f'.val.1 xA) = fAP (fA xA)
      have h_uniq := (Classical.choose_spec (hA (f₁ ⊚ fAX xA)
          (f₂ ⊚ fAX xA))).2
      have h_left := h_uniq (fAP (f'.val.1 xA)) ⟨hp₁, hp₂⟩
      have h_right := h_uniq (fAP (fA xA)) (hA_proj xA)
      rw [h_left, h_right]
    -- Show dot maps are equal
    · funext xD
      have hp₁ : p₁ ⊚ fDP (f'.val.2 xD) = f₁ ⊚ fDX xD := by
        apply (homDEquiv B₁).injective
        apply_fun (fun k => k.val.2 xD) at hf'₁
        exact hf'₁
      have hp₂ : p₂ ⊚ fDP (f'.val.2 xD) = f₂ ⊚ fDX xD := by
        apply (homDEquiv B₂).injective
        apply_fun (fun k => k.val.2 xD) at hf'₂
        exact hf'₂
      apply (homDEquiv P).symm.injective
      change fDP (f'.val.2 xD) = fDP (fD xD)
      have h_uniq := (Classical.choose_spec (hD (f₁ ⊚ fDX xD)
          (f₂ ⊚ fDX xD))).2
      have h_left := h_uniq (fDP (f'.val.2 xD)) ⟨hp₁, hp₂⟩
      have h_right := h_uniq (fDP (fD xD)) (hD_proj xD)
      rw [h_left, h_right]

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
    (h : f.val.1 0 = f.val.1 1) : f.IsSingular := by
  intro ⟨hA, _⟩
  exact absurd (hA h) (by decide)

example {X : IrreflexiveGraph} (f : FigA₂ X)
    (h : f.val.2 0 = f.val.2 1) : f.IsSingular := by
  intro ⟨_, hD⟩
  exact absurd (hD h) (by decide)

example {X : IrreflexiveGraph} (f : FigA₂ X)
    (h : f.val.2 0 = f.val.2 2) : f.IsSingular := by
  intro ⟨_, hD⟩
  exact absurd (hD h) (by decide)

example {X : IrreflexiveGraph} (f : FigA₂ X)
    (h : f.val.2 1 = f.val.2 2) : f.IsSingular := by
  intro ⟨_, hD⟩
  exact absurd (hD h) (by decide)

end Ex22_2

end CM


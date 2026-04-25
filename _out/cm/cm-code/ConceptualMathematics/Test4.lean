import ConceptualMathematics.Article4
import Mathlib
open CategoryTheory
open Limits
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Problem Test 4.1 (p. 300)
-/
noncomputable
example {𝒞 : Type u} [Category.{v, u} 𝒞] [HasTerminal 𝒞] {B C : 𝒞}
    [HasBinaryProduct B C] (h : B ⨯ C ≅ ⊤_ 𝒞) : B ≅ ⊤_ 𝒞 := by
  let tBxC : IsTerminal (B ⨯ C) := terminalIsTerminal.ofIso h.symm
  let iso : B ≅ B ⨯ C := {
    hom := prod.lift (𝟙 B) (prod.snd ⊚ tBxC.from B)
    inv := prod.fst
    hom_inv_id := prod.lift_fst _ _
    inv_hom_id := tBxC.hom_ext _ _
  }
  exact iso.trans h

/-!
Problem Test 4.2 (p. 300)
-/
namespace Test4_2

def B : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 2
  toSrc := fun
    | 0 => 0
    | 1 => 0
  toTgt := fun
    | 0 => 0
    | 1 => 1
}

def C : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 3
  toSrc := fun
    | 0 => 1
    | 1 => 1
  toTgt := fun
    | 0 => 0
    | 1 => 2
}

open IrreflexiveGraph

def BuD : IrreflexiveGraph := {
  carrierA := Sum B.carrierA D.carrierA
  carrierD := Sum B.carrierD D.carrierD
  toSrc := fun
    | Sum.inl a => Sum.inl (B.toSrc a)
    | Sum.inr a => Sum.inr (D.toSrc a)
  toTgt := fun
    | Sum.inl a => Sum.inl (B.toTgt a)
    | Sum.inr a => Sum.inr (D.toTgt a)
}

example : Unique (termIG ⟶ BuD) := {
  default := ⟨
    (fun _ ↦ Sum.inl (0 : Fin 2), fun _ ↦ Sum.inl (0 : Fin 2)),
    by constructor <;> rfl
  ⟩
  uniq f := by
    have hSrc : f.val.2 () = BuD.toSrc (f.val.1 ()) :=
      congr_fun f.property.1 ()
    have hTgt : f.val.2 () = BuD.toTgt (f.val.1 ()) :=
      congr_fun f.property.2 ()
    have h_eq : BuD.toSrc (f.val.1 ()) = BuD.toTgt (f.val.1 ()) :=
      Eq.trans hSrc.symm hTgt
    apply hom_ext
    all_goals
      funext x
      cases x
      generalize f.val.1 () = a at *
      · cases a with
        | inl b =>
          change Fin 2 at b
          fin_cases b
          · first | rfl | exact hSrc
          · change Sum.inl (0 : Fin 2) = Sum.inl (1 : Fin 2) at h_eq
            injection h_eq
            try contradiction
        | inr d =>
          exact Empty.elim d
}

example : IsEmpty (termIG ⟶ C) := {
  false f := by
    have hSrc : f.val.2 () = C.toSrc (f.val.1 ()) :=
      congr_fun f.property.1 ()
    have hTgt : f.val.2 () = C.toTgt (f.val.1 ()) :=
      congr_fun f.property.2 ()
    have h_eq : C.toSrc (f.val.1 ()) = C.toTgt (f.val.1 ()) :=
      Eq.trans hSrc.symm hTgt
    generalize f.val.1 () = a at h_eq
    change Fin 2 at a
    fin_cases a
    · change (1 : Fin 3) = 0 at h_eq
      contradiction
    · change (1 : Fin 3) = 2 at h_eq
      contradiction
}

def AxB : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 2 × Fin 2
  toSrc := fun _ ↦ (0, 0)
  toTgt := fun
    | 0 => (1, 0)
    | 1 => (1, 1)
}

def AxD : IrreflexiveGraph := {
  carrierA := Empty
  carrierD := Fin 2
  toSrc := Empty.elim
  toTgt := Empty.elim
}

def AxC : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 2 × Fin 3
  toSrc := fun _ ↦ (0, 1)
  toTgt := fun
    | 0 => (1, 0)
    | 1 => (1, 2)
}

def AxBuD : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 2 × Fin 3
  toSrc := fun _ ↦ (0, 0)
  toTgt := fun
    | 0 => (1, 0)
    | 1 => (1, 1)
}

example : AxBuD ≅ AxC := by
  let fD : Fin 2 × Fin 3 ⟶ Fin 2 × Fin 3
    | (0, 0) => (0, 1)
    | (0, 1) => (0, 0)
    | (1, 1) => (1, 2)
    | (1, 2) => (1, 1)
    | (d₁, d₂) => (d₁, d₂)
  exact {
    hom := ⟨(fun a ↦ a, fD),
      by
        constructor
        · rfl
        · funext d
          change Fin 2 at d
          fin_cases d <;> rfl⟩
    inv := ⟨(fun a ↦ a, fD),
      by
        constructor
        · rfl
        · funext d
          change Fin 2 at d
          fin_cases d <;> rfl⟩
    hom_inv_id := by
      apply hom_ext
      · rfl
      · funext d
        change Fin 2 × Fin 3 at d
        fin_cases d <;> rfl
    inv_hom_id := by
      apply hom_ext
      · rfl
      · funext d
        change Fin 2 × Fin 3 at d
        fin_cases d <;> rfl
  }

end Test4_2

end CM


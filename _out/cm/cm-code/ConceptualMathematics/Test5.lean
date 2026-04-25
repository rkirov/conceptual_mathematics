import ConceptualMathematics.Article4
import Mathlib
open CategoryTheory
open Limits
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Problem Test 5.1 (p. 301)
-/
namespace Test5_1

def G₁ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 0
  toTgt := fun
    | 0 => 0
    | 1 => 0
}

def G₂ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 1
  toTgt := fun
    | 0 => 0
    | 1 => 1
}

def G₃ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 0
  toTgt := fun
    | 0 => 0
    | 1 => 1
}

def G₄ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 1
  toTgt := fun
    | 0 => 0
    | 1 => 0
}

def G₅ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 1
  toTgt := fun
    | 0 => 0
    | 1 => 2
}

def G₆ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 0
  toTgt := fun
    | 0 => 1
    | 1 => 1
}

def G₇ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 1
  toTgt := fun
    | 0 => 1
    | 1 => 2
}

def G₈ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 2
  toTgt := fun
    | 0 => 1
    | 1 => 3
}

def G₉ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 1
  toTgt := fun
    | 0 => 1
    | 1 => 0
}

def G₁₀ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 2
  toTgt := fun
    | 0 => 1
    | 1 => 1
}

def G₁₁ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 1
    | 1 => 1
  toTgt := fun
    | 0 => 0
    | 1 => 2
}

end Test5_1

/-!
Problem Test 5.2 (p. 301)
-/
namespace Test5_2

abbrev I : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 3
  toSrc := fun
    | 0 => 0
    | 1 => 1
  toTgt := fun
    | 0 => 1
    | 1 => 2
}

abbrev IxI : IrreflexiveGraph := {
  carrierA := Fin 4
  carrierD := Fin 3 × Fin 3
  toSrc := fun
    | 0 => (0, 0)
    | 1 => (0, 1)
    | 2 => (1, 0)
    | 3 => (1, 1)
  toTgt := fun
    | 0 => (1, 1)
    | 1 => (1, 2)
    | 2 => (2, 1)
    | 3 => (2, 2)
}

open IrreflexiveGraph

abbrev Fam2D2AI : Fin 5 → IrreflexiveGraph
  | 0 => D
  | 1 => D
  | 2 => A
  | 3 => A
  | 4 => I

def G : IrreflexiveGraph := {
  carrierA := Σ i, (Fam2D2AI i).carrierA
  carrierD := Σ i, (Fam2D2AI i).carrierD
  toSrc := fun ⟨i, a⟩ ↦ ⟨i, (Fam2D2AI i).toSrc a⟩
  toTgt := fun ⟨i, a⟩ ↦ ⟨i, (Fam2D2AI i).toTgt a⟩
}

example : IxI ≅ G := {
  hom := ⟨
    (fun
      | 0 => ⟨4, 0⟩
      | 1 => ⟨2, ()⟩
      | 2 => ⟨3, ()⟩
      | 3 => ⟨4, 1⟩,
    fun
      | (0, 0) => ⟨4, 0⟩
      | (0, 1) => ⟨2, 0⟩
      | (0, 2) => ⟨0, ()⟩
      | (1, 0) => ⟨3, 0⟩
      | (1, 1) => ⟨4, 1⟩
      | (1, 2) => ⟨2, 1⟩
      | (2, 0) => ⟨1, ()⟩
      | (2, 1) => ⟨3, 1⟩
      | (2, 2) => ⟨4, 2⟩),
    by
      constructor
      all_goals
        funext a; fin_cases a <;> rfl
  ⟩
  inv := ⟨
    (fun
      | ⟨0, a⟩ => nomatch a
      | ⟨1, a⟩ => nomatch a
      | ⟨2, ()⟩ => 1
      | ⟨3, ()⟩ => 2
      | ⟨4, 0⟩ => 0
      | ⟨4, 1⟩ => 3,
    fun
      | ⟨0, ()⟩ => (0, 2)
      | ⟨1, ()⟩ => (2, 0)
      | ⟨2, 0⟩ => (0, 1)
      | ⟨2, 1⟩ => (1, 2)
      | ⟨3, 0⟩ => (1, 0)
      | ⟨3, 1⟩ => (2, 1)
      | ⟨4, 0⟩ => (0, 0)
      | ⟨4, 1⟩ => (1, 1)
      | ⟨4, 2⟩ => (2, 2)),
    by
      constructor
      all_goals
        funext ⟨i, a⟩
        fin_cases i
        · nomatch a
        · nomatch a
        · rfl
        · rfl
        · fin_cases a <;> rfl
  ⟩
  hom_inv_id := by
    apply hom_ext
    all_goals
      funext x; fin_cases x <;> rfl
  inv_hom_id := by
    apply hom_ext
    · funext ⟨i, a⟩
      fin_cases i
      · nomatch a
      · nomatch a
      · rfl
      · rfl
      · fin_cases a <;> rfl
    · funext ⟨i, d⟩
      fin_cases i
      · rfl
      · rfl
      · fin_cases d <;> rfl
      · fin_cases d <;> rfl
      · fin_cases d <;> rfl
}

end Test5_2

end CM


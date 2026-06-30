import ConceptualMathematics.Sorried.Article4
import Mathlib
open CategoryTheory
open Limits
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Problem Test 5.1 (p. 301)
-/
namespace Test5_1

def G₁ : IrreflexiveGraph :=
  sorry

def G₂ : IrreflexiveGraph :=
  sorry

def G₃ : IrreflexiveGraph :=
  sorry

def G₄ : IrreflexiveGraph :=
  sorry

def G₅ : IrreflexiveGraph :=
  sorry

def G₆ : IrreflexiveGraph :=
  sorry

def G₇ : IrreflexiveGraph :=
  sorry

def G₈ : IrreflexiveGraph :=
  sorry

def G₉ : IrreflexiveGraph :=
  sorry

def G₁₀ : IrreflexiveGraph :=
  sorry

def G₁₁ : IrreflexiveGraph :=
  sorry

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

abbrev IxI : IrreflexiveGraph :=
  sorry

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

example : IxI ≅ G :=
  sorry

end Test5_2

end CM

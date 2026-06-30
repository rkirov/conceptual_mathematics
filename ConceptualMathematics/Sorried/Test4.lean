import ConceptualMathematics.Sorried.Article4
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
    [HasBinaryProduct B C] (h : B ⨯ C ≅ ⊤_ 𝒞) : B ≅ ⊤_ 𝒞 :=
  sorry

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

example : Unique (termIG ⟶ BuD) :=
  sorry

example : IsEmpty (termIG ⟶ C) :=
  sorry

def AxB : IrreflexiveGraph :=
  sorry

def AxD : IrreflexiveGraph :=
  sorry

def AxC : IrreflexiveGraph :=
  sorry

def AxBuD : IrreflexiveGraph :=
  sorry

example : AxBuD ≅ AxC :=
  sorry

end Test4_2

end CM

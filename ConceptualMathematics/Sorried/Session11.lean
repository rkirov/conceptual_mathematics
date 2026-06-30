import ConceptualMathematics.Sorried.Article3
import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise 11.1 (p. 153)
-/
namespace Ex11_1

inductive A
  | a₁ | a₂ | a₃

inductive X
  | x₁ | x₂ | x₃ | x₄

def A' : SetWithEndomap := {
  carrier := A
  toEnd := fun
    | A.a₁ => A.a₂
    | A.a₂ => A.a₃
    | A.a₃ => A.a₁
}

def X' : SetWithEndomap := {
  carrier := X
  toEnd := fun -- a restriction of α to the subset {x₁, x₂, x₃, x₄}
    | X.x₁ => X.x₁
    | X.x₂ => X.x₃
    | X.x₃ => X.x₄
    | X.x₄ => X.x₂
}

def f₁ : A ⟶ X :=
  sorry

-- f₁ is structure-preserving
example : A' ⟶ X' :=
  sorry

def f₂ : A ⟶ X :=
  sorry

-- f₂ is structure-preserving
example : A' ⟶ X' :=
  sorry

def f₃ : A ⟶ X :=
  sorry

-- f₃ is structure-preserving
example : A' ⟶ X' :=
  sorry

def f₄ : A ⟶ X :=
  sorry

-- f₄ is structure-preserving
example : A' ⟶ X' :=
  sorry

end Ex11_1

/-!
Exercise 11.2 (p. 158)
-/
namespace Ex11_2

inductive X
  | a | b | c

def α : X ⟶ X
  | X.a => X.c
  | X.b => X.a
  | X.c => X.b

def Xα : SetWithEndomap := {
  carrier := X
  toEnd := α
}

inductive Y
  | p | q | r

def β : Y ⟶ Y
  | Y.p => Y.q
  | Y.q => Y.r
  | Y.r => Y.p

def Yβ : SetWithEndomap := {
  carrier := Y
  toEnd := β
}

def f₁ : X ⟶ Y :=
  sorry

--f₁ is an isomorphism
example : ∃ f : Xα ⟶ Yβ, IsIso f :=
  sorry

def f₂ : X ⟶ Y :=
  sorry

--f₂ is an isomorphism
example : ∃ f : Xα ⟶ Yβ, IsIso f :=
  sorry

def f₃ : X ⟶ Y :=
  sorry

--f₃ is an isomorphism
example : ∃ f : Xα ⟶ Yβ, IsIso f :=
  sorry

end Ex11_2

/-!
Exercise 11.3 (p. 159)
-/
namespace Ex11_3

inductive X
  | x₁ | x₂ | x₃ | x₄

def α : X ⟶ X
  | X.x₁ => X.x₂
  | X.x₂ => X.x₃
  | X.x₃ => X.x₄
  | X.x₄ => X.x₂

def Xα : SetWithEndomap := {
  carrier := X
  toEnd := α
}

inductive Y
  | y₁ | y₂ | y₃ | y₄

def β : Y ⟶ Y
  | Y.y₁ => Y.y₂
  | Y.y₂ => Y.y₃
  | Y.y₃ => Y.y₄
  | Y.y₄ => Y.y₁

def Yβ : SetWithEndomap := {
  carrier := Y
  toEnd := β
}

example : ¬(∃ f : Xα ⟶ Yβ, IsIso f) :=
  sorry

end Ex11_3

/-!
Exercise 11.4 (p. 159)
-/
example {Aα Bβ : SetWithEndomap}
    (f : Aα ⟶ Bβ) (g : Bβ.carrier ⟶ Aα.carrier)
    (h : g ⊚ f.val = 𝟙 Aα.carrier ∧ f.val ⊚ g = 𝟙 Bβ.carrier)
    : ∃ finv : Bβ ⟶ Aα, finv.val = g :=
  sorry

/-!
Exercise 11.5 (p. 159)
-/
namespace Ex11_5

def α := (· + (2 : ℤ))
def β := (· + (3 : ℤ))

abbrev ℤα : SetWithEndomap := {
  carrier := ℤ
  toEnd := α
}

abbrev ℤβ : SetWithEndomap := {
  carrier := ℤ
  toEnd := β
}

example (f : ℤα ⟶ ℤβ) : ¬(IsIso f) :=
  sorry

end Ex11_5

/-!
Exercise 11.6 (p. 159)
-/
namespace Ex11_6

inductive A
  | a₁ | a₂ | a₃

inductive D
  | d₁ | d₂ | d₃

def graph_a : IrreflexiveGraph := {
  carrierA := A
  carrierD := D
  toSrc := fun
    | A.a₁ => D.d₂
    | A.a₂ => D.d₁
    | A.a₃ => D.d₃
  toTgt := fun
    | A.a₁ => D.d₃
    | A.a₂ => D.d₂
    | A.a₃ => D.d₂
}

def graph_b : IrreflexiveGraph := {
  carrierA := A
  carrierD := D
  toSrc := fun
    | A.a₁ => D.d₁
    | A.a₂ => D.d₂
    | A.a₃ => D.d₂,
  toTgt := fun
    | A.a₁ => D.d₂
    | A.a₂ => D.d₃
    | A.a₃ => D.d₁
}

def graph_c : IrreflexiveGraph := {
  carrierA := A
  carrierD := D
  toSrc := fun
    | A.a₁ => D.d₁
    | A.a₂ => D.d₁
    | A.a₃ => D.d₁
  toTgt := fun
    | A.a₁ => D.d₃
    | A.a₂ => D.d₂
    | A.a₃ => D.d₃
}

def graph_d : IrreflexiveGraph := {
  carrierA := A
  carrierD := D
  toSrc := fun
    | A.a₁ => D.d₃
    | A.a₂ => D.d₁
    | A.a₃ => D.d₂
  toTgt := fun
    | A.a₁ => D.d₂
    | A.a₂ => D.d₂
    | A.a₃ => D.d₃
}

def graph_e : IrreflexiveGraph := {
  carrierA := A
  carrierD := D
  toSrc := fun
    | A.a₁ => D.d₁
    | A.a₂ => D.d₁
    | A.a₃ => D.d₃
  toTgt := fun
    | A.a₁ => D.d₃
    | A.a₂ => D.d₂
    | A.a₃ => D.d₁
}

def graph_f : IrreflexiveGraph := {
  carrierA := A
  carrierD := D
  toSrc := fun
    | A.a₁ => D.d₁
    | A.a₂ => D.d₁
    | A.a₃ => D.d₁
  toTgt := fun
    | A.a₁ => D.d₂
    | A.a₂ => D.d₃
    | A.a₃ => D.d₃
}

def f₁ : graph_a ⟶ graph_d :=
  sorry

def finv₁ : graph_d ⟶ graph_a :=
  sorry

example : graph_a ≅ graph_d :=
  sorry

def f₂ : graph_b ⟶ graph_e :=
  sorry

def finv₂ : graph_e ⟶ graph_b :=
  sorry

example : graph_b ≅ graph_e :=
  sorry

def f₃ : graph_c ⟶ graph_f :=
  sorry

def finv₃ : graph_f ⟶ graph_c :=
  sorry

example : graph_c ≅ graph_f :=
  sorry

end Ex11_6

/-!
Exercise 11.7 (p. 160)
-/
namespace Ex11_7

inductive A
  | a₁ | a₂ | a₃ | a₄ | a₅ | a₆

inductive D
  | d₁ | d₂ | d₃ | d₄ | d₅

def graph_L : IrreflexiveGraph := {
  carrierA := A
  carrierD := D
  toSrc := fun
    | A.a₁ => D.d₁
    | A.a₂ => D.d₂
    | A.a₃ => D.d₃
    | A.a₄ => D.d₄
    | A.a₅ => D.d₁
    | A.a₆ => D.d₅
  toTgt := fun
    | A.a₁ => D.d₂
    | A.a₂ => D.d₃
    | A.a₃ => D.d₄
    | A.a₄ => D.d₁
    | A.a₅ => D.d₅
    | A.a₆ => D.d₃
}

def graph_R : IrreflexiveGraph := {
  carrierA := A
  carrierD := D
  toSrc := fun
    | A.a₁ => D.d₂
    | A.a₂ => D.d₃
    | A.a₃ => D.d₃
    | A.a₄ => D.d₄
    | A.a₅ => D.d₁
    | A.a₆ => D.d₅
  toTgt := fun
    | A.a₁ => D.d₁
    | A.a₂ => D.d₂
    | A.a₃ => D.d₄
    | A.a₄ => D.d₁
    | A.a₅ => D.d₅
    | A.a₆ => D.d₃
}

def f : graph_L ⟶ graph_R :=
  sorry

def finv : graph_R ⟶ graph_L :=
  sorry

example : graph_L ≅ graph_R :=
  sorry

end Ex11_7

/-!
Exercise 11.8 (p. 160)
-/
namespace Ex11_8

inductive A
  | a₁ | a₂ | a₃

abbrev D := Fin 2

def J : IrreflexiveGraph := {
  carrierA := A
  carrierD := D
  toSrc := fun
    | A.a₁ => 0
    | A.a₂ => 1
    | A.a₃ => 1
  toTgt := fun
    | A.a₁ => 0
    | A.a₂ => 0
    | A.a₃ => 1
}

variable (G : IrreflexiveGraph) (b e : G.carrierD)

end Ex11_8

end CM

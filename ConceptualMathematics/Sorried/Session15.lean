import ConceptualMathematics.Sorried.Article3
import Mathlib.CategoryTheory.Endomorphism
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Period of an element (p. 176)
-/
theorem period_four_of_period_one {Y : Type} (β : End Y) (y : Y)
    : β y = y → (β ^ 4) y = y := by
  intro hβ
  nth_rw 2 [← hβ, ← hβ, ← hβ, ← hβ]
  rfl

theorem period_four_of_period_two {Y : Type} (β : End Y) (y : Y)
    : (β ^ 2) y = y → (β ^ 4) y = y := by
  intro hβ2
  nth_rw 2 [← hβ2, ← hβ2]
  rfl

/-!
Exercise 15.1 (p. 177)
-/
open Function
example {X : Type} (α : End X) (x : X)
    : (α ^ 5) x = x ∧ (α ^ 7) x = x → α x = x :=
  sorry

/-!
Successor map (p. 178)
-/
def σ : ℕ ⟶ ℕ := (· + 1)

def ℕσ : SetWithEndomap := {
  carrier := ℕ
  toEnd := σ
}

/-!
Exercise 15.2 (p. 178)
-/
namespace Ex15_2

def ς : Fin 4 ⟶ Fin 4 := (· + 1)

def C₄ : SetWithEndomap := {
  carrier := Fin 4
  toEnd := ς
}

def f₀ : ℕσ.carrier ⟶ C₄.carrier :=
  sorry

def f₀' : ℕσ ⟶ C₄ :=
  sorry

def f₁ : ℕσ.carrier ⟶ C₄.carrier :=
  sorry

def f₁' : ℕσ ⟶ C₄ :=
  sorry

def f₂ : ℕσ.carrier ⟶ C₄.carrier :=
  sorry

def f₂' : ℕσ ⟶ C₄ :=
  sorry

def f₃ : ℕσ.carrier ⟶ C₄.carrier :=
  sorry

def f₃' : ℕσ ⟶ C₄ :=
  sorry

end Ex15_2

/-!
Exercise 15.3 (p. 179)
-/
/-!
Exercise 15.4 (p. 179)
-/
namespace Ex15_4

variable (X : Type) (α : X ⟶ X)

def Xα : SetWithEndomap := {
  carrier := X
  toEnd := α
}

example : α ⊚ (Xα X α).toEnd = (Xα X α).toEnd ⊚ α :=
  sorry

end Ex15_4

/-!
Exercise 15.5 (p. 179)
-/
example (Yβ : SetWithEndomap) (f : ℕσ ⟶ Yβ) (y : Yβ.carrier)
    (hy : f.val (0 : ℕ) = y)
    : (f.val ⊚ σ) (0 : ℕ) = Yβ.toEnd y :=
  sorry

/-!
Exercise 15.6 (p. 181)
-/
namespace Ex15_6

inductive B
  | female | male

def β : B ⟶ B
  | B.female => B.female
  | B.male => B.female

inductive ParentType
  | isMother

structure Person where
  parentType : ParentType

def m : Person ⟶ Person := fun _ ↦ ⟨ParentType.isMother⟩

def Xm : SetWithEndomap := {
  carrier := Person
  toEnd := m
}

def g : Xm.carrier ⟶ B :=
  sorry

example : g ⊚ Xm.toEnd = β ⊚ g :=
  sorry

def Bβ : SetWithEndomap :=
  sorry

def g' : Xm ⟶ Bβ :=
  sorry

end Ex15_6

/-!
Exercise 15.7 (p. 185)
-/
namespace Ex15_7

inductive X
  | a | a₁ | a₂ | a₃ | a₄ | b | c | d | d₁

-- Subscripts correspond to powers of α
-- (i.e., the number of applications of α to the element)
def α : X ⟶ X
  | X.a => X.a₁
  | X.a₁ => X.a₂
  | X.a₂ => X.a₃
  | X.a₃ => X.a₄
  | X.a₄ => X.a₂
  | X.b => X.a₂
  | X.c => X.a₃
  | X.d => X.d₁
  | X.d₁ => X.d

inductive Y
  | l | m | p | q | r | s | t | u | v | w | x | y | z

def β : Y ⟶ Y
  | Y.l => Y.m
  | Y.m => Y.l
  | Y.p => Y.r
  | Y.q => Y.r
  | Y.r => Y.t
  | Y.s => Y.t
  | Y.t => Y.v
  | Y.u => Y.s
  | Y.v => Y.u
  | Y.w => Y.x
  | Y.x => Y.y
  | Y.y => Y.w
  | Y.z => Y.y

def Xα : SetWithEndomap := {
  carrier := X
  toEnd := α
}

def Yβ : SetWithEndomap := {
  carrier := Y
  toEnd := β
}

def f₁ : Xα.carrier ⟶ Yβ.carrier :=
  sorry

def f₁' : Xα ⟶ Yβ :=
  sorry

def f₂ : Xα.carrier ⟶ Yβ.carrier :=
  sorry

def f₂' : Xα ⟶ Yβ :=
  sorry

def f₃ : Xα.carrier ⟶ Yβ.carrier :=
  sorry

def f₃' : Xα ⟶ Yβ :=
  sorry

def f₄ : Xα.carrier ⟶ Yβ.carrier :=
  sorry

def f₄' : Xα ⟶ Yβ :=
  sorry

def f₅ : Xα.carrier ⟶ Yβ.carrier :=
  sorry

def f₅' : Xα ⟶ Yβ :=
  sorry

def f₆ : Xα.carrier ⟶ Yβ.carrier :=
  sorry

def f₆' : Xα ⟶ Yβ :=
  sorry

def f₇ : Xα.carrier ⟶ Yβ.carrier :=
  sorry

def f₇' : Xα ⟶ Yβ :=
  sorry

def f₈ : Xα.carrier ⟶ Yβ.carrier :=
  sorry

def f₈' : Xα ⟶ Yβ :=
  sorry

def f₉ : Xα.carrier ⟶ Yβ.carrier :=
  sorry

def f₉' : Xα ⟶ Yβ :=
  sorry

def f₁₀ : Xα.carrier ⟶ Yβ.carrier :=
  sorry

def f₁₀' : Xα ⟶ Yβ :=
  sorry

def f₁₁ : Xα.carrier ⟶ Yβ.carrier :=
  sorry

def f₁₁' : Xα ⟶ Yβ :=
  sorry

def f₁₂ : Xα.carrier ⟶ Yβ.carrier :=
  sorry

def f₁₂' : Xα ⟶ Yβ :=
  sorry

end Ex15_7

/-!
Exercise 15.12 (p. 186)
-/
end CM

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FinCases
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise I.1 (p. 19)
-/
namespace ExI_1

inductive A
  | a₁ | a₂ | a₃

inductive B
  | b₁ | b₂ | b₃ | b₄

inductive C
  | c₁ | c₂ | c₃ | c₄ | c₅

inductive D
  | d₁ | d₂ | d₃ | d₄ | d₅ | d₆

def f (a : A) : B := match a with
  | A.a₁ => B.b₁
  | A.a₂ => B.b₂
  | A.a₃ => B.b₃

def g (b : B) : C := match b with
  | B.b₁ => C.c₁
  | B.b₂ => C.c₁
  | B.b₃ => C.c₂
  | B.b₄ => C.c₅


def h (c : C) : D := match c with
  | C.c₁ => D.d₁
  | C.c₂ => D.d₂
  | C.c₃ => D.d₁
  | C.c₄ => D.d₂
  | C.c₅ => D.d₃

def hg (b : B) : D := match b with
  | B.b₁ => D.d₁
  | B.b₂ => D.d₁
  | B.b₃ => D.d₂
  | B.b₄ => D.d₃

example : hg = h ∘ g := by
  funext b
  cases b <;> rfl

def hgf (a : A) : D := match a with
  | A.a₁ => D.d₁
  | A.a₂ => D.d₁
  | A.a₃ => D.d₂

example : hgf = (h ∘ g) ∘ f := by
  funext a
  cases a <;> rfl

example : hgf = h ∘ (g ∘ f) := by
  funext a
  cases a <;> rfl

end ExI_1

/-!
One, CM_Type.Point
-/
abbrev One := Unit

def Point (Y : Type) := One → Y

-- These concrete example sets live in their own namespace so the names `A`/`B`
-- do not shadow other meanings of `A` (e.g. `IrreflexiveGraph.A`) in files that
-- import this one. Within this file we `open CM_Finset` (below) for convenience.
namespace CM_Finset

def A : Finset String := {"John" , "Mary", "Sam" }
def B : Finset String := { "eggs" , "coffee" }

def John : Point A := fun _ ↦ ⟨"John", by simp [A]⟩

def f : A → B := fun a ↦
  match a.val with
  | "John" => ⟨"eggs", by simp [B]⟩
  | "Mary" => ⟨"eggs", by simp [B]⟩
  | _ => ⟨"coffee", by simp [B]⟩

def eggs : Point B := fun _ ↦ ⟨"eggs", by simp [B]⟩

example : f ∘ John = eggs := rfl

end CM_Finset

-- Make `A`, `B`, and the maps above available unqualified for the rest of this
-- file only; this `open` does not leak to importers.
open CM_Finset

/-!
Point
-/
def PointCat (Y : Type) := One ⟶ Y

/-!
Alysia's formula
-/
def Alysia's_formula (α β : Type*) [Fintype α] [Fintype β] : ℕ :=
  Fintype.card β ^ Fintype.card α

/-!
Exercise I.2 (p. 20)
-/
#eval Alysia's_formula A B

/-!
Exercise I.3 (p. 20)
-/
#eval Alysia's_formula A A

/-!
Exercise I.4 (p. 20)
-/

#eval Alysia's_formula B A

/-!
Exercise I.5 (p. 20)
-/

#eval Alysia's_formula B B

/-!
idempotentCount

-- the key observation is that an idempotent function would send every
-- element to a fixed point under the function.

-- to count, we pick the size of Fix = {x | f x = x} - k
-- then we choose Fix, n.choose k ways, and for each assign the rest
-- n - k elements k ways.
-/
def idempotentCount (α : Type) [Fintype α] : ℕ :=
  let n := Fintype.card α
  ∑ k ∈ Finset.range (n + 1), (n.choose k) * k ^ (n - k)

/-!
Exercise I.6 (p. 20)
-/

#eval idempotentCount A

/-!
Exercise I.7 (p. 20)
-/

#eval idempotentCount B

/-!
Exercise I.8 (p. 20)
-/

def idA : A → A := fun a ↦ a
def idB : B → B := fun b ↦ b

example : Decidable (∃ f : A → B, ∃ g : B → A, g ∘ f = idA) := by
  apply isFalse
  push Not
  intro f g
  by_contra h
  have : ∃ a : A, ∀ b : B, g b ≠ a := by
    -- cardinality of B is smaller, so g cannot be surjective
    by_contra hc
    push Not at hc
    have hs : Function.Surjective g := hc
    have hcard := Fintype.card_le_of_surjective g hs
    simp only [Fintype.card_coe] at hcard
    revert hcard
    decide
  obtain ⟨a, ha⟩ := this
  have : (g ∘ f) a = a := congrFun h a
  specialize ha (f a)
  contradiction


/-!
Exercise I.9 (p. 20)
-/

example : Decidable (∃ f : B → A, ∃ g : A → B, g ∘ f = idB) := by
  apply isTrue
  use fun b ↦ match b.val with
    | "eggs" => ⟨"John", by simp [A]⟩
    | "coffee" => ⟨"Mary", by simp [A]⟩
    | _ => ⟨"Sam", by simp [A]⟩
  use fun a ↦ match a.val with
    | "John" => ⟨"eggs", by simp [B]⟩
    | "Mary" => ⟨"coffee", by simp [B]⟩
    | _ => ⟨"coffee", by simp [B]⟩
  funext b
  fin_cases b <;> rfl

end CM

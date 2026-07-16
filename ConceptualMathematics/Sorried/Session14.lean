import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Combinatorics.Quiver.ReflQuiver
import ConceptualMathematics.Sorried.Article3
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

namespace Ex14_1_3

variable (X Y : Type) (α : End X) (β : End Y)
         (f : X ⟶ Y) (hf_comm : f ⊚ α = β ⊚ f)

/-!
Exercise 14.1 (p. 170)
-/
example (x₁ x₂ : X) (y₁ y₂ : Y)
    (hy₁ : y₁ = f x₁) (hy₂ : y₂ = f x₂) (hα : α x₁ = α x₂)
    : β y₁ = β y₂ := by
  rw [hy₁, hy₂]
  have hβ₁ := congr_fun hf_comm x₁
  have hβ₂ := congr_fun hf_comm x₂
  simp only [types_comp_apply] at hβ₁ hβ₂
  rw [← hβ₁]
  rw [hα, ←hβ₂]

/-!
Exercise 14.2 (p. 170)
-/
example (x₁ x₂ : X) (y₁ y₂ : Y)
    (hy₁ : y₁ = f x₁) (hy₂ : y₂ = f x₂) (h : x₂ = (α ^ 5) x₁)
    : y₂ = (β ^ 5) y₁ := by
  rw [hy₁, hy₂, h]
  -- `f ∘ α = β ∘ f` semiconjugates, and semiconjugacy lifts to iterates:
  -- `f ∘ αⁿ = βⁿ ∘ f`, no manual associativity juggling needed.
  -- (`α ^ 5` in `End X` is defeq to the iterate `α^[5]`.)
  exact (Function.semiconj_iff_comp_eq.mpr hf_comm : Function.Semiconj f α β).iterate_right 5 x₁


open Function
lemma _root_.pow_comm {X Y : Type} (f : X ⟶ Y)
    (α : End X) (β : End Y)
    (hf_comm : f ⊚ α = β ⊚ f) (n : ℕ)
    : f ⊚ (α^[n]) = (β^[n]) ⊚ f :=
  have hf_semiconj : Semiconj f α β :=
    semiconj_iff_comp_eq.mpr hf_comm
  have hf_pow_semiconj : Semiconj f (α^[n]) (β^[n]) :=
    Semiconj.iterate_right hf_semiconj n
  semiconj_iff_comp_eq.mp hf_pow_semiconj

example (x₁ x₂ : X) (y₁ y₂ : Y)
    (hy₁ : y₁ = f x₁) (hy₂ : y₂ = f x₂) (h : x₂ = (α ^ 5) x₁)
    : y₂ = (β ^ 5) y₁ := by
  rw [hy₁, hy₂, h]
  -- `f ∘ α = β ∘ f` semiconjugates, and semiconjugacy lifts to iterates:
  -- `f ∘ αⁿ = βⁿ ∘ f`, no manual associativity juggling needed.
  -- (`α ^ 5` in `End X` is defeq to the iterate `α^[5]`.)
  exact (Function.semiconj_iff_comp_eq.mpr hf_comm : Function.Semiconj f α β).iterate_right 5 x₁

/-!
Exercise 14.3 (p. 170)
-/
example (x : X) (y : Y) (hy : y = f x) (h : α x = x) : β y = y := by
  rw [hy]
  have hβ := congr_fun hf_comm x
  simp only [types_comp_apply] at hβ
  rw [←hβ, h]

end Ex14_1_3

/-!
Exercise 14.4 (p. 171)
-/
namespace Ex14_4

inductive X
  | x₁ | x₂
  deriving DecidableEq

inductive Y
  | y₁

def α : X ⟶ X
  | X.x₁ => X.x₂
  | X.x₂ => X.x₂

def β : Y ⟶ Y
  | Y.y₁ => Y.y₁

variable (f : X ⟶ Y) (hf_comm : f ⊚ α = β ⊚ f)

example : ¬(α X.x₁ = X.x₁) ∧ β (f X.x₁) = f X.x₁ := by
  constructor
  · intro h
    rw [α] at h
    cases h
  · simp only

end Ex14_4

/-!
Exercise 14.5 (p. 171)
-/
namespace Ex14_5

example (X Y : Type) (α : End X) (β : End Y)
    (f : X ⟶ Y) (hf_comm : f ⊚ α = β ⊚ f)
    (x : X) (y : Y)
    (hy : y = f x) (h : (α ^ 4) x = x)
    : (β ^ 4) y = y := by
  rw [hy]
  have hβ := congr_fun (pow_comm f α β hf_comm 4) x
  simp only [types_comp_apply] at hβ
  -- hβ : f (α^[4] x) = β^[4] (f x); `exact` bridges `β ^ 4` ≡ `β^[4]` by defeq
  -- (rw can't, since it matches syntactically)
  exact hβ.symm.trans (congrArg f h)

inductive X
  | x₁ | x₂ | x₃ | x₄
  deriving DecidableEq

inductive Y
  | y₁ | y₂
  deriving DecidableEq

def α : End X
  | X.x₁ => X.x₂
  | X.x₂ => X.x₃
  | X.x₃ => X.x₄
  | X.x₄ => X.x₁

def β : End Y
  | Y.y₁ => Y.y₂
  | Y.y₂ => Y.y₁

def X' : SetWithEndomap := {
  carrier := X
  toEnd := α
}

def Y' : SetWithEndomap := {
  carrier := Y
  toEnd := β
}

def f : X' ⟶ Y' := ⟨
  fun
    | X.x₁ => Y.y₁
    | X.x₂ => Y.y₂
    | X.x₃ => Y.y₁
    | X.x₄ => Y.y₂,
  by
    ext x
    cases x <;> simp only [types_comp_apply, X', Y', α, β]
  ⟩

example (x : X) (y : Y) (hy : y = f x)
    : (α ^ 4) x = x ∧ ¬((α ^ 2) x = x)
      ∧
      (β ^ 2) y = y ∧ ¬(β y = y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases x <;> rfl      -- α is a 4-cycle, so α⁴ = id
  · cases x <;> decide   -- α² moves every point (no fixed point)
  · cases y <;> rfl      -- β is a 2-cycle, so β² = id
  · cases y <;> decide   -- β swaps the two points (no fixed point)

end Ex14_5

end CM

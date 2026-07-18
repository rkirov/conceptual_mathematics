import ConceptualMathematics.Sorried.Article3
import Mathlib.CategoryTheory.Endomorphism
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Problem Test 2.1 (p. 204)
-/
example (X Y : SetWithEndomap) (f : X ⟶ Y)
    (hx : ∃ x : X.carrier, X.toEnd x = x) :
    (∃ y : Y.carrier, Y.toEnd y = y) := by
  obtain ⟨x, hx'⟩ := hx
  use f x
  have := congr_fun f.prop x
  simp only [types_comp_apply] at this
  rw [hx'] at this
  exact this.symm

/-!
Problem Test 2.2 (p. 204)
-/
namespace Test2_2

inductive A₁
  | a | b

inductive D₁
  | p | q | r

def G₁ : IrreflexiveGraph := {
  A := A₁
  D := D₁
  toSrc := fun
    | A₁.a => D₁.p
    | A₁.b => D₁.q
  toTgt := fun
    | A₁.a => D₁.r
    | A₁.b => D₁.r
}

inductive A₂
  | c | d

inductive D₂
  | v | w

def G₂ : IrreflexiveGraph := {
  A := A₂
  D := D₂
  toSrc := fun
    | A₂.c => D₂.w
    | A₂.d => D₂.v
  toTgt := fun
    | A₂.c => D₂.w
    | A₂.d => D₂.w
}

def f₁ : G₁ ⟶ G₂ :=
  ⟨
    ⟨
      fun
        | A₁.a => A₂.c
        | A₁.b => A₂.d,
      fun
        | D₁.p => D₂.w
        | D₁.q => D₂.v
        | D₁.r => D₂.w
    ⟩, by
      funext x
      cases x <;> rfl
    , by
      funext x
      cases x <;> rfl
  ⟩

def f₂ : G₁ ⟶ G₂ :=
    ⟨
    ⟨
      fun
        | A₁.a => A₂.d
        | A₁.b => A₂.c,
      fun
        | D₁.p => D₂.v
        | D₁.q => D₂.w
        | D₁.r => D₂.w
    ⟩, by
      funext x
      cases x <;> rfl
    , by
      funext x
      cases x <;> rfl
  ⟩

def f₃ : G₁ ⟶ G₂ :=
  ⟨
    ⟨
      fun
        | A₁.a => A₂.d
        | A₁.b => A₂.d,
      fun
        | D₁.p => D₂.v
        | D₁.q => D₂.v
        | D₁.r => D₂.w
    ⟩, by
      funext x
      cases x <;> rfl
    , by
      funext x
      cases x <;> rfl
  ⟩

def f₄ : G₁ ⟶ G₂ :=
  ⟨
    ⟨
      fun
        | A₁.a => A₂.c
        | A₁.b => A₂.c,
      fun
        | D₁.p => D₂.w
        | D₁.q => D₂.w
        | D₁.r => D₂.w
    ⟩, by
      funext x
      cases x <;> rfl
    , by
      funext x
      cases x <;> rfl
  ⟩

example : f₁ ≠ f₂ ∧ f₁ ≠ f₃ ∧ f₁ ≠ f₄ ∧ f₂ ≠ f₃ ∧ f₂ ≠ f₄ ∧ f₃ ≠ f₄ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;>
    (have hv := congrArg (fun m => m.val.1) h
     have ha := congrFun hv A₁.a
     have hb := congrFun hv A₁.b
     simp [f₁, f₂, f₃, f₄] at ha hb)

example : ∀ (f : G₁ ⟶ G₂), f = f₁ ∨ f = f₂ ∨ f = f₃ ∨ f = f₄ := by
  rintro ⟨⟨fA, fD⟩, hs, ht⟩
  have hsa := congrFun hs A₁.a
  have hsb := congrFun hs A₁.b
  have hta := congrFun ht A₁.a
  have htb := congrFun ht A₁.b
  rcases ha : fA A₁.a with _ | _ <;> rcases hb : fA A₁.b with _ | _ <;>
    simp only [types_comp_apply, G₁, G₂, ha, hb] at hsa hsb hta htb
  -- fA a = c, fA b = c  →  f₄
  · refine Or.inr (Or.inr (Or.inr (IrreflexiveGraph.hom_ext _ _ ?_ ?_)))
    · funext x; cases x <;> simp_all [f₄]
    · funext x; cases x <;> simp_all [f₄]
  -- fA a = c, fA b = d  →  f₁
  · refine Or.inl (IrreflexiveGraph.hom_ext _ _ ?_ ?_)
    · funext x; cases x <;> simp_all [f₁]
    · funext x; cases x <;> simp_all [f₁]
  -- fA a = d, fA b = c  →  f₂
  · refine Or.inr (Or.inl (IrreflexiveGraph.hom_ext _ _ ?_ ?_))
    · funext x; cases x <;> simp_all [f₂]
    · funext x; cases x <;> simp_all [f₂]
  -- fA a = d, fA b = d  →  f₃
  · refine Or.inr (Or.inr (Or.inl (IrreflexiveGraph.hom_ext _ _ ?_ ?_)))
    · funext x; cases x <;> simp_all [f₃]
    · funext x; cases x <;> simp_all [f₃]

end Test2_2

/-!
Problem Test 2.3 (p. 204)
-/
namespace Test2_3

inductive X
  | x₁ | x₂ | x₃

def α : End X := fun
  | X.x₁ => X.x₂
  | X.x₂ => X.x₃
  | X.x₃ => X.x₃

example : α ^ 2 = α ^ 3 ∧ α ≠ α ^ 2 := by
  constructor
  · funext x
    cases x <;> rfl
  · intro h
    have := congr_fun h X.x₁
    simp [α] at this
    contradiction

end Test2_3

end CM

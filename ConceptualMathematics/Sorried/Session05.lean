import ConceptualMathematics.Sorried.Article1
import Mathlib.Tactic.DeriveFintype
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise 5.1 (p. 70)
-/

-- a)
example {A B C : Type} {f : A ⟶ B} {h : A ⟶ C}
    (hg : ∃ g : B ⟶ C, h = g ⊚ f)
    : ∀ a₁ a₂ : Point A, f ⊚ a₁ = f ⊚ a₂ → h ⊚ a₁ = h ⊚ a₂ := by
  intro a b hab
  obtain ⟨g, hg⟩ := hg
  rw [hg]
  rw [← Category.assoc, hab, Category.assoc]

noncomputable example {A B C : Type} {f : A ⟶ B} {h : A ⟶ C}
    (ha : ∀ a₁ a₂ : Point A, f ⊚ a₁ = f ⊚ a₂ → h ⊚ a₁ = h ⊚ a₂)
    : Decidable (∃ g : B ⟶ C, h = g ⊚ f) := by
  classical
  -- `ha` phrased on elements (points `Unit → A` are the same data as elements of `A`):
  -- if `f a₁ = f a₂` then `h a₁ = h a₂`.
  have key : ∀ a₁ a₂ : A, f a₁ = f a₂ → h a₁ = h a₂ := by
    intro a₁ a₂ hf
    have := ha (fun _ => a₁) (fun _ => a₂) (by funext _; exact hf)
    exact congr_fun this ()
  by_cases hC : Nonempty C
  · -- The interesting case: pick a fallback value `c₀ : C` for `b` outside the image of `f`.
    apply isTrue
    obtain ⟨c₀⟩ := hC
    -- define g as follows
    -- for b, if b = f a, then define g b := h a
    -- otherwise define g b arbitrarily (as c₀)
    refine ⟨fun b => if hb : ∃ a, f a = b then h hb.choose else c₀, ?_⟩
    funext a
    -- by `key`, this choice is well-defined: any preimage of `f a` has the same `h`-value.
    have hb : ∃ a', f a' = f a := ⟨a, rfl⟩
    change h a = if hb : ∃ a', f a' = f a then h hb.choose else c₀
    rw [dif_pos hb]
    exact (key _ _ hb.choose_spec).symm
  · -- `C` is empty. Then a factorization exists iff `B` is also empty.
    by_cases hB : Nonempty B
    · apply isFalse
      rintro ⟨g, -⟩
      exact hC ⟨g hB.some⟩
    · apply isTrue
      exact ⟨fun b => (hB ⟨b⟩).elim, funext fun a => (hC ⟨h a⟩).elim⟩

/-!
IsConstantMap
-/
def IsConstantMap {A C : Type} (h : A ⟶ C) :=
  ∃ (f : A ⟶ One) (g : One ⟶ C), h = g ⊚ f

/-!
Exercise 5.2 (p. 71)
-/
theorem exercise_5_2_a {A B C : Type} {g : B ⟶ C} {h : A ⟶ C}
    (hf : ∃ f : A ⟶ B, g ⊚ f = h)
    : ∀ a : A, ∃ b : B, h a = g b := by
  intro a
  obtain ⟨f, hf⟩ := hf
  use f a
  have := congr_fun hf a
  exact this.symm

example {A B C : Type} {g : B ⟶ C} {h : A ⟶ C}
    (ha : ∀ a : A, ∃ b : B, h a = g b)
    : ∃ f : A ⟶ B, g ⊚ f = h := by
  use fun a => (ha a).choose
  have h' (a: A) := (ha a).choose_spec
  funext a
  simp only [types_comp_apply]
  specialize h' a
  rw [h'.symm]

/-!
Exercise 5.3 (p. 75)
-/
namespace Ex5_3

inductive A
  | a₁₁ | a₁₂ | a₁₃ | a₁₄ | a₂₁ | a₂₂
  deriving Fintype

inductive B
  | b₁ | b₂
  deriving Fintype

def f : A ⟶ B
  | A.a₁₁ => B.b₁
  | A.a₁₂ => B.b₁
  | A.a₁₃ => B.b₁
  | A.a₁₄ => B.b₁
  | A.a₂₁ => B.b₂
  | A.a₂₂ => B.b₂

def s₁ : B ⟶ A
  | B.b₁ => A.a₁₁
  | B.b₂ => A.a₂₁

example : f ⊚ s₁ = 𝟙 B := by
  funext b; cases b <;> rfl

def s₂ : B ⟶ A
  | B.b₁ => A.a₁₂
  | B.b₂ => A.a₂₁

example : f ⊚ s₂ = 𝟙 B := by
  funext b; cases b <;> rfl

def s₃ : B ⟶ A
  | B.b₁ => A.a₁₃
  | B.b₂ => A.a₂₁

example : f ⊚ s₃ = 𝟙 B := by
  funext b; cases b <;> rfl

def s₄ : B ⟶ A
  | B.b₁ => A.a₁₄
  | B.b₂ => A.a₂₁

example : f ⊚ s₄ = 𝟙 B := by
  funext b; cases b <;> rfl

def s₅ : B ⟶ A
  | B.b₁ => A.a₁₁
  | B.b₂ => A.a₂₂

example : f ⊚ s₅ = 𝟙 B := by
  funext b; cases b <;> rfl

def s₆ : B ⟶ A
  | B.b₁ => A.a₁₂
  | B.b₂ => A.a₂₂

example : f ⊚ s₆ = 𝟙 B := by
  funext b; cases b <;> rfl

def s₇ : B ⟶ A
  | B.b₁ => A.a₁₃
  | B.b₂ => A.a₂₂

example : f ⊚ s₇ = 𝟙 B := by
  funext b; cases b <;> rfl

def s₈ : B ⟶ A
  | B.b₁ => A.a₁₄
  | B.b₂ => A.a₂₂

example : f ⊚ s₈ = 𝟙 B := by
  funext b; cases b <;> rfl

end Ex5_3

end CM

import ConceptualMathematics.Article3
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

def f₁ : A ⟶ X
  | A.a₁ => X.x₁
  | A.a₂ => X.x₁
  | A.a₃ => X.x₁

-- f₁ is structure-preserving
example : A' ⟶ X' := ⟨
  f₁,
  by
    funext a
    cases a <;> rfl
⟩

def f₂ : A ⟶ X
  | A.a₁ => X.x₂
  | A.a₂ => X.x₃
  | A.a₃ => X.x₄

-- f₂ is structure-preserving
example : A' ⟶ X' := ⟨
  f₂,
  by
    funext a
    cases a <;> rfl
⟩

def f₃ : A ⟶ X
  | A.a₁ => X.x₃
  | A.a₂ => X.x₄
  | A.a₃ => X.x₂

-- f₃ is structure-preserving
example : A' ⟶ X' := ⟨
  f₃,
  by
    funext a
    cases a <;> rfl
⟩

def f₄ : A ⟶ X
  | A.a₁ => X.x₄
  | A.a₂ => X.x₂
  | A.a₃ => X.x₃

-- f₄ is structure-preserving
example : A' ⟶ X' := ⟨
  f₄,
  by
    funext a
    cases a <;> rfl
⟩

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

def f₁ : X ⟶ Y
  | X.a => Y.r
  | X.b => Y.q
  | X.c => Y.p

--f₁ is an isomorphism
example : ∃ f : Xα ⟶ Yβ, IsIso f := by
  let f : Xα ⟶ Yβ := ⟨
    f₁,
    by
      -- fα = βf
      funext x
      cases x <;> rfl
  ⟩
  let finv : Yβ ⟶ Xα := ⟨
    fun
      | Y.p => X.c
      | Y.q => X.b
      | Y.r => X.a,
    by
      -- f⁻¹β = αf⁻¹
      funext y
      cases y <;> rfl
  ⟩
  use f
  use finv
  constructor
  · -- f⁻¹f = 𝟙 X
    have h : finv.val ⊚ f.val = 𝟙 X := by
      funext x
      cases x <;> rfl
    exact Subtype.ext h
  · -- ff⁻¹ = 𝟙 Y
    have h : f.val ⊚ finv.val = 𝟙 Y := by
      funext y
      cases y <;> rfl
    exact Subtype.ext h

def f₂ : X ⟶ Y
  | X.a => Y.q
  | X.b => Y.p
  | X.c => Y.r

--f₂ is an isomorphism
example : ∃ f : Xα ⟶ Yβ, IsIso f := by
  let f : Xα ⟶ Yβ := ⟨
    f₂,
    by
      -- fα = βf
      funext x
      cases x <;> rfl
  ⟩
  let finv : Yβ ⟶ Xα := ⟨
    fun
      | Y.p => X.b
      | Y.q => X.a
      | Y.r => X.c,
    by
      -- f⁻¹β = αf⁻¹
      funext y
      cases y <;> rfl
  ⟩
  use f
  use finv
  constructor
  · -- f⁻¹f = 𝟙 X
    have h : finv.val ⊚ f.val = 𝟙 X := by
      funext x
      cases x <;> rfl
    exact Subtype.ext h
  · -- ff⁻¹ = 𝟙 Y
    have h : f.val ⊚ finv.val = 𝟙 Y := by
      funext y
      cases y <;> rfl
    exact Subtype.ext h

def f₃ : X ⟶ Y
  | X.a => Y.p
  | X.b => Y.r
  | X.c => Y.q

--f₃ is an isomorphism
example : ∃ f : Xα ⟶ Yβ, IsIso f := by
  let f : Xα ⟶ Yβ := ⟨
    f₃,
    by
      -- fα = βf
      funext x
      cases x <;> rfl
  ⟩
  let finv : Yβ ⟶ Xα := ⟨
    fun
      | Y.p => X.a
      | Y.q => X.c
      | Y.r => X.b,
    by
      -- f⁻¹β = αf⁻¹
      funext y
      cases y <;> rfl
  ⟩
  use f
  use finv
  constructor
  · -- f⁻¹f = 𝟙 X
    have h : finv.val ⊚ f.val = 𝟙 X := by
      funext x
      cases x <;> rfl
    exact Subtype.ext h
  · -- ff⁻¹ = 𝟙 Y
    have h : f.val ⊚ finv.val = 𝟙 Y := by
      funext y
      cases y <;> rfl
    exact Subtype.ext h

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

example : ¬(∃ f : Xα ⟶ Yβ, IsIso f) := by
  rintro ⟨f, _⟩
  -- X.x₂ is a fixed point of α ⊚ α ⊚ α,
  have h₁ : (Xα.toEnd ⊚ Xα.toEnd ⊚ Xα.toEnd) X.x₂ = X.x₂ := by rfl
  -- but β ⊚ β ⊚ β has no fixed points in Y
  have h₂ : ∀ y : Y, (Yβ.toEnd ⊚ Yβ.toEnd ⊚ Yβ.toEnd) y ≠ y := by
    intro y
    cases y <;> exact fun h ↦ by contradiction
  -- Since f ⊚ (α ⊚ α ⊚ α) = (β ⊚ β ⊚ β) ⊚ f, we can derive a
  -- contradiction
  have h_contra : f.val ((Xα.toEnd ⊚ Xα.toEnd ⊚ Xα.toEnd) X.x₂) =
      (Yβ.toEnd ⊚ Yβ.toEnd ⊚ Yβ.toEnd) (f.val X.x₂) := by
    rw [← types_comp_apply f.val (Yβ.toEnd ⊚ Yβ.toEnd ⊚ Yβ.toEnd),
        ← Category.assoc, ← Category.assoc, ← f.property]
    rw [Category.assoc Xα.toEnd f.val, ← f.property]
    rw [Category.assoc Xα.toEnd (f.val ⊚ Xα.toEnd),
        Category.assoc Xα.toEnd f.val, ← f.property]
    rw [← Category.assoc, ← Category.assoc,
        types_comp_apply (Xα.toEnd ⊚ Xα.toEnd ⊚ Xα.toEnd)]
  have : (Yβ.toEnd ⊚ Yβ.toEnd ⊚ Yβ.toEnd) (f.val X.x₂) =
      f.val X.x₂ := by
    rw [← h_contra, h₁]
  have : (Yβ.toEnd ⊚ Yβ.toEnd ⊚ Yβ.toEnd) (f.val X.x₂) ≠
      f.val X.x₂ := h₂ (f.val X.x₂)
  contradiction

end Ex11_3

/-!
Exercise 11.4 (p. 159)
-/
example {Aα Bβ : SetWithEndomap}
    (f : Aα ⟶ Bβ) (g : Bβ.carrier ⟶ Aα.carrier)
    (h : g ⊚ f.val = 𝟙 Aα.carrier ∧ f.val ⊚ g = 𝟙 Bβ.carrier)
    : ∃ finv : Bβ ⟶ Aα, finv.val = g := by
  obtain ⟨f, hf_comm⟩ := f
  use ⟨
    g,
    by
      funext b
      apply_fun f
      · rw [← types_comp_apply (g ⊚ Bβ.toEnd) f, Category.assoc,
            h.2, Category.comp_id]
        rw [← types_comp_apply (Aα.toEnd ⊚ g) f, Category.assoc,
            hf_comm, ← Category.assoc, h.2, Category.id_comp]
      · intro a₁ a₂ hf
        have hgf := congrArg g hf
        repeat rw [← types_comp_apply f g, h.1] at hgf
        exact hgf
  ⟩

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

example (f : ℤα ⟶ ℤβ) : ¬(IsIso f) := by
  -- Assume f is an isomorphism, and derive a contradiction
  by_contra hf_iso
  -- We begin by extracting the structure-preserving property of f
  have hf_comm
      : ∀ x : ℤ, (f.val ∘ ℤα.toEnd) x = (ℤβ.toEnd ∘ f.val) x := by
    intro x
    exact congrFun f.property x
  -- and unfolding the definitions of α and β
  have hf_comm' : ∀ x : ℤ, f.val (x + 2) = f.val x + 3 := hf_comm
  -- The key observation: f.val(x + 2) and f.val(x) have the same
  -- remainder when divided by 3
  have hf_mod_3_eq : ∀ x : ℤ, f.val (x + 2) ≡ f.val x [ZMOD 3] := by
    intro x
    dsimp [Int.ModEq]
    rw [hf_comm' x]
    omega
  -- Hence all even numbers map to values with the same remainder
  -- mod 3 as f.val(0),
  have hf_even_congr :
      ∀ x : ℤ, f.val (2 * x) ≡ f.val 0 [ZMOD 3] := by
    intro x
    dsimp [Int.ModEq]
    induction x with
    | zero => simp
    | succ x' ih => rw [mul_add, mul_one, hf_mod_3_eq (2 * x'), ih]
    | pred x' ih => rw [mul_sub, ← hf_mod_3_eq (2 * (-x') - 2 * 1),
        mul_one, sub_add_cancel, ih]
  -- and all odd numbers map to values with the same remainder mod 3
  -- as f.val(1)
  have hf_odd_congr
      : ∀ x : ℤ, f.val (2 * x + 1) ≡ f.val 1 [ZMOD 3] := by
    intro x
    dsimp [Int.ModEq]
    induction x with
    | zero => simp
    | succ x' ih =>
        rw [mul_add, mul_one]
        rw [add_assoc, add_comm 2 1, ← add_assoc]
        rw [hf_mod_3_eq (2 * x' + 1), ih]
    | pred x' ih =>
        rw [mul_sub, ← hf_mod_3_eq (2 * (-x') - 2 * 1 + 1)]
        have : 2 * (-x' : ℤ) - 2 * 1 + 1 + 2 = 2 * (-x') +1 := by
          ring
        rw [this]
        exact ih
  -- So the image of f.val can have at most two distinct remainders
  -- mod 3
  have hf_img_set₁ : Set.range (fun x ↦ f.val x % 3) =
      {f.val 0 % 3, f.val 1 % 3} := by
    ext b
    constructor
    · rintro ⟨a, hfa⟩
      dsimp at hfa
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases Int.even_or_odd a with ha_even | ha_odd
      · left
        obtain ⟨a', ha_even⟩ := ha_even
        rw [← hfa, ha_even, ← two_mul, hf_even_congr a']
      · right
        obtain ⟨a', ha_odd⟩ := ha_odd
        rw [← hfa, ha_odd, hf_odd_congr a']
    · intro hb
      rcases hb with hb_mem | hb_mem <;> (rw [hb_mem]; simp)
  -- Now, since f is an isomorphism, f.val is bijective
  have hf_bij : Function.Bijective f.val :=
    ConcreteCategory.bijective_of_isIso f
  -- and hence surjective,
  have hf_surj : Function.Surjective f.val := hf_bij.right
  -- but a surjective function on ℤ must hit all three remainders
  -- mod 3
  have hf_img_set₂ :
      Set.range (fun x ↦ f.val x % 3) = {0, 1, 2} := by
    ext b
    constructor
    · rintro ⟨a, hfa⟩
      dsimp at hfa
      have hf_lbound : 0 ≤ f.val a % 3 := Int.emod_nonneg
          (f.val a) (by decide : (3 : ℤ) ≠ 0)
      have hf_ubound : f.val a % 3 < 3 := Int.emod_lt_of_pos
          (f.val a) (by decide : (0 < (3 : ℤ)))
      interval_cases k : f.val a % 3 using hf_lbound, hf_ubound <;>
        (rw [← hfa]; bound)
    · rintro (hb | hb | hb)
      all_goals
        obtain ⟨a, hfa⟩ := hf_surj b
        use a
        dsimp
        rw [hfa, hb]
        norm_num1
  -- Since we have found that the image of f.val can have at most
  -- two distinct elements and must also have exactly three distinct
  -- elements, we have a contradiction
  have h_card₁
      : Set.ncard ({f.val 0 % 3, f.val 1 % 3} : Set ℤ) ≤ 2 := by
    have h := Set.ncard_insert_le (f.val 0 % 3) {f.val 1 % 3}
    rwa [Set.ncard_singleton] at h
  have h_card₂ : Set.ncard ({0, 1, 2} : Set ℤ) = 3 := by
    apply Set.ncard_eq_three.mpr
    use 0, 1, 2
    trivial
  rw [← hf_img_set₁, hf_img_set₂, h_card₂] at h_card₁
  linarith

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

def f₁ : graph_a ⟶ graph_d := {
  val := (
    fun -- maps arrows
      | A.a₁ => A.a₃
      | A.a₂ => A.a₂
      | A.a₃ => A.a₁,
    fun -- maps dots
      | D.d₁ => D.d₁
      | D.d₂ => D.d₂
      | D.d₃ => D.d₃
  )
  property := by
    constructor
    all_goals
      funext x; cases x <;> rfl
}

def finv₁ : graph_d ⟶ graph_a := {
  val := (
    fun -- maps arrows
      | A.a₁ => A.a₃
      | A.a₂ => A.a₂
      | A.a₃ => A.a₁,
    fun -- maps dots
      | D.d₁ => D.d₁
      | D.d₂ => D.d₂
      | D.d₃ => D.d₃
  )
  property := by
    constructor
    all_goals
      funext x; cases x <;> rfl
}

example : graph_a ≅ graph_d := {
  hom := f₁,
  inv := finv₁,
  hom_inv_id := by
    have h₁ : (finv₁.val.1 ⊚ f₁.val.1 = 𝟙 graph_a.carrierA) ∧
        (finv₁.val.2 ⊚ f₁.val.2 = 𝟙 graph_a.carrierD) := by
      constructor <;> (funext x; cases x <;> rfl)
    have h₂ : (finv₁.val.1 ⊚ f₁.val.1, finv₁.val.2 ⊚ f₁.val.2) =
        (𝟙 graph_a.carrierA, 𝟙 graph_a.carrierD) := by
      rw [h₁.1, h₁.2]
    exact Subtype.ext h₂,
  inv_hom_id := by
    have h₁ : (f₁.val.1 ⊚ finv₁.val.1 = 𝟙 graph_d.carrierA) ∧
        (f₁.val.2 ⊚ finv₁.val.2 = 𝟙 graph_d.carrierD) := by
      constructor <;> (funext x; cases x <;> rfl)
    have h₂ : (f₁.val.1 ⊚ finv₁.val.1, f₁.val.2 ⊚ finv₁.val.2) =
        (𝟙 graph_d.carrierA, 𝟙 graph_d.carrierD) := by
      rw [h₁.1, h₁.2]
    exact Subtype.ext h₂
}

def f₂ : graph_b ⟶ graph_e := {
  val := (
    fun -- maps arrows
      | A.a₁ => A.a₃
      | A.a₂ => A.a₂
      | A.a₃ => A.a₁,
    fun -- maps dots
      | D.d₁ => D.d₃
      | D.d₂ => D.d₁
      | D.d₃ => D.d₂
  )
  property := by
    constructor
    all_goals
      funext x; cases x <;> rfl
}

def finv₂ : graph_e ⟶ graph_b := {
  val := (
    fun -- maps arrows
      | A.a₁ => A.a₃
      | A.a₂ => A.a₂
      | A.a₃ => A.a₁,
    fun -- maps dots
      | D.d₁ => D.d₂
      | D.d₂ => D.d₃
      | D.d₃ => D.d₁
  )
  property := by
    constructor
    all_goals
      funext x; cases x <;> rfl
}

example : graph_b ≅ graph_e := {
  hom := f₂,
  inv := finv₂,
  hom_inv_id := by
    have h₁ : (finv₂.val.1 ⊚ f₂.val.1 = 𝟙 graph_b.carrierA) ∧
        (finv₂.val.2 ⊚ f₂.val.2 = 𝟙 graph_b.carrierD) := by
      constructor <;> (funext x; cases x <;> rfl)
    have h₂ : (finv₂.val.1 ⊚ f₂.val.1, finv₂.val.2 ⊚ f₂.val.2) =
        (𝟙 graph_b.carrierA, 𝟙 graph_b.carrierD) := by
      rw [h₁.1, h₁.2]
    exact Subtype.ext h₂,
  inv_hom_id := by
    have h₁ : (f₂.val.1 ⊚ finv₂.val.1 = 𝟙 graph_e.carrierA) ∧
        (f₂.val.2 ⊚ finv₂.val.2 = 𝟙 graph_e.carrierD) := by
      constructor <;> (funext x; cases x <;> rfl)
    have h₂ : (f₂.val.1 ⊚ finv₂.val.1, f₂.val.2 ⊚ finv₂.val.2) =
        (𝟙 graph_e.carrierA, 𝟙 graph_e.carrierD) := by
      rw [h₁.1, h₁.2]
    exact Subtype.ext h₂
}

def f₃ : graph_c ⟶ graph_f := {
  val := (
    fun -- maps arrows
      | A.a₁ => A.a₂
      | A.a₂ => A.a₁
      | A.a₃ => A.a₃,
    fun -- maps dots
      | D.d₁ => D.d₁
      | D.d₂ => D.d₂
      | D.d₃ => D.d₃
  )
  property := by
    constructor
    all_goals
      funext x; cases x <;> rfl
}

def finv₃ : graph_f ⟶ graph_c := {
  val := (
    fun -- maps arrows
      | A.a₁ => A.a₂
      | A.a₂ => A.a₁
      | A.a₃ => A.a₃,
    fun -- maps dots
      | D.d₁ => D.d₁
      | D.d₂ => D.d₂
      | D.d₃ => D.d₃
  )
  property := by
    constructor
    all_goals
      funext x; cases x <;> rfl
}

example : graph_c ≅ graph_f := {
  hom := f₃,
  inv := finv₃,
  hom_inv_id := by
    have h₁ : (finv₃.val.1 ⊚ f₃.val.1 = 𝟙 graph_c.carrierA) ∧
        (finv₃.val.2 ⊚ f₃.val.2 = 𝟙 graph_c.carrierD) := by
      constructor <;> (funext x; cases x <;> rfl)
    have h₂ : (finv₃.val.1 ⊚ f₃.val.1, finv₃.val.2 ⊚ f₃.val.2) =
        (𝟙 graph_c.carrierA, 𝟙 graph_c.carrierD) := by
      rw [h₁.1, h₁.2]
    exact Subtype.ext h₂,
  inv_hom_id := by
    have h₁ : (f₃.val.1 ⊚ finv₃.val.1 = 𝟙 graph_f.carrierA) ∧
        (f₃.val.2 ⊚ finv₃.val.2 = 𝟙 graph_f.carrierD) := by
      constructor <;> (funext x; cases x <;> rfl)
    have h₂ : (f₃.val.1 ⊚ finv₃.val.1, f₃.val.2 ⊚ finv₃.val.2) =
        (𝟙 graph_f.carrierA, 𝟙 graph_f.carrierD) := by
      rw [h₁.1, h₁.2]
    exact Subtype.ext h₂
}

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

def f : graph_L ⟶ graph_R := {
  val := (
    fun -- maps arrows
      | A.a₁ => A.a₃
      | A.a₂ => A.a₄
      | A.a₃ => A.a₅
      | A.a₄ => A.a₆
      | A.a₅ => A.a₂
      | A.a₆ => A.a₁
      ,
    fun -- maps dots
      | D.d₁ => D.d₃
      | D.d₂ => D.d₄
      | D.d₃ => D.d₁
      | D.d₄ => D.d₅
      | D.d₅ => D.d₂
  )
  property := by
    constructor
    all_goals
      funext x; cases x <;> rfl
}

def finv : graph_R ⟶ graph_L := {
  val := (
    fun -- maps arrows
      | A.a₁ => A.a₆
      | A.a₂ => A.a₅
      | A.a₃ => A.a₁
      | A.a₄ => A.a₂
      | A.a₅ => A.a₃
      | A.a₆ => A.a₄,
    fun -- maps dots
      | D.d₁ => D.d₃
      | D.d₂ => D.d₅
      | D.d₃ => D.d₁
      | D.d₄ => D.d₂
      | D.d₅ => D.d₄
  )
  property := by
    constructor
    all_goals
      funext x; cases x <;> rfl
}

example : graph_L ≅ graph_R := {
  hom := f,
  inv := finv,
  hom_inv_id := by
    have h₁ : (finv.val.1 ⊚ f.val.1 = 𝟙 graph_L.carrierA) ∧
        (finv.val.2 ⊚ f.val.2 = 𝟙 graph_L.carrierD) := by
      constructor <;> (funext x; cases x <;> rfl)
    have h₂ : (finv.val.1 ⊚ f.val.1, finv.val.2 ⊚ f.val.2) =
        (𝟙 graph_L.carrierA, 𝟙 graph_L.carrierD) := by
      rw [h₁.1, h₁.2]
    exact Subtype.ext h₂,
  inv_hom_id := by
    have h₁ : (f.val.1 ⊚ finv.val.1 = 𝟙 graph_R.carrierA) ∧
        (f.val.2 ⊚ finv.val.2 = 𝟙 graph_R.carrierD) := by
      constructor <;> (funext x; cases x <;> rfl)
    have h₂ : (f.val.1 ⊚ finv.val.1, f.val.2 ⊚ finv.val.2) =
        (𝟙 graph_R.carrierA, 𝟙 graph_R.carrierD) := by
      rw [h₁.1, h₁.2]
    exact Subtype.ext h₂
}

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


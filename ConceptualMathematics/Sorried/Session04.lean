import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise 4.1 (p. 66)
-/
structure AlgebraicObj where
  t : Type
  carrier : Set t
  oper : t → t → t
  oper_mem {a b} : a ∈ carrier → b ∈ carrier → oper a b ∈ carrier

instance : Category AlgebraicObj where
  Hom X Y := {
    f : X.t ⟶ Y.t //
        (∀ x ∈ X.carrier, f x ∈ Y.carrier) -- maps to codomain
        ∧ (∀ x₁ ∈ X.carrier, -- respects combining-rules
             ∀ x₂ ∈ X.carrier, f (X.oper x₁ x₂) = Y.oper (f x₁) (f x₂))
  }
  id X := ⟨
    𝟙 X.t,
    by
      constructor
      · intro _ hx
        exact hx
      · intros
        rfl
  ⟩
  comp := by
    rintro _ _ _ ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨
      g ⊚ f,
      by
        obtain ⟨hf_mtc, hf_comb⟩ := hf
        obtain ⟨hg_mtc, hg_comb⟩ := hg
        constructor
        · intro x hx
          exact hg_mtc (f x) (hf_mtc x hx)
        · intro x₁ hx₁ x₂ hx₂
          dsimp
          have h₁ := hf_comb x₁ hx₁ x₂ hx₂
          rw [h₁]
          have h₂ :=
            hg_comb (f x₁) (hf_mtc x₁ hx₁) (f x₂) (hf_mtc x₂ hx₂)
          rw [h₂]
    ⟩

def RealAdd : AlgebraicObj := {
  t := ℝ
  carrier := Set.univ
  oper := (· + ·)
  oper_mem := fun _ _ ↦ Set.mem_univ _
}

namespace Ex4_1

def d : RealAdd ⟶ RealAdd := ⟨
  fun (x : ℝ) ↦ 2 * x,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · intros
      dsimp [RealAdd]
      ring
⟩

noncomputable def h : RealAdd ⟶ RealAdd := ⟨
  fun (x : ℝ) ↦ x / 2,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · intros
      dsimp [RealAdd]
      ring
⟩

example : IsIso d :=
  sorry

end Ex4_1

/-!
Exercise 4.2 (p. 66)
-/
namespace Ex4_2

inductive Parity
  | odd | even

def add : Parity → Parity → Parity
  | Parity.odd, Parity.odd => Parity.even
  | Parity.odd, Parity.even => Parity.odd
  | Parity.even, Parity.odd => Parity.odd
  | Parity.even, Parity.even => Parity.even

instance : Add Parity where
  add := add

inductive Sign
  | pos | neg

def mul : Sign → Sign → Sign
  | Sign.pos, Sign.pos => Sign.pos
  | Sign.pos, Sign.neg => Sign.neg
  | Sign.neg, Sign.pos => Sign.neg
  | Sign.neg, Sign.neg => Sign.pos

instance : Mul Sign where
  mul := mul

def parityAdd : AlgebraicObj := {
  t := Parity
  carrier := Set.univ
  oper := (· + ·)
  oper_mem := fun _ _ ↦ Set.mem_univ _
}

def signMul : AlgebraicObj := {
  t := Sign
  carrier := Set.univ
  oper := (· * ·)
  oper_mem := fun _ _ ↦ Set.mem_univ _
}

def f : parityAdd ⟶ signMul :=
  sorry

def finv : signMul ⟶ parityAdd :=
  sorry

example : IsIso f :=
  sorry

end Ex4_2

/-!
Exercise 4.3 (p. 66)
-/
example {p : ℝ ⟶ ℝ} (hp : ∀ x : ℝ, p x = x + 1)
    : ¬(∀ a b : ℝ, p (a + b) = p a + p b) :=
  sorry

example {sq : ℝ ⟶ ℝ} (hsq : ∀ x : ℝ, sq x = x ^ 2)
    : ¬(∃ r : ℝ → ℝ, (∀ x : ℝ, r (sq x) = x)) :=
  sorry

open NNReal in
example {sq : ℝ ⟶ ℝ≥0} (hsq : ∀ x : ℝ, sq x = x ^ 2)
    : ¬(∃ r : ℝ → ℝ, (∀ x : ℝ, r (sq x) = x)) :=
  sorry

namespace Ex4_3_d

def m : RealAdd ⟶ RealAdd := ⟨
  fun (x : ℝ) ↦ -x,
  by
    constructor
    · exact fun _ _ ↦ Set.mem_univ _
    · intros
      dsimp [RealAdd]
      ring
⟩

def minv := m

example : IsIso m :=
  sorry

end Ex4_3_d

example {m : ℝ ⟶ ℝ} (hm : ∀ x : ℝ, m x = -x)
    : ¬(∀ a b : ℝ, m (a * b) = m a * m b) :=
  sorry

namespace Ex4_3_f

abbrev ℝpos := { x : ℝ // x > 0 }

example {c : ℝ → ℝpos} (hc : ∀ x : ℝ, c x = x ^ 3)
    : ∃ x : ℝ, ¬(∃ y : ℝpos, y.val = c x) :=
  sorry

end Ex4_3_f

end CM

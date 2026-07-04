import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Tactic.DeriveFintype
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise 4.1 (p. 66)
-/
structure AlgebraicObj where
  α : Type
  op : α → α → α

instance : Category AlgebraicObj where
  Hom X Y := { f : X.α → Y.α // ∀ x y : X.α, f (X.op x y) = Y.op (f x) (f y) }
  id _ := ⟨fun x => x, by grind⟩
  comp := fun f g => ⟨fun x => g.val (f.val x), by grind⟩

def RealAdd : AlgebraicObj := {
  α := ℝ
  op := (· + ·)
}

namespace Ex4_1

def d : RealAdd ⟶ RealAdd := ⟨fun (x : ℝ) ↦ 2 * x, by
  intro x y
  simp [RealAdd]
  ring
⟩

noncomputable def h : RealAdd ⟶ RealAdd := ⟨fun (x : ℝ) ↦ x / 2, by
  intro x y
  simp [RealAdd]
  ring
⟩

example : IsIso d := by
  use h
  constructor
  · simp [h, d, RealAdd, CategoryStruct.id]
    simp [CategoryStruct.comp]
  · simp [h, d, RealAdd, CategoryStruct.id]
    simp [CategoryStruct.comp]
    grind

end Ex4_1

/-!
Exercise 4.2 (p. 66)
-/
namespace Ex4_2

inductive Parity
  | odd | even
  deriving Fintype

def add : Parity → Parity → Parity
  | Parity.odd, Parity.odd => Parity.even
  | Parity.odd, Parity.even => Parity.odd
  | Parity.even, Parity.odd => Parity.odd
  | Parity.even, Parity.even => Parity.even

instance : Add Parity where
  add := add

inductive Sign
  | pos | neg
  deriving Fintype

def mul : Sign → Sign → Sign
  | Sign.pos, Sign.pos => Sign.pos
  | Sign.pos, Sign.neg => Sign.neg
  | Sign.neg, Sign.pos => Sign.neg
  | Sign.neg, Sign.neg => Sign.pos

instance : Mul Sign where
  mul := mul

def parityAdd : AlgebraicObj := {
  α := Parity
  op := (· + ·)
}

def signMul : AlgebraicObj := {
  α := Sign
  op := (· * ·)
}

def f : parityAdd ⟶ signMul :=
  ⟨fun p ↦
    match p with
    | Parity.odd => Sign.neg
    | Parity.even => Sign.pos,
  by
    intro x y
    cases x <;> cases y <;> rfl⟩

def finv : signMul ⟶ parityAdd :=
  ⟨fun s ↦
    match s with
    | Sign.neg => Parity.odd
    | Sign.pos => Parity.even,
  by
    intro x y
    cases x <;> cases y <;> rfl⟩

example : IsIso f := by
  use finv
  constructor
  · simp [f, finv, parityAdd, signMul, CategoryStruct.comp, CategoryStruct.id]
    grind
  · simp [f, finv, parityAdd, signMul, CategoryStruct.comp, CategoryStruct.id]
    grind

end Ex4_2

/-!
Exercise 4.3 (p. 66)
-/
-- a) can't be made to AlgebraicObj
def p : ℝ → ℝ := fun x => x + 1
example : ¬(∀ a b : ℝ, p (a + b) = p a + p b) := by
  push Not
  use 1, 1
  simp [p]

-- b)
def sq := fun (x : ℝ) => x ^ 2
def RealMul : AlgebraicObj := {
  α := ℝ
  op := (· * ·)
}
def sq' : RealMul ⟶ RealMul := ⟨sq, by
  intro x y
  simp [RealMul, sq]
  ring
⟩

example : ¬ IsIso sq' := by
  intro h
  obtain ⟨g, hg, _⟩ := h
  simp only [RealMul, CategoryStruct.comp, sq', sq, CategoryStruct.id] at hg
  have hf := Subtype.ext_iff.mp hg
  have h1 := congr_fun hf (-1)
  have h2 := congr_fun hf 1
  simp only [even_two, Even.neg_pow, one_pow] at h1 h2
  rw [h1] at h2
  norm_num at h2

-- c)
open NNReal in
def PosRealMul : AlgebraicObj := {
  α := ℝ≥0
  op := fun x y => ⟨x.val * y.val, mul_nonneg x.property y.property⟩
}

def sq'' : RealMul ⟶ PosRealMul := ⟨fun (x : ℝ) ↦ ⟨x ^ 2, by positivity⟩, by
  intro x y
  simp only [RealMul, PosRealMul]
  apply Subtype.ext
  ring
⟩

example : ¬ IsIso sq'' := by
  intro h
  obtain ⟨g, hg, hg'⟩ := h
  simp only [PosRealMul, CategoryStruct.comp, sq'', CategoryStruct.id] at hg hg'
  have hf := Subtype.ext_iff.mp hg
  simp only at hf
  have h1 := congr_fun hf (1 : ℝ)
  have h2 := congr_fun hf (-1 : ℝ)
  norm_num at h1 h2
  rw [h1] at h2
  change (1 : ℝ) = -1 at h2
  norm_num at h2

-- d)
namespace Ex4_3_d

def m : RealAdd ⟶ RealAdd := ⟨
  fun (x : ℝ) ↦ -x, by
    intros
    dsimp [RealAdd]
    ring
⟩

example : IsIso m := by
  use m
  constructor <;> simp [m, RealAdd, CategoryStruct.comp, CategoryStruct.id]

end Ex4_3_d

-- e)

def m : ℝ → ℝ := fun (x : ℝ) => -x
example : ¬(∀ a b : ℝ, m (a * b) = m a * m b) := by
  push Not
  use -1, -1
  simp [m]
  norm_num

-- f)
namespace Ex4_3_f

-- the domain is not correct
def c := fun (x : ℝ) => x ^ 3
example : ∃ x : ℝ, ¬ c x > 0 := by
  use -1
  simp [c]
  norm_num

end Ex4_3_f

end CM

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
    (h : (α ^ 5) x = x ∧ (α ^ 7) x = x) : α x = x := by
  obtain ⟨h5, h7⟩ := h
  -- gcd(5, 7) = 1.  First `α² x = x`, since `α⁷ x = α² (α⁵ x) = α² x`.
  -- (The split `α⁷ x = α² (α⁵ x)` is `rfl`: `End` powers unfold to iterates.)
  have h2 : (α ^ 2) x = x := by
    have e : (α ^ 7) x = (α ^ 2) ((α ^ 5) x) := rfl
    rw [e, h5] at h7
    exact h7
  -- Then `α⁵ x = α (α² (α² x)) = α x`, and `α⁵ x = x`, so `α x = x`.
  have e5 : (α ^ 5) x = α ((α ^ 2) ((α ^ 2) x)) := rfl
  rw [h2, h2, h5] at e5
  exact e5.symm

/-!
Successor map (p. 178)
-/
def σ : ℕ ⟶ ℕ := (· + 1)

def ℕσ : SetWithEndomap := {
  carrier := ℕ
  toEnd := σ
}

/-- A map out of `ℕσ` (the naturals with successor) is determined by where it
sends `0`: two morphisms `ℕσ ⟶ Yβ` that agree at `0` are equal.  This is the
universal property of `ℕσ` as the free dynamical system on one generator —
successor forces `f (n+1) = Yβ.toEnd (f n)`, so `f 0` propagates to all of `ℕ`. -/
theorem ℕσ_hom_ext {Yβ : SetWithEndomap} (f g : ℕσ ⟶ Yβ)
    (h0 : f.val (0 : ℕ) = g.val (0 : ℕ)) : f = g := by
  apply Subtype.ext
  funext n
  induction n with
  | zero => exact h0
  | succ k ih =>
    have hf := congr_fun f.property k
    have hg := congr_fun g.property k
    simp only [ℕσ, σ, types_comp_apply] at hf hg
    rw [hf, hg, ih]

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
  fun (n : ℕ) ↦ ⟨n % 4, Nat.mod_lt n (by decide)⟩

def f₀' : ℕσ ⟶ C₄ :=
  ⟨f₀, by
    ext n
    simp only [types_comp_apply, ℕσ, C₄, σ, ς, f₀]
    grind
  ⟩

def f₁ : ℕσ.carrier ⟶ C₄.carrier :=
  fun (n : ℕ) ↦ ⟨(n + 1) % 4, Nat.mod_lt (n + 1) (by decide)⟩

def f₁' : ℕσ ⟶ C₄ :=
  ⟨f₁, by
    ext n
    simp only [types_comp_apply, ℕσ, C₄, σ, ς, f₁]
    grind
  ⟩

def f₂ : ℕσ.carrier ⟶ C₄.carrier :=
  fun (n : ℕ) ↦ ⟨(n + 2) % 4, Nat.mod_lt (n + 2) (by decide)⟩

def f₂' : ℕσ ⟶ C₄ :=
  ⟨f₂, by
    ext n
    simp only [types_comp_apply, ℕσ, C₄, σ, ς, f₂]
    grind
  ⟩

def f₃ : ℕσ.carrier ⟶ C₄.carrier :=
  fun (n : ℕ) ↦ ⟨(n + 3) % 4, Nat.mod_lt (n + 3) (by decide)⟩

def f₃' : ℕσ ⟶ C₄ :=
  ⟨f₃, by
    ext n
    simp only [types_comp_apply, ℕσ, C₄, σ, ς, f₃]
    grind
  ⟩

example : List.Pairwise (· ≠ ·) [ f₀, f₁, f₂, f₃,] := by
  -- the four maps already disagree at `0`: `fᵢ 0 = i`
  simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil,
    and_self, and_true]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
    intro h <;>
    (have := congrFun h (0 : ℕ); simp only [f₀, f₁, f₂, f₃, C₄, Fin.ext_iff] at this; omega)

example (f : ℕσ ⟶ C₄) : f = f₀' ∨ f = f₁' ∨ f = f₂' ∨ f = f₃' := by
  -- `f` is pinned by `f 0`, which is one of the four base values `fᵢ 0 = i`;
  -- `ℕσ_hom_ext` then identifies `f` with the corresponding `fᵢ'`.
  have hcase : f.val (0 : ℕ) = f₀ (0 : ℕ) ∨ f.val (0 : ℕ) = f₁ (0 : ℕ)
      ∨ f.val (0 : ℕ) = f₂ (0 : ℕ) ∨ f.val (0 : ℕ) = f₃ (0 : ℕ) := by
    simp only [f₀, f₁, f₂, f₃, C₄, Fin.ext_iff]
    omega
  rcases hcase with h | h | h | h
  · exact Or.inl (ℕσ_hom_ext f f₀' h)
  · exact Or.inr (Or.inl (ℕσ_hom_ext f f₁' h))
  · exact Or.inr (Or.inr (Or.inl (ℕσ_hom_ext f f₂' h)))
  · exact Or.inr (Or.inr (Or.inr (ℕσ_hom_ext f f₃' h)))


end Ex15_2

/-!
Exercise 15.3 (p. 179)
-/
def eval0 (X : SetWithEndomap) (f : ℕσ ⟶ X) : Unit → X.carrier :=
  fun _ ↦ f.val (0 : ℕ)

def iter (X : SetWithEndomap) (f : Unit → X.carrier) : ℕσ ⟶ X :=
  ⟨fun n ↦ (X.toEnd^[n]) (f ()), by
    ext n
    simp only [types_comp_apply, ℕσ, σ]
    -- `toEnd^[n+1] = toEnd ∘ toEnd^[n]`, so `iter` commutes with the endomaps
    exact Function.iterate_succ_apply' X.toEnd n (f ())
  ⟩

-- `iter` and `eval0` are mutually inverse: `Hom(ℕσ, X) ≃ X.carrier`.
example (X : SetWithEndomap) (f : ℕσ ⟶ X) : iter X (eval0 X f) = f := by
  -- both sides send `0` to `f 0`, so `ℕσ_hom_ext` identifies them
  apply ℕσ_hom_ext
  simp [iter, eval0]

example (X : SetWithEndomap) (f : Unit → X.carrier) : eval0 X (iter X f) = f := by
  funext u
  -- `eval0 (iter f) () = toEnd^[0] (f ()) = f ()`, and `Unit` is a subsingleton
  cases u
  rfl

/-!
Exercise 15.4 (p. 179)
-/
namespace Ex15_4

variable (X : Type) (α : X ⟶ X)

def Xα : SetWithEndomap := {
  carrier := X
  toEnd := α
}

example : α ⊚ (Xα X α).toEnd = (Xα X α).toEnd ⊚ α := by
  simp only [Xα]

end Ex15_4

/-!
Exercise 15.5 (p. 179)
-/
example (Yβ : SetWithEndomap) (f : ℕσ ⟶ Yβ) (y : Yβ.carrier)
    (hy : f.val (0 : ℕ) = y)
    : (f.val ⊚ σ) (0 : ℕ) = Yβ.toEnd y := by
  rw [← hy]
  simp only [types_comp_apply]
  have := congr_fun f.property (0 : ℕ)
  simp only [types_comp_apply] at this
  rw [← this]
  rfl

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

-- todo: think how to rework this. Person should not be a type with a
-- single inhabitant, but if too free we don't know how to define
-- the endomap.
structure Person where
  parentType : ParentType

def m : Person ⟶ Person := fun _ ↦ ⟨ParentType.isMother⟩

def Xm : SetWithEndomap := {
  carrier := Person
  toEnd := m
}

def g : Xm.carrier ⟶ B
  | ⟨ParentType.isMother⟩ => B.female

example : g ⊚ Xm.toEnd = β ⊚ g := by
  simp only [Xm]
  rfl

def Bβ : SetWithEndomap := {
  carrier := B
  toEnd := β
}

def g' : Xm ⟶ Bβ :=
  ⟨g, by
    ext p
    simp only [types_comp_apply, Xm, Bβ, β, g]
    grind
  ⟩

end Ex15_6

/-!
Exercise 15.7 (p. 185)
-/
namespace Ex15_7

inductive X
  | a | a₁ | a₂ | a₃ | a₄ | b | c | d | d₁
  deriving DecidableEq, Fintype

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
  deriving DecidableEq, Fintype

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

-- find a st β^5 a = β^2 a - y w x - 1 + 2 + 1 + 2
-- β ^ 2 a = β b - w -> x or z,
-- β ^ 3 a = β c - w -> y
-- d -> d₁ or d₂

-- a = z, b = y, c = w, d = x
def f₁ : Xα.carrier ⟶ Yβ.carrier
  | X.a => Y.z
  | X.a₁ => Y.y
  | X.a₂ => Y.w
  | X.a₃ => Y.x
  | X.a₄ => Y.y
  | X.b => Y.y
  | X.c => Y.w
  | X.d => Y.l
  | X.d₁ => Y.m

def f₁' : Xα ⟶ Yβ :=
  ⟨f₁, by
    ext x
    simp only [types_comp_apply, Xα, Yβ, α, β, f₁]
    grind
  ⟩

def f₂ : Xα.carrier ⟶ Yβ.carrier
  | X.a => Y.z
  | X.a₁ => Y.y
  | X.a₂ => Y.w
  | X.a₃ => Y.x
  | X.a₄ => Y.y
  | X.b => Y.y
  | X.c => Y.w
  | X.d => Y.m
  | X.d₁ => Y.l

def f₂' : Xα ⟶ Yβ :=
  ⟨f₂, by
    ext x
    simp only [types_comp_apply, Xα, Yβ, α, β, f₂]
    grind
  ⟩

def f₃ : Xα.carrier ⟶ Yβ.carrier
  | X.a => Y.y
  | X.a₁ => Y.w
  | X.a₂ => Y.x
  | X.a₃ => Y.y
  | X.a₄ => Y.w
  | X.b => Y.w
  | X.c => Y.x
  | X.d => Y.l
  | X.d₁ => Y.m

def f₃' : Xα ⟶ Yβ :=
  ⟨f₃, by
    ext x
    simp only [types_comp_apply, Xα, Yβ, α, β, f₃]
    grind
  ⟩

def f₄ : Xα.carrier ⟶ Yβ.carrier
  | X.a => Y.y
  | X.a₁ => Y.w
  | X.a₂ => Y.x
  | X.a₃ => Y.y
  | X.a₄ => Y.w
  | X.b => Y.w
  | X.c => Y.x
  | X.d => Y.m
  | X.d₁ => Y.l

def f₄' : Xα ⟶ Yβ :=
  ⟨f₄, by
    ext x
    simp only [types_comp_apply, Xα, Yβ, α, β, f₄]
    grind
  ⟩

def f₅ : Xα.carrier ⟶ Yβ.carrier
  | X.a => Y.y
  | X.a₁ => Y.w
  | X.a₂ => Y.x
  | X.a₃ => Y.y
  | X.a₄ => Y.w
  | X.b => Y.w
  | X.c => Y.z
  | X.d => Y.m
  | X.d₁ => Y.l

def f₅' : Xα ⟶ Yβ :=
  ⟨f₅, by
    ext x
    simp only [types_comp_apply, Xα, Yβ, α, β, f₅]
    grind
  ⟩

def f₆ : Xα.carrier ⟶ Yβ.carrier
  | X.a => Y.y
  | X.a₁ => Y.w
  | X.a₂ => Y.x
  | X.a₃ => Y.y
  | X.a₄ => Y.w
  | X.b => Y.w
  | X.c => Y.z
  | X.d => Y.l
  | X.d₁ => Y.m

def f₆' : Xα ⟶ Yβ :=
  ⟨f₆, by
    ext x
    simp only [types_comp_apply, Xα, Yβ, α, β, f₆]
    grind
  ⟩

def f₇ : Xα.carrier ⟶ Yβ.carrier
  | X.a => Y.x
  | X.a₁ => Y.y
  | X.a₂ => Y.w
  | X.a₃ => Y.x
  | X.a₄ => Y.y
  | X.b => Y.y
  | X.c => Y.w
  | X.d => Y.m
  | X.d₁ => Y.l

def f₇' : Xα ⟶ Yβ :=
  ⟨f₇, by
    ext x
    simp only [types_comp_apply, Xα, Yβ, α, β, f₇]
    grind
  ⟩

def f₈ : Xα.carrier ⟶ Yβ.carrier
  | X.a => Y.x
  | X.a₁ => Y.y
  | X.a₂ => Y.w
  | X.a₃ => Y.x
  | X.a₄ => Y.y
  | X.b => Y.y
  | X.c => Y.w
  | X.d => Y.l
  | X.d₁ => Y.m

def f₈' : Xα ⟶ Yβ :=
  ⟨f₈, by
    ext x
    simp only [types_comp_apply, Xα, Yβ, α, β, f₈]
    grind
  ⟩

def f₉ : Xα.carrier ⟶ Yβ.carrier
  | X.a => Y.w
  | X.a₁ => Y.x
  | X.a₂ => Y.y
  | X.a₃ => Y.w
  | X.a₄ => Y.x
  | X.b => Y.x
  | X.c => Y.y
  | X.d => Y.l
  | X.d₁ => Y.m

def f₉' : Xα ⟶ Yβ :=
  ⟨f₉, by
    ext x
    simp only [types_comp_apply, Xα, Yβ, α, β, f₉]
    grind
  ⟩

def f₁₀ : Xα.carrier ⟶ Yβ.carrier
  | X.a => Y.w
  | X.a₁ => Y.x
  | X.a₂ => Y.y
  | X.a₃ => Y.w
  | X.a₄ => Y.x
  | X.b => Y.x
  | X.c => Y.y
  | X.d => Y.m
  | X.d₁ => Y.l

def f₁₀' : Xα ⟶ Yβ :=
  ⟨f₁₀, by
    ext x
    simp only [types_comp_apply, Xα, Yβ, α, β, f₁₀]
    grind
  ⟩

def f₁₁ : Xα.carrier ⟶ Yβ.carrier
  | X.a => Y.w
  | X.a₁ => Y.x
  | X.a₂ => Y.y
  | X.a₃ => Y.w
  | X.a₄ => Y.x
  | X.b => Y.z
  | X.c => Y.y
  | X.d => Y.l
  | X.d₁ => Y.m

def f₁₁' : Xα ⟶ Yβ :=
  ⟨f₁₁, by
    ext x
    simp only [types_comp_apply, Xα, Yβ, α, β, f₁₁]
    grind
  ⟩

def f₁₂ : Xα.carrier ⟶ Yβ.carrier
  | X.a => Y.w
  | X.a₁ => Y.x
  | X.a₂ => Y.y
  | X.a₃ => Y.w
  | X.a₄ => Y.x
  | X.b => Y.z
  | X.c => Y.y
  | X.d => Y.m
  | X.d₁ => Y.l

def f₁₂' : Xα ⟶ Yβ :=
  ⟨f₁₂, by
    ext x
    simp only [types_comp_apply, Xα, Yβ, α, β, f₁₂]
    grind
  ⟩

-- expose the finite/decidable structure of the (def-wrapped) carriers and of
-- the categorical hom type `⟶` (which is defeq to `→` but not syntactically)
instance : Fintype Xα.carrier := inferInstanceAs (Fintype X)
instance : DecidableEq Xα.carrier := inferInstanceAs (DecidableEq X)
instance : DecidableEq Yβ.carrier := inferInstanceAs (DecidableEq Y)
instance : DecidableEq (Xα.carrier ⟶ Yβ.carrier) :=
  inferInstanceAs (DecidableEq (Xα.carrier → Yβ.carrier))

example : List.Pairwise (· ≠ ·)
  [ f₁, f₂, f₃, f₄, f₅, f₆, f₇, f₈, f₉, f₁₀, f₁₁, f₁₂ ] := by decide

set_option maxRecDepth 4000 in
example (f : Xα ⟶ Yβ) : f = f₁' ∨ f = f₂' ∨ f = f₃' ∨ f = f₄' ∨ f = f₅'
    ∨ f = f₆' ∨ f = f₇' ∨ f = f₈' ∨ f = f₉' ∨ f = f₁₀'
    ∨ f = f₁₁' ∨ f = f₁₂' := by
  obtain ⟨g, hg⟩ := f
  have ha := congr_fun hg X.a
  have ha1 := congr_fun hg X.a₁
  have ha2 := congr_fun hg X.a₂
  have ha3 := congr_fun hg X.a₃
  have ha4 := congr_fun hg X.a₄
  have hb := congr_fun hg X.b
  have hc := congr_fun hg X.c
  have hd := congr_fun hg X.d
  have hd1 := congr_fun hg X.d₁
  simp only [Xα, Yβ, α, types_comp_apply] at ha ha1 ha2 ha3 ha4 hb hc hd hd1
  -- Structure preservation (the recurring theme of the section): a map of endomaps
  -- carries `α`-relations to `β`-relations.  Here `α⁵ a = α² a` (both are `a₂`),
  -- so `β⁵ (g a) = β² (g a)` — which already cuts `g a` down to four values.
  have hb2 : β (β (g X.a)) = g X.a₂ := by rw [← ha, ← ha1]
  have hb5 : β (β (β (β (β (g X.a))))) = g X.a₂ := by rw [← ha, ← ha1, ← ha2, ← ha3, ← ha4]
  have hga4 : g X.a = Y.w ∨ g X.a = Y.x ∨ g X.a = Y.y ∨ g X.a = Y.z := by
    have hper := hb2.trans hb5.symm
    rcases hh : g X.a <;> simp [hh, β] at hper ⊢
  -- Unfold `β` in the remaining constraints so `grind` can case-split `g b, g c, g d`.
  simp only [β] at ha ha1 ha2 ha3 ha4 hb hc hd hd1
  -- Reduce to the *pointwise* classification as ground conjunctions (one per map),
  -- so the whole thing stays inside `grind`'s ground reasoning.
  -- `agree fᵢ` abbreviates "`g` agrees with `fᵢ` on all nine generators".
  let agree : (Xα.carrier ⟶ Yβ.carrier) → Prop := fun fi =>
    g X.a = fi X.a ∧ g X.a₁ = fi X.a₁ ∧ g X.a₂ = fi X.a₂ ∧ g X.a₃ = fi X.a₃
      ∧ g X.a₄ = fi X.a₄ ∧ g X.b = fi X.b ∧ g X.c = fi X.c ∧ g X.d = fi X.d
      ∧ g X.d₁ = fi X.d₁
  have unpack : ∀ {fi : Xα.carrier ⟶ Yβ.carrier} (hi), agree fi → (⟨g, hg⟩ : Xα ⟶ Yβ) = ⟨fi, hi⟩ :=
    fun hi h => Subtype.ext (funext fun x => by
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := h; cases x <;> assumption)
  suffices h : agree f₁ ∨ agree f₂ ∨ agree f₃ ∨ agree f₄ ∨ agree f₅ ∨ agree f₆
      ∨ agree f₇ ∨ agree f₈ ∨ agree f₉ ∨ agree f₁₀ ∨ agree f₁₁ ∨ agree f₁₂ by
    rcases h with h|h|h|h|h|h|h|h|h|h|h|h
    · exact Or.inl (unpack f₁'.property h)
    · exact Or.inr (Or.inl (unpack f₂'.property h))
    · exact Or.inr (Or.inr (Or.inl (unpack f₃'.property h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (unpack f₄'.property h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (unpack f₅'.property h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (unpack f₆'.property h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (unpack f₇'.property h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (unpack f₈'.property h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (unpack f₉'.property h)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (unpack f₁₀'.property h))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (unpack f₁₁'.property h)))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (unpack f₁₂'.property h)))))))))))
  -- Only four starting values remain (instead of thirteen); fixing `g a` forces
  -- the whole `a`-chain by forward evaluation, then `grind` settles `g b, g c, g d`.
  simp only [agree]
  rcases hga4 with h | h | h | h <;> simp only [h] at ha <;>
    grind [f₁, f₂, f₃, f₄, f₅, f₆, f₇, f₈, f₉, f₁₀, f₁₁, f₁₂]

end Ex15_7

/-!
Exercise 15.12 (p. 186)
-/
end CM

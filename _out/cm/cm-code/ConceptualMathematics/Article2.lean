import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise II.1 (p. 41)
-/
namespace ExII_1

variable {𝒞 : Type u} [Category.{v, u} 𝒞] {A B C : 𝒞}

example : IsIso (𝟙 A) := by
  use 𝟙 A
  constructor <;> exact Category.id_comp (𝟙 A)

example (f : A ⟶ B) (_ : IsIso f)
    (g : B ⟶ A) (hg : g ⊚ f = 𝟙 A ∧ f ⊚ g = 𝟙 B)
    : IsIso g := by
  use f
  exact ⟨hg.2, hg.1⟩

example (f : A ⟶ B) (hf : IsIso f) (k : B ⟶ C) (hk : IsIso k)
    : IsIso (k ⊚ f) := by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨kinv, hkinv⟩ := hk
  use finv ⊚ kinv
  constructor
  · rw [Category.assoc, ← Category.assoc k]
    rw [hkinv.1, Category.id_comp, hfinv.1]
  · rw [Category.assoc, ← Category.assoc finv]
    rw [hfinv.2, Category.id_comp, hkinv.2]

end ExII_1

/-!
Exercise II.2 (p. 42)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞} (f : A ⟶ B)
    (g : B ⟶ A) (hg : g ⊚ f = 𝟙 A ∧ f ⊚ g = 𝟙 B)
    (k : B ⟶ A) (hk : k ⊚ f = 𝟙 A ∧ f ⊚ k = 𝟙 B)
    : g = k := by
  calc
    g = 𝟙 A ⊚ g := by rw [Category.comp_id]
    _ = (k ⊚ f) ⊚ g := by rw [hk.1]
    _ = k ⊚ (f ⊚ g) := by rw [Category.assoc]
    _ = k ⊚ 𝟙 B := by rw [hg.2]
    _ = k := by rw [Category.id_comp]

/-!
Exercise II.3 (p. 43)
-/
namespace ExII_3

variable {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞}

example (f : A ⟶ B)
    (hf : ∃ finv : B ⟶ A, finv ⊚ f = 𝟙 A ∧ f ⊚ finv = 𝟙 B)
    (h : B ⟶ A) (k : B ⟶ A)
    : f ⊚ h = f ⊚ k → h = k := by
  obtain ⟨finv, hfinv₁, hfinv₂⟩ := hf
  intro h₁
  have h₂ : finv ⊚ f ⊚ h = finv ⊚ f ⊚ k := by rw [h₁]
  repeat rw [Category.assoc] at h₂
  rw [hfinv₁] at h₂
  repeat rw [Category.comp_id] at h₂
  exact h₂

example (f : A ⟶ B)
    (hf : ∃ finv : B ⟶ A, finv ⊚ f = 𝟙 A ∧ f ⊚ finv = 𝟙 B)
    (h : B ⟶ A) (k : B ⟶ A)
    : h ⊚ f = k ⊚ f → h = k := by
  obtain ⟨finv, hfinv₁, hfinv₂⟩ := hf
  intro h₁
  have h₂ : (h ⊚ f) ⊚ finv = (k ⊚ f) ⊚ finv := by rw [h₁]
  repeat rw [← Category.assoc] at h₂
  rw [hfinv₂] at h₂
  repeat rw [Category.id_comp] at h₂
  exact h₂

def f : Fin 2 ⟶ Fin 2
  | 0 => 1
  | 1 => 0

example : f ⊚ f = 𝟙 (Fin 2) := by
  funext x
  fin_cases x <;> dsimp [f]

def h : Fin 2 ⟶ Fin 2
  | 0 => 1
  | 1 => 1

def k : Fin 2 ⟶ Fin 2
  | 0 => 0
  | 1 => 0

example : ¬(h ⊚ f = f ⊚ k → h = k) := by
  push Not
  constructor
  · funext x
    fin_cases x <;> dsimp [f, h, k]
  · by_contra h₀
    have h₁ : h 0 = 1 := rfl
    have h₂ : k 0 = 0 := rfl
    rw [← h₀, h₁] at h₂
    contradiction

end ExII_3

/-!
Exercise II.4 (p. 44)
-/
example (f : ℝ → ℝ) (hf : ∀ x : ℝ, f x = 3 * x + 7)
    : ∃ finv : ℝ → ℝ, finv ∘ f = id ∧ f ∘ finv = id := by
  use fun x ↦ (x - 7) / 3 -- f⁻¹(x)
  constructor
  · funext x
    rw [Function.comp_apply, id_eq, hf x]
    ring
  · funext x
    rw [Function.comp_apply, id_eq, hf ((x - 7) / 3)]
    ring

open NNReal in
example (g : ℝ≥0 → ℝ≥0) (hg : ∀ x : ℝ≥0, g x = x * x)
  : ∃ ginv : ℝ≥0 → ℝ≥0, ginv ∘ g = id ∧ g ∘ ginv = id := by
  use fun x ↦ NNReal.sqrt x -- g⁻¹(x)
  constructor
  · funext x
    rw [Function.comp_apply, id_eq, hg x]
    exact NNReal.sqrt_mul_self x
  · funext x
    rw [Function.comp_apply, id_eq, hg (sqrt x)]
    exact mul_self_sqrt x

example (h : ℝ → ℝ) (hh : ∀ x : ℝ, h x = x * x)
    : ¬(∃ hinv : ℝ → ℝ, hinv ∘ h = id ∧ h ∘ hinv = id) := by
  push Not
  intro hinv h_inv_left _
  have h₁ : h 1 = 1 := by
    rw [hh 1]
    norm_num1
  have h₂ : h (-1) = 1 := by
    rw [hh (-1)]
    norm_num1
  have h₃ : (hinv ∘ h) 1 = 1:= by
    rw [h_inv_left, id_eq]
  have h₄ : (hinv ∘ h) (-1) = -1 := by
    rw [h_inv_left, id_eq]
  dsimp at h₃ h₄
  rw [h₁] at h₃
  rw [h₂] at h₄
  linarith

open NNReal in
example (k : ℝ → ℝ≥0) (hk : ∀ x : ℝ, k x = x * x)
    : ¬(∃ kinv : ℝ≥0 → ℝ, kinv ∘ k = id ∧ k ∘ kinv = id) := by
  push Not
  intro kinv h_inv_left _
  have h₁ : k 1 = 1 := by
    rw [← coe_eq_one, hk 1]
    norm_num1
  have h₂ : k (-1) = 1 := by
    rw [← coe_eq_one, hk (-1)]
    norm_num1
  have h₃ : (kinv ∘ k) 1 = 1:= by
    rw [h_inv_left, id_eq]
  have h₄ : (kinv ∘ k) (-1) = -1 := by
    rw [h_inv_left, id_eq]
  dsimp at h₃ h₄
  rw [h₁] at h₃
  rw [h₂] at h₄
  linarith

/-!
Chad's formula
-/
def Chad's_formula {α χ : Type*} [DecidableEq α]
    [Fintype α] [Fintype χ] (X : Finset χ) (A : Finset α)
    (p : χ → α)
    : ℕ :=
  ∏ a ∈ A, pinvCount a
where
  pinvCount (a : α) : ℕ := X.filter (fun x ↦ p x = a) |>.card

/-!
Danilo's formula
-/
open Finset in
def Danilo's_formula {α χ : Type*}
    [Fintype α] [Fintype χ] (A : Finset α) (X : Finset χ)
    (j : α → χ) (p : χ → α) (_ : p ∘ j = id) (_ : Function.Injective j)
    : ℕ :=
  #A ^ (#X - #A)

/-!
Exercise II.5 (p. 47)
-/
namespace ExII_5

inductive XElems
  | b | p | q | r | s
  deriving Fintype

def A : Finset (Fin 2) := Finset.univ
def X : Finset XElems := Finset.univ

open XElems in
def g : XElems → Fin 2
  | b => 0
  | p => 0
  | q => 0
  | r => 1
  | s => 1

#eval Chad's_formula X A g

open XElems in
def f : Fin 2 → XElems
  | 0 => b
  | 1 => r

#eval Danilo's_formula A X f g
  (by
    funext x
    fin_cases x <;> rfl)
  (by
    intro x y _
    fin_cases x <;> fin_cases y
    all_goals
      first | rfl
            | simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
                         zero_ne_one]; trivial)

end ExII_5

/-!
Retraction, IsRetraction
-/
abbrev Retraction {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞}
    (f : A ⟶ B) :=
  SplitMono f
abbrev IsRetraction {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞}
    (f : A ⟶ B) :=
  IsSplitMono f

/-!
Section, IsSection
-/
abbrev Section {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞}
    (f : A ⟶ B) :=
  SplitEpi f
abbrev IsSection {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞}
    (f : A ⟶ B) :=
  IsSplitEpi f

/-!
Proposition 1 (p. 51)
-/
theorem prop1 {𝒞 : Type u} [Category.{v, u} 𝒞] {A B T : 𝒞}
    (f : A ⟶ B) [hf : IsSection f]
    : ∀ y : T ⟶ B, ∃ x : T ⟶ A, f ⊚ x = y := by
  obtain ⟨s, hf⟩ := hf
  intro y
  use s ⊚ y
  rw [Category.assoc]
  rw [hf]
  exact Category.comp_id y

/-!
Exercise II.6 (Proposition 1*) (p. 52)
-/
theorem «prop1*» {𝒞 : Type u} [Category.{v, u} 𝒞] {A B T : 𝒞}
    (f : A ⟶ B) [hf : IsRetraction f]
    : ∀ g : A ⟶ T, ∃ t : B ⟶ T, t ⊚ f = g := by
  obtain ⟨r, hf⟩ := hf
  intro g
  use g ⊚ r
  rw [← Category.assoc, hf, Category.id_comp]

/-!
Proposition 2 (p. 52)
-/
theorem prop2 {𝒞 : Type u} [Category.{v, u} 𝒞] {A B T : 𝒞}
    (f : A ⟶ B) [hf : IsRetraction f]
    : ∀ x₁ x₂ : T ⟶ A, f ⊚ x₁ = f ⊚ x₂ → x₁ = x₂ := by
  obtain ⟨r, hf⟩ := hf
  intro x₁ x₂ h
  rw [← Category.comp_id x₁]
  rw [← hf]
  rw [← Category.assoc]
  rw [h]
  rw [Category.assoc]
  rw [hf]
  exact Category.comp_id x₂

/-!
Exercise II.7 (Proposition 2*) (p. 53)
-/
theorem «prop2*» {𝒞 : Type u} [Category.{v, u} 𝒞] {A B T : 𝒞}
    (f : A ⟶ B) [hf : IsSection f]
    : ∀ t₁ t₂ : B ⟶ T, t₁ ⊚ f = t₂ ⊚ f → t₁ = t₂ := by
  obtain ⟨s, hf⟩ := hf
  intro t₁ t₂ h
  rw [← Category.id_comp t₁, ← hf]
  rw [Category.assoc, h, ← Category.assoc]
  rw [hf, Category.id_comp]

/-!
cancel_mono, cancel_epi
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] {X Y Z : 𝒞}
    (f : X ⟶ Y) [Mono f] {g h : Z ⟶ X}
    : f ⊚ g = f ⊚ h ↔ g = h := cancel_mono f

example {𝒞 : Type u} [Category.{v, u} 𝒞] {X Y Z : 𝒞}
    (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z}
    : g ⊚ f = h ⊚ f ↔ g = h := cancel_epi f

/-!
Proposition 3 (p. 53)
-/
theorem prop3 {𝒞 : Type u} [Category.{v, u} 𝒞] {A B C : 𝒞}
    (f : A ⟶ B) [hf : IsRetraction f] (g : B ⟶ C) [hg : IsRetraction g]
    : IsRetraction (g ⊚ f) := by
  obtain ⟨r₁, hf⟩ := hf
  obtain ⟨r₂, hg⟩ := hg
  use r₁ ⊚ r₂
  change (r₁ ⊚ r₂) ⊚ (g ⊚ f) = 𝟙 A
  rw [Category.assoc, ← Category.assoc g]
  rw [hg]
  rw [Category.id_comp]
  exact hf

/-!
instIsSplitMonoComp
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A B C : 𝒞}
    (f : A ⟶ B) [hf : IsRetraction f] (g : B ⟶ C) [hg : IsRetraction g]
    : IsRetraction (g ⊚ f) := instIsSplitMonoComp

/-!
Exercise II.8 (p. 54)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A B C : 𝒞}
    (f : A ⟶ B) [hf : IsSection f] (g : B ⟶ C) [hg : IsSection g]
    : IsSection (g ⊚ f) := by
  obtain ⟨s₁, hf⟩ := hf
  obtain ⟨s₂, hg⟩ := hg
  use s₁ ⊚ s₂
  change (g ⊚ f) ⊚ (s₁ ⊚ s₂) = 𝟙 C
  rw [Category.assoc, ← Category.assoc s₁]
  rw [hf]
  rw [Category.id_comp]
  exact hg

/-!
instIsSplitEpiComp
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A B C : 𝒞}
    (f : A ⟶ B) [hf : IsSection f] (g : B ⟶ C) [hg : IsSection g]
    : IsSection (g ⊚ f) := instIsSplitEpiComp

/-!
Idempotent, IsIdempotent
-/
structure Idempotent {𝒞 : Type u} [Category.{v, u} 𝒞] (A : 𝒞) where
  e : A ⟶ A
  idem : e ⊚ e = e

class IsIdempotent {𝒞 : Type u} [Category.{v, u} 𝒞] {A : 𝒞}
    (e : A ⟶ A) where
  idem : e ⊚ e = e

/-!
Exercise II.9 (p. 54)
-/
namespace ExII_9

variable {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞}
         (f : A ⟶ B) (e : B ⟶ B)

example (r : Retraction f) (he : e = f ⊚ r.retraction)
    : IsIdempotent e := {
  idem := by
    rw [he, Category.assoc, ← Category.assoc f, r.id,
        Category.id_comp]
}

example [hf : IsIso f]
    (r : Retraction f) (he : e = f ⊚ r.retraction)
    : e = 𝟙 B := by
  have ⟨finv, hfinv⟩ := hf
  rw [← hfinv.2, ← Category.id_comp f, ← r.id]
  repeat rw [← Category.assoc]
  rwa [hfinv.2, Category.id_comp]

end ExII_9

/-!
Theorem (uniqueness of inverses) (p. 54)
-/
theorem uniqueness_of_inverses {𝒞 : Type u} [Category.{v, u} 𝒞]
    {A B : 𝒞} (f : A ⟶ B) (r : Retraction f) (s : Section f)
    : r.retraction = s.section_ := by
  obtain ⟨r, hr⟩ := r
  obtain ⟨s, hs⟩ := s
  change r = s
  calc
    r = r ⊚ 𝟙 B := by rw [Category.id_comp]
    _ = r ⊚ (f ⊚ s) := by rw [hs]
    _ = (r ⊚ f) ⊚ s := by rw [← Category.assoc]
    _ = 𝟙 A ⊚ s := by rw [← hr]
    _ = s := Category.comp_id s

/-!
Equivalency of two definitions of isomorphism (pp. 54 & 40)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞}
    (f : A ⟶ B) (r : Retraction f) (s : Section f)
    : r.retraction = s.section_ ↔ IsIso f := by
  constructor
  · intro h
    exact {
      out := by
        use r.retraction
        constructor
        · exact r.id
        · rw [h]
          exact s.id
    }
  · rintro ⟨finv, hfinv⟩
    obtain ⟨r, hr⟩ := r
    obtain ⟨s, hs⟩ := s
    change r = s
    calc
      r = r ⊚ 𝟙 B := by rw [Category.id_comp]
      _ = r ⊚ (f ⊚ s) := by rw [hs]
      _ = (r ⊚ f) ⊚ s := by rw [← Category.assoc]
      _ = 𝟙 A ⊚ s := by rw [← hr]
      _ = s := Category.comp_id s

/-!
Exercise II.10 (p. 55)
-/
open CategoryTheory in
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A B C : 𝒞}
    (f : A ⟶ B) [hf : IsIso f] (g : B ⟶ C) [hg : IsIso g]
    : IsIso (g ⊚ f) ∧ inv (g ⊚ f) = inv f ⊚ inv g := by
  constructor
  · obtain ⟨finv, hfinv⟩ := hf
    obtain ⟨ginv, hginv⟩ := hg
    exact {
      out := by
        use finv ⊚ ginv
        constructor
        · rw [Category.assoc, ← Category.assoc g]
          rw [hginv.1]
          rw [Category.id_comp]
          exact hfinv.1
        · rw [Category.assoc, ← Category.assoc finv]
          rw [hfinv.2]
          rw [Category.id_comp]
          exact hginv.2
    }
  · exact IsIso.inv_comp

/-!
Exercise II.11 (p. 55)
-/
namespace ExII_11

inductive A
  | Fatima | Omer | Alysia
  deriving Fintype

inductive B
  | coffee | tea | cocoa
  deriving Fintype

def f : A ⟶ B
  | A.Fatima => B.coffee
  | A.Omer => B.tea
  | A.Alysia => B.cocoa

def finv : B ⟶ A
  | B.coffee => A.Fatima
  | B.tea => A.Omer
  | B.cocoa => A.Alysia

example : IsIso f := {
  out := by
    use finv
    constructor
    all_goals
      funext x
      fin_cases x <;> dsimp [f, finv]
}

end ExII_11

/-!
Exercise II.12 (p. 56), isoCount, autCount
-/
def isoCount (α β : Type*) [Fintype α] [Fintype β] : ℕ :=
  if Fintype.card α = Fintype.card β then
    Nat.factorial (Fintype.card α)
  else
    0

open ExII_11

#eval isoCount A B

abbrev autCount (α : Type*) [Fintype α] := isoCount α α

open ExII_11

#eval autCount A

/-!
permCount
-/
def permCount {α : Type*} (s : Finset α) : ℕ :=
  if 0 < Finset.card s then
    Nat.factorial (Finset.card s)
  else
    0

open ExII_11

#eval permCount (Finset.univ (α := A))

end CM


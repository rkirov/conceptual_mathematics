import Mathlib
open CategoryTheory
namespace CM
-- flip the order to match the book.
local notation:80 g " ⊚ " f:80 => f ≫ g

/-!
Exercise II.1 (p. 41)
-/
namespace ExII_1

variable {𝒞 : Type u} [Category.{v, u} 𝒞] {A B C : 𝒞}

example : IsIso (𝟙 A) := IsIso.mk (by
  use 𝟙 A
  constructor
  · rw [Category.id_comp]
  · rw [Category.comp_id]
)

example (f : A ⟶ B) (_ : IsIso f)
    (g : B ⟶ A) (hg : g ⊚ f = 𝟙 A ∧ f ⊚ g = 𝟙 B)
    : IsIso g := IsIso.mk (by
  use f
  constructor
  · exact hg.2
  · exact hg.1
)


example (f : A ⟶ B) (hf : IsIso f) (k : B ⟶ C) (hk : IsIso k)
    : IsIso (k ⊚ f) := IsIso.mk (by
  use (hf.1.choose ⊚ hk.1.choose)
  have ⟨h1, h2⟩ := hf.1.choose_spec
  have ⟨h3, h4⟩ := hk.1.choose_spec
  constructor
  · rw [Category.assoc, ← Category.assoc k _, h3, Category.id_comp, h1]
  · rw [Category.assoc, ← Category.assoc _ f, h2, Category.id_comp, h4]
)

end ExII_1

/-!
Exercise II.2 (p. 42)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞} (f : A ⟶ B)
    (g : B ⟶ A) (hg : g ⊚ f = 𝟙 A ∧ f ⊚ g = 𝟙 B)
    (k : B ⟶ A) (hk : k ⊚ f = 𝟙 A ∧ f ⊚ k = 𝟙 B)
    : g = k := by
  have h : g ⊚ f ⊚ k = g ⊚ f ⊚ k := rfl
  conv_lhs at h => rw [hk.2, Category.id_comp]
  conv_rhs at h => rw [Category.assoc, hg.1, Category.comp_id]
  exact h

/-!
Exercise II.3 (p. 43)
-/
namespace ExII_3

variable {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞}

example (f : A ⟶ B) (hf : IsIso f) (h : B ⟶ A) (k : B ⟶ A)
    : f ⊚ h = f ⊚ k → h = k := by
  obtain ⟨f', hf'⟩ := hf
  intro hk
  have := congrArg (f' ⊚ ·) hk
  simp only [Category.assoc] at this
  rw [hf'.1, Category.comp_id, Category.comp_id] at this
  exact this

example (f : A ⟶ B) (hf : IsIso f) (h : B ⟶ A) (k : B ⟶ A)
    : h ⊚ f = k ⊚ f → h = k := by
  obtain ⟨f', hf'⟩ := hf
  intro hk
  have := congrArg (· ⊚ f') hk
  simp only at this
  rw [← Category.assoc, ← Category.assoc, hf'.2, Category.id_comp, Category.id_comp] at this
  exact this

-- we will use the category of Lean types
example : ∃ A : Type, ∃ f : A ⟶ A,
    IsIso f ∧ ∃ h, ∃ k, h ⊚ f = f ⊚ k ∧ h ≠ k := by
  let f : Fin 2 → Fin 2
    | 0 => 1
    | 1 => 0
  use Fin 2
  use f
  constructor
  · exact IsIso.mk (by
      use f
      constructor <;> (funext x; fin_cases x <;> simp [f])
    )
  · let h : Fin 2 → Fin 2
    | 0 => 0
    | 1 => 0
    let k : Fin 2 → Fin 2
      | 0 => 1
      | 1 => 1
    use h, k
    constructor
    · funext x; fin_cases x <;> simp [h, k, f]
    · intro hneq
      have h0 : h 0 = k 0 := congr_fun hneq 0
      simp [h, k]at h0

end ExII_3

/-!
Exercise II.4 (p. 44)
-/
example (f : ℝ → ℝ) (hf : ∀ x : ℝ, f x = 3 * x + 7)
    : Decidable (∃ finv : ℝ → ℝ, finv ∘ f = id ∧ f ∘ finv = id) := by
  apply isTrue
  use (fun x => (x - 7) / 3)
  constructor
  · funext x; simp [hf]
  · funext x; simp [hf]; field_simp [hf]; simp

open NNReal in
example (g : ℝ≥0 → ℝ≥0) (hg : ∀ x : ℝ≥0, g x = x * x)
  : Decidable (∃ ginv : ℝ≥0 → ℝ≥0, ginv ∘ g = id ∧ g ∘ ginv = id) := by
  apply isTrue
  use (fun x => sqrt x)
  constructor <;> (funext x; simp [hg])

example (h : ℝ → ℝ) (hh : ∀ x : ℝ, h x = x * x)
    : Decidable (∃ hinv : ℝ → ℝ, hinv ∘ h = id ∧ h ∘ hinv = id) := by
  apply isFalse
  intro hexists
  obtain ⟨hinv, ⟨hcomp1, hcomp2⟩⟩ := hexists
  have h1 := congr_fun hcomp1 (-1)
  simp [hh] at h1
  have h1' := congr_fun hcomp1 1
  simp [hh] at h1'
  linarith

open NNReal in
example (k : ℝ → ℝ≥0) (hk : ∀ x : ℝ, k x = x * x)
    : Decidable (∃ kinv : ℝ≥0 → ℝ, kinv ∘ k = id ∧ k ∘ kinv = id) := by
  apply isFalse
  intro hexists
  obtain ⟨kinv, ⟨kcomp1, kcomp2⟩⟩ := hexists
  have hk0 := congr_fun kcomp1 (-1)
  have : k (-1) = 1 := by apply NNReal.coe_injective; simp [hk]
  simp [this] at hk0
  have hk1 := congr_fun kcomp1 1
  have : k 1 = 1 := by apply NNReal.coe_injective; simp [hk]
  simp [this] at hk1
  linarith

/-!
Chad's formula for number of secions of a function.
-/
def Chad's_formula {α β : Type*} [DecidableEq α]
    [Fintype α] [Fintype β] (g : β → α) : ℕ :=
  ∏ a : α, pinvCount a
where
  pinvCount (a : α) : ℕ := Finset.univ.filter (fun x ↦ g x = a) |>.card

theorem Chad's_formula_correct {α β : Type*} [DecidableEq α] [Fintype α] [Fintype β]
  (g : β → α) : Chad's_formula g = Fintype.card {f : α → β // g ∘ f = id} := by
  have e : {f : α → β // g ∘ f = id} ≃ ∀ a : α, {b : β // g b = a} :=
    (Equiv.subtypeEquivRight (fun f ↦ by simp [funext_iff])).trans Equiv.subtypePiEquivPi
  rw [Fintype.card_congr e, Fintype.card_pi]
  simp only [Chad's_formula, Chad's_formula.pinvCount, Fintype.card_subtype]

/-!
Danilo's formula for number of retractions for fixed section.
-/
def Danilo's_formula {α β : Type*} [DecidableEq α]
    [Fintype α] [Fintype β]
    (j : α → β) (p : β → α) (_ : p ∘ j = id)
    : ℕ := Fintype.card α ^ (Fintype.card β - Fintype.card α)

theorem Danilo's_formula_correct {α β : Type*} [DecidableEq α] [DecidableEq β]
  [Fintype α] [Fintype β]
  (g : β → α) (f : α → β) (h : g ∘ f = id) :
  Danilo's_formula f g h = Fintype.card {g' : β → α // g' ∘ f = id} := by
  have hf : Function.Injective f := Function.LeftInverse.injective (fun a => congr_fun h a)
  have hgf : ∀ a, g (f a) = a := fun a => congr_fun h a
  -- A retraction g' agrees with g on the range of f and is arbitrary off it,
  -- so retractions correspond to functions from the complement of the range into α.
  let e : {g' : β → α // g' ∘ f = id} ≃ (((Set.range f)ᶜ : Set β) → α) :=
  { toFun := fun G b => G.1 b.1
    invFun := fun F => ⟨fun b => if hb : b ∈ Set.range f then g b else F ⟨b, hb⟩, by
      funext a
      change (if hb : f a ∈ Set.range f then g (f a) else F ⟨f a, hb⟩) = a
      rw [dif_pos ⟨a, rfl⟩]; exact hgf a⟩
    left_inv := by
      rintro ⟨G, hG⟩
      have hGf : ∀ a, G (f a) = a := fun a => congr_fun hG a
      ext b
      by_cases hb : b ∈ Set.range f
      · obtain ⟨a, rfl⟩ := hb
        change (if _ : f a ∈ Set.range f then g (f a) else _) = G (f a)
        rw [dif_pos ⟨a, rfl⟩, hgf a, hGf a]
      · change (if _ : b ∈ Set.range f then g b else _) = G b
        rw [dif_neg hb]
    right_inv := fun F => by
      funext b
      change (if hb : b.1 ∈ Set.range f then g b.1 else F ⟨b.1, hb⟩) = F b
      rw [dif_neg b.2] }
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_compl_set,
    Set.card_range_of_injective hf]
  rfl

/-!
Exercise II.5 (p. 47)
-/
namespace ExII_5

inductive X
  | b | p | q | r | s
  deriving Fintype

open X in
def g : X → Fin 2
  | b => 0
  | p => 0
  | q => 0
  | r => 1
  | s => 1

#eval Chad's_formula g

open X in
def f : Fin 2 → X
  | 0 => b
  | 1 => r

#eval Danilo's_formula f g
  (by
    funext x
    fin_cases x <;> rfl)

end ExII_5

/-!
Retraction, IsRetraction
In Mathlib it is called `SplitMono`.
-/
abbrev Retraction {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞}
    (f : A ⟶ B) := SplitMono f
abbrev IsRetraction {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞}
    (f : A ⟶ B) := IsSplitMono f

/-!
Section, IsSection
In Mathlib it is called `SplitEpi`.
-/
abbrev Section {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞}
    (f : A ⟶ B) := SplitEpi f
abbrev IsSection {𝒞 : Type u} [Category.{v, u} 𝒞] {A B : 𝒞}
    (f : A ⟶ B) := IsSplitEpi f

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
  rw [← Category.assoc]
  rw [hf]
  exact Category.id_comp g

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
  intro t₁ t₂ h
  obtain ⟨s, hf⟩ := hf
  have := congr_arg (· ⊚ s) h
  simp only at this
  rw [← Category.assoc,← Category.assoc, hf, Category.id_comp, Category.id_comp] at this
  exact this

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
    (f : A ⟶ B) (hf : IsRetraction f) (g : B ⟶ C) (hg : IsRetraction g)
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
This is instIsSplitMonoComp in mathlib
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A B C : 𝒞}
    (f : A ⟶ B) (hf : IsRetraction f) (g : B ⟶ C) (hg : IsRetraction g)
    : IsRetraction (g ⊚ f) := instIsSplitMonoComp

/-!
Exercise II.8 (p. 54)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A B C : 𝒞}
    (f : A ⟶ B) (hf : IsSection f) (g : B ⟶ C) (hg : IsSection g)
    : IsSection (g ⊚ f) := by
  obtain ⟨s, hf⟩ := hf
  obtain ⟨t, hg⟩ := hg
  use s ⊚ t
  change (g ⊚ f) ⊚ (s ⊚ t) = 𝟙 C
  rw [Category.assoc, ← Category.assoc s]
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

theorem is_idempotent (r : Retraction f) (he : e = f ⊚ r.retraction)
    : IsIdempotent e := by
  constructor
  rw [he]
  rw [Category.assoc, ← Category.assoc f, r.id, Category.id_comp]

example (r : Retraction f) (he : e = f ⊚ r.retraction) (hf : IsIso f)
    : e = 𝟙 B := by
  have ⟨g, hg, hg'⟩ := hf
  have hr := r.id
  have := congr_arg (fun x => x ⊚ g) hr
  simp only at this
  rw [Category.comp_id, ← Category.assoc, hg', Category.id_comp] at this
  rw [this, hg'] at he
  exact he

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
  · use inv f ⊚ inv g
    constructor
    · simp only [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id]
    · simp only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id]
  · simp only [IsIso.inv_comp]

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

inductive C
  | true | false
  deriving Fintype

example : Decidable (∃ f : A ⟶ B, IsIso f) := by
  apply isTrue
  let f : A ⟶ B
    | A.Fatima => B.coffee
    | A.Omer => B.tea
    | A.Alysia => B.cocoa

  let finv : B ⟶ A
    | B.coffee => A.Fatima
    | B.tea    => A.Omer
    | B.cocoa  => A.Alysia
  use f
  use finv
  constructor
  · ext x
    fin_cases x <;> rfl
  · ext x
    fin_cases x <;> rfl

example : Decidable (∃ f : A ⟶ C, IsIso f) := by
  apply isFalse
  push Not
  intro h
  by_contra h'
  have := Fintype.card_eq_of_iso h'
  norm_num

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
#eval isoCount A C

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

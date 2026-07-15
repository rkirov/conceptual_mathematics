import ConceptualMathematics.Sorried.Article2
import ConceptualMathematics.Sorried.Review
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Data.Fintype.Defs
import Mathlib.GroupTheory.Perm.Cycle.Type
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
The (concrete) category 𝑺↻ of endomaps of sets (pp. 136–137)
-/
structure SetWithEndomap where
  carrier : Type
  toEnd : carrier ⟶ carrier

def SetWithEndomapHom (X Y : SetWithEndomap) := {
  f : X.carrier ⟶ Y.carrier //
      f ⊚ X.toEnd = Y.toEnd ⊚ f -- commutes
}

def SetWithEndomapHom.id (X : SetWithEndomap)
    : SetWithEndomapHom X X := ⟨𝟙 X.carrier, rfl⟩

def SetWithEndomapHom.comp {X Y Z : SetWithEndomap}
    (f : SetWithEndomapHom X Y) (g : SetWithEndomapHom Y Z)
    : SetWithEndomapHom X Z := ⟨
  g.val ⊚ f.val,
  by
    have hf_comm := f.property
    have hg_comm := g.property
    rw [← Category.assoc, hf_comm, Category.assoc, hg_comm,
        ← Category.assoc]
⟩

instance instCatSetWithEndomap : Category SetWithEndomap where
  Hom := SetWithEndomapHom
  id := SetWithEndomapHom.id
  comp := SetWithEndomapHom.comp

instance {X Y : SetWithEndomap}
    : FunLike (instCatSetWithEndomap.Hom X Y) X.carrier
                                              Y.carrier where
  coe f := f.val
  coe_injective' := fun _ _ h ↦ Subtype.ext h

instance
    : ConcreteCategory SetWithEndomap instCatSetWithEndomap.Hom where
  hom f := f
  ofHom f := f

/-!
Exercise III.1 (p. 137)
-/
example {X Y Z : Type}
    (α : X ⟶ X) (β : Y ⟶ Y) (γ : Z ⟶ Z)
    (f : X ⟶ Y) (hf_comm : f ⊚ α = β ⊚ f)
    (g : Y ⟶ Z) (hg_comm : g ⊚ β = γ ⊚ g)
    : (g ⊚ f) ⊚ α = γ ⊚ (g ⊚ f) := by
  rw [← Category.assoc, hf_comm, Category.assoc, hg_comm]
  rw [Category.assoc]

example {X Y Z : SetWithEndomap} (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ Z :=
  SetWithEndomapHom.comp f g

/-!
The (concrete) category 𝑺ᵉ of idempotent endomaps of sets (p. 138)
-/
structure SetWithIdemEndomap extends SetWithEndomap where
  idem : toEnd ⊚ toEnd = toEnd

instance instCatSetWithIdemEndomap : Category SetWithIdemEndomap where
  Hom X Y := SetWithEndomapHom X.toSetWithEndomap Y.toSetWithEndomap
  id X := SetWithEndomapHom.id X.toSetWithEndomap
  comp := SetWithEndomapHom.comp

instance {X Y : SetWithIdemEndomap}
    : FunLike (instCatSetWithIdemEndomap.Hom X Y) X.carrier
                                                  Y.carrier where
  coe f := f.val
  coe_injective' := fun _ _ h ↦ Subtype.ext h

instance
    : ConcreteCategory SetWithIdemEndomap instCatSetWithIdemEndomap.Hom
    where
  hom f := f
  ofHom f := f

/-!
The (concrete) category 𝑺◯ of invertible endomaps of sets (p. 138)
-/
structure SetWithInvEndomap extends SetWithEndomap where
  inv : ∃ inv, inv ⊚ toEnd = 𝟙 carrier ∧ toEnd ⊚ inv = 𝟙 carrier

instance instCatSetWithInvEndomap : Category SetWithInvEndomap where
  Hom X Y := SetWithEndomapHom X.toSetWithEndomap Y.toSetWithEndomap
  id X := SetWithEndomapHom.id X.toSetWithEndomap
  comp := SetWithEndomapHom.comp

instance {X Y : SetWithInvEndomap}
    : FunLike (instCatSetWithInvEndomap.Hom X Y) X.carrier
                                                 Y.carrier where
  coe f := f.val
  coe_injective' := fun _ _ h ↦ Subtype.ext h

instance
    : ConcreteCategory SetWithInvEndomap instCatSetWithInvEndomap.Hom
    where
  hom f := f
  ofHom f := f

/-!
The (concrete) category 𝑪↻ of endomaps (pp. 138–139)
-/
abbrev Endomap := SetWithEndomap

/-!
The (concrete) category 𝑪ᵉ of idempotents (pp. 138–139)
-/
abbrev IdemEndomap := SetWithIdemEndomap

/-!
The (concrete) category 𝑪◯ of isomorphic endomaps (pp. 138–139)
-/
abbrev InvEndomap := SetWithInvEndomap

/-!
The (concrete) category 𝑪ᶿ of involutions (pp. 138–139)
-/
structure InvolEndomap extends SetWithInvEndomap where
  invol : toEnd ⊚ toEnd = 𝟙 carrier

instance instCatInvolEndomap : Category InvolEndomap where
  Hom X Y := SetWithEndomapHom X.toSetWithEndomap Y.toSetWithEndomap
  id X := SetWithEndomapHom.id X.toSetWithEndomap
  comp := SetWithEndomapHom.comp

instance {X Y : InvolEndomap}
    : FunLike (instCatInvolEndomap.Hom X Y) X.carrier Y.carrier where
  coe f := f.val
  coe_injective' := fun _ _ h ↦ Subtype.ext h

instance : ConcreteCategory InvolEndomap instCatInvolEndomap.Hom where
  hom f := f
  ofHom f := f

example {𝒞 : Type u} [Category.{v, u} 𝒞] {A : 𝒞} {α β : A ⟶ A}
    (h_idem : α ⊚ α = α) (h_section : α ⊚ β = 𝟙 A)
    : α = 𝟙 A := by
  have := congr_arg (· ⊚ β) h_idem
  simp only at this
  rw [← Category.assoc, h_section] at this
  simp only [Category.id_comp] at this
  exact this

/-!
Exercise III.2 (p. 139)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A : 𝒞} {α β : A ⟶ A}
    (h_idem : α ⊚ α = α) (h_retraction : β ⊚ α = 𝟙 A)
    : α = 𝟙 A := by
  have := congr_arg (β ⊚ ·) h_idem
  simp only at this
  rw [Category.assoc, h_retraction] at this
  simp only [Category.comp_id] at this
  exact this

/-!
Exercise III.3 (p. 140)
-/
def isInvo {α : Type} [Fintype α] (f : α → α) : Prop := f ∘ f = id

def isEven (α : Type) [Fintype α] [DecidableEq α] : Prop := ∃ f : α → α, isInvo f ∧
  (Finset.card {x : α | f x = x }) = 0

def isOdd (α : Type) [Fintype α] [DecidableEq α] : Prop := ∃ f : α → α, isInvo f ∧
  (Finset.card {x : α | f x = x }) = 1

-- Involution principle: an involution pairs up the non-fixed points, so the
-- cardinality has the same parity as the number of fixed points.
private theorem card_modEq_card_fixed {α : Type} [Fintype α] [DecidableEq α]
    {f : α → α} (hf : Function.Involutive f) :
    Fintype.card α ≡ (Finset.card {x : α | f x = x}) [MOD 2] := by
  have hsq : (Function.Involutive.toPerm f hf) ^ 2 = 1 := by
    ext x; simp [pow_two, Function.Involutive.coe_toPerm, hf x]
  have hdvd := Equiv.Perm.two_dvd_card_support hsq
  have hsupp : (Function.Involutive.toPerm f hf).support
      = Finset.univ.filter (fun x => ¬ f x = x) := by
    ext x; simp [Equiv.Perm.mem_support, Function.Involutive.coe_toPerm]
  rw [hsupp] at hdvd
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset α)) (fun x => f x = x)
  rw [Finset.card_univ] at hsplit
  rw [Nat.ModEq]
  omega

example {α : Type} [Fintype α] [DecidableEq α] : Even (Fintype.card α) ↔ isEven α := by
  constructor
  · rintro ⟨n, hn⟩
    -- `card α = n + n`: identify `α` with `Fin n × Bool` and flip the `Bool`.
    have hcard : Fintype.card α = Fintype.card (Fin n × Bool) := by
      simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, hn]; ring
    obtain e := Fintype.equivOfCardEq hcard
    refine ⟨fun x => e.symm ((e x).1, !(e x).2), ?_, ?_⟩
    · funext x
      simp only [Function.comp_apply, Equiv.apply_symm_apply, Bool.not_not,
        Prod.mk.eta, Equiv.symm_apply_apply, id_eq]
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _ hx
      apply congrArg e at hx
      rw [Equiv.apply_symm_apply] at hx
      have : (e x).2 = !(e x).2 := (congrArg Prod.snd hx).symm
      simp at this
  · rintro ⟨f, hf_invo, hf_card⟩
    have hinv : Function.Involutive f := fun x => congr_fun hf_invo x
    have hmod := card_modEq_card_fixed hinv
    rw [hf_card, Nat.ModEq] at hmod
    rw [Nat.even_iff]
    omega

example {α : Type} [Fintype α] [DecidableEq α] : Odd (Fintype.card α) ↔ isOdd α := by
  constructor
  · rintro ⟨n, hn⟩
    -- `card α = 2n + 1`: identify `α` with `Option (Fin n × Bool)`, flip the
    -- `Bool` on the paired elements and fix the extra `none`.
    have hcard : Fintype.card α = Fintype.card (Option (Fin n × Bool)) := by
      simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_bool, hn]; ring
    obtain e := Fintype.equivOfCardEq hcard
    set swp : Fin n × Bool → Fin n × Bool := fun p => (p.1, !p.2) with hswp
    have hswp2 : swp ∘ swp = id := by funext p; simp [hswp]
    refine ⟨fun x => e.symm ((e x).map swp), ?_, ?_⟩
    · funext x
      simp only [Function.comp_apply, Equiv.apply_symm_apply, Option.map_map,
        hswp2, Option.map_id, id_eq, Equiv.symm_apply_apply]
    · rw [Finset.card_eq_one]
      refine ⟨e.symm none, ?_⟩
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hx
        apply congrArg e at hx
        rw [Equiv.apply_symm_apply] at hx
        cases h : e x with
        | none =>
          apply congrArg e.symm at h
          rw [Equiv.symm_apply_apply] at h
          exact h
        | some p =>
          rw [h] at hx
          simp only [Option.map_some, hswp, Option.some.injEq] at hx
          exact absurd (congrArg Prod.snd hx) (by simp)
      · intro hx
        subst hx
        simp [Equiv.apply_symm_apply]
  · rintro ⟨f, hf_invo, hf_card⟩
    have hinv : Function.Involutive f := fun x => congr_fun hf_invo x
    have hmod := card_modEq_card_fixed hinv
    rw [hf_card, Nat.ModEq] at hmod
    rw [Nat.odd_iff]
    omega


/-!
Exercise III.4 (p. 140)
-/
namespace ExIII_4

def α : ℤ ⟶ ℤ := fun x ↦ -x

example : Decidable (IsIdempotent α) := by
  apply isFalse
  rintro ⟨h⟩
  have h1 := congr_fun h 1
  simp [α] at h1

example : Decidable (IsInvolution α) := by
  apply isTrue
  refine ⟨?_⟩
  ext x
  simp [α]

example {x : ℤ} : Function.IsFixedPt α x ↔ x = 0 := by
  constructor
  · rintro h
    simp only [Function.IsFixedPt, α] at h
    exact self_eq_neg.mp (id (Eq.symm h))
  · rintro rfl
    simp [Function.IsFixedPt, α]

end ExIII_4

/-!
Exercise III.5 (p. 140)
-/
namespace ExIII_5

def α : ℤ ⟶ ℤ := fun x ↦ |x|

example : Decidable (IsIdempotent α) := by
  apply isTrue
  refine ⟨?_⟩
  ext x
  simp [α]

example : Decidable (IsInvolution α) := by
  apply isFalse
  rintro ⟨h⟩
  have h1 := congr_fun h (-1)
  simp [α] at h1

example {x : ℤ} : Function.IsFixedPt α x ↔ 0 ≤ x := by
  constructor
  · rintro h
    simp only [Function.IsFixedPt, α] at h
    rw [abs_eq_self] at h
    exact h
  · rintro h
    simp [Function.IsFixedPt, α, abs_of_nonneg h]

end ExIII_5

/-!
Exercise III.6 (p. 140)
-/
namespace ExIII_6

def α : ℤ ⟶ ℤ := fun x ↦ x + 3

example : Decidable (IsIso α) := by
  apply isTrue
  refine ⟨fun x ↦ x - 3, ?_, ?_⟩
  · ext x
    simp [α]
  · ext x
    simp [α]

end ExIII_6

/-!
Exercise III.7 (p. 140)
-/
namespace ExIII_7

def α : ℤ ⟶ ℤ := fun x ↦ 5 * x

example : Decidable (IsIso α) := by
  apply isFalse
  rintro ⟨h, h_left_inv, h_right_inv⟩
  have h1 := congr_fun h_left_inv 1
  have h2 := congr_fun h_right_inv 1
  simp [α] at h1 h2
  omega

end ExIII_7

/-!
Exercise III.8 (p. 140)
-/
example {α : IdemEndomap}
    : α.toEnd ⊚ α.toEnd ⊚ α.toEnd = α.toEnd := by
  have h_idem := α.idem
  rw [h_idem]
  exact h_idem

example {𝒞 : Type u} [Category.{v, u} 𝒞] {A : 𝒞}
    (α : A ⟶ A) [IsIdempotent α] : α ⊚ α ⊚ α = α := by
  have h_idem : IsIdempotent α := inferInstance
  obtain ⟨h_idem⟩ := h_idem
  rw [h_idem]
  exact h_idem

example {α : InvolEndomap}
    : α.toEnd ⊚ α.toEnd ⊚ α.toEnd = α.toEnd := by
  have h_invol := α.invol
  rw [h_invol]
  exact Category.id_comp _

example {𝒞 : Type u} [Category.{v, u} 𝒞] {A : 𝒞}
    (α : A ⟶ A) [IsInvolution α] : α ⊚ α ⊚ α = α := by
  have h_invol : IsInvolution α := inferInstance
  obtain ⟨h_invol⟩ := h_invol
  rw [h_invol]
  exact Category.id_comp _

/-!
Exercise III.9 (p. 141)
-/
namespace ExIII_9

inductive A
  | a₁ | a₂ | a₃

def α : A ⟶ A
  | A.a₁ => A.a₂
  | A.a₂ => A.a₃
  | A.a₃ => A.a₂

example : α ⊚ α ⊚ α = α := by
  ext x
  cases x <;> simp [α]

example : ¬(IsIdempotent α) := by
  intro h
  obtain ⟨h_idem⟩ := h
  have h1 := congr_fun h_idem A.a₁
  simp [α] at h1

example : ¬(IsInvolution α) := by
  intro h
  obtain ⟨h_invol⟩ := h
  have h1 := congr_fun h_invol A.a₁
  simp [α] at h1

end ExIII_9

/-!
Exercise III.10 (p. 141)
-/
namespace ExIII_10

inductive X
  | a | b | c | d | e

inductive P
  | k | m | n | p | q | r

def s : X ⟶ P
  | X.a => P.k
  | X.b => P.m
  | X.c => P.k
  | X.d => P.p
  | X.e => P.m

def t : X ⟶ P
  | X.a => P.m
  | X.b => P.m
  | X.c => P.m
  | X.d => P.q
  | X.e => P.r

example : Decidable (∃ x : X, s x = t x) := by
  apply isTrue
  use X.b
  simp [s, t]

example : Decidable (∃ x : X, t x = P.k) := by
  apply isFalse
  rintro ⟨x, h⟩
  cases x <;> simp [t] at h

end ExIII_10

/-!
The category 𝑺⇊ of (irreflexive directed multi-) graphs (pp. 141–142)
-/
structure IrreflexiveGraph where
  A : Type
  D : Type
  toSrc : A ⟶ D
  toTgt : A ⟶ D

instance instCategoryIrreflexiveGraph : Category IrreflexiveGraph where
  Hom X Y := {
    f : (X.A ⟶ Y.A) × (X.D ⟶ Y.D) //
        f.2 ⊚ X.toSrc = Y.toSrc ⊚ f.1 -- source commutes
        ∧ f.2 ⊚ X.toTgt = Y.toTgt ⊚ f.1 -- target commutes
  }
  id X := ⟨(𝟙 X.A, 𝟙 X.D), ⟨rfl, rfl⟩⟩
  -- exerercise III.11 (p. 142)
  comp := by
    rintro _ _ _ ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨
      (g.1 ⊚ f.1, g.2 ⊚ f.2),
      by
        obtain ⟨hfSrc_comm, hfTgt_comm⟩ := hf
        obtain ⟨hgSrc_comm, hgTgt_comm⟩ := hg
        constructor
        · rw [← Category.assoc, hfSrc_comm, Category.assoc, hgSrc_comm,
              ← Category.assoc]
        · rw [← Category.assoc, hfTgt_comm, Category.assoc, hgTgt_comm,
              ← Category.assoc]
    ⟩

@[ext]
lemma IrreflexiveGraph.hom_ext {X Y : IrreflexiveGraph}
    (f g : X ⟶ Y) (hA : f.val.1 = g.val.1) (hD : f.val.2 = g.val.2)
    : f = g :=
  Subtype.ext (Prod.ext hA hD)

/-!
Exercise III.11 (p. 142)
-/
namespace ExIII_11

example (X Y Z : IrreflexiveGraph) (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ Z := by
  exact instCategoryIrreflexiveGraph.comp f g

end ExIII_11

/-!
Exercise III.12 (p. 143)
-/
def funSetWithEndoToIrrG
    : Functor SetWithEndomap IrreflexiveGraph := {
  obj (X : SetWithEndomap) := {
    A := X.carrier
    D := X.carrier
    toSrc := 𝟙 X.carrier
    toTgt := X.toEnd
  }
  map {X Y : SetWithEndomap} (f : X ⟶ Y) := {
    val := (f, f)
    property := by
      obtain ⟨carrierX, toEndX⟩ := X
      obtain ⟨carrierY, toEndY⟩ := Y
      obtain ⟨f, hf_comm⟩ := f
      dsimp at f hf_comm
      constructor <;> (dsimp; trivial)
  }
}

-- Helper function to align to the notation in the book
abbrev I {X Y : SetWithEndomap} (f : X ⟶ Y) := funSetWithEndoToIrrG.map f

-- exercise III.12 (p. 143)
example {X Y Z : SetWithEndomap}
    (f : X ⟶ Y) (g : Y ⟶ Z) : I (g ⊚ f) = I g ⊚ I f := rfl

/-!
Exercise III.13 (p. 144)
-/
namespace ExIII_13

example (X' Y' : SetWithEndomap) (f : funSetWithEndoToIrrG.obj X' ⟶ funSetWithEndoToIrrG.obj Y') :
  f.val.1 = f.val.2 := by
  obtain ⟨f, hf1, hf2⟩ := f
  simp only [funSetWithEndoToIrrG, Category.id_comp, Category.comp_id] at hf1 hf2 ⊢
  exact hf1.symm

end ExIII_13

/-!
The category 𝑺↓ of simple directed graphs (pp. 144–145)
-/
structure SimpleGraph where
  A : Type
  D : Type
  toFun : A ⟶ D

instance : Category SimpleGraph where
  Hom X Y := {
    f : (X.A ⟶ Y.A) × (X.D ⟶ Y.D) //
        f.2 ⊚ X.toFun = Y.toFun ⊚ f.1 -- commutes
  }
  id X := ⟨(𝟙 X.A, 𝟙 X.D), rfl⟩
  comp := by
    rintro _ _ _ ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨
      (g.1 ⊚ f.1, g.2 ⊚ f.2),
      by
        have hfSrc_comm := hf
        have hgSrc_comm := hg
        rw [← Category.assoc, hfSrc_comm, Category.assoc, hgSrc_comm,
            ← Category.assoc]
    ⟩

@[ext]
lemma SimpleGraph.hom_ext {X Y : SimpleGraph}
    (f g : X ⟶ Y) (hA : f.val.1 = g.val.1) (hD : f.val.2 = g.val.2)
    : f = g :=
  Subtype.ext (Prod.ext hA hD)

def funSetWithEndoToSimpG : Functor SetWithEndomap SimpleGraph := {
  obj (X : SetWithEndomap) := {
    A := X.carrier
    D := X.carrier
    toFun := X.toEnd
  }
  map {X Y : SetWithEndomap} (f : X ⟶ Y) := {
    val := (f, f)
    property := by
      obtain ⟨f, hf_comm⟩ := f
      trivial
  }
}

-- Helper function to align to the notation in the book
abbrev J {X Y : SetWithEndomap} (f : X ⟶ Y) :=
  funSetWithEndoToSimpG.map f

example {X Y Z : SetWithEndomap}
    (f : X ⟶ Y) (g : Y ⟶ Z) : J (g ⊚ f) = J g ⊚ J f := rfl

/-!
Exercise III.14 (p. 144)
-/
namespace ExIII_14

-- Contrast with III.13: for the simple-graph functor there is no source
-- map to force the two components to agree.  Take the identity endomap on
-- `Bool` for `X` and the swap (`not`) endomap for `Y`.  Every graph morphism
-- `J X ⟶ J Y` must satisfy `f.2 = not ∘ f.1`, so `f.1 = f.2` is impossible.
example : ∃ X Y : SetWithEndomap,
    ∀ f : funSetWithEndoToSimpG.obj X ⟶ funSetWithEndoToSimpG.obj Y,
    f.val.2 ⊚ X.toEnd = Y.toEnd ⊚ f.val.1 ∧ f.val.1 ≠ f.val.2 := by
  refine ⟨⟨Bool, 𝟙 Bool⟩, ⟨Bool, fun b => !b⟩, ?_⟩
  rintro ⟨⟨f1, f2⟩, hf⟩
  refine ⟨hf, ?_⟩
  intro h
  have hh : f1 true = f2 true := congr_fun h true
  have hb := congr_fun hf true
  simp only [funSetWithEndoToSimpG, CategoryStruct.comp, Function.comp_apply,
    types_id_apply] at hb
  rw [← hh] at hb
  simp at hb

end ExIII_14

/-!
The category of reflexive graphs (p. 145)
-/
structure ReflexiveGraph extends IrreflexiveGraph where
  toInc : D ⟶ A
  section_src : toSrc ⊚ toInc = 𝟙 D
  section_tgt : toTgt ⊚ toInc = 𝟙 D

instance : Category ReflexiveGraph where
  Hom X Y := {
    f : (X.A ⟶ Y.A) × (X.D ⟶ Y.D) //
        f.2 ⊚ X.toSrc = Y.toSrc ⊚ f.1 -- source commutes
        ∧ f.2 ⊚ X.toTgt = Y.toTgt ⊚ f.1 -- target commutes
        ∧ f.1 ⊚ X.toInc = Y.toInc ⊚ f.2
  }
  id X := ⟨
    (𝟙 X.A, 𝟙 X.D),
    by
      split_ands <;> first | exact fun _ hx ↦ hx | rfl
  ⟩
  comp := by
    rintro _ _ _ ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨
      (g.1 ⊚ f.1, g.2 ⊚ f.2),
      by
        obtain ⟨hfSrc_comm, hfTgt_comm, hfCommonSection_comm⟩ := hf
        obtain ⟨hgSrc_comm, hgTgt_comm, hgCommonSection_comm⟩ := hg
        split_ands
        · rw [← Category.assoc, hfSrc_comm, Category.assoc, hgSrc_comm,
              ← Category.assoc]
        · rw [← Category.assoc, hfTgt_comm, Category.assoc, hgTgt_comm,
              ← Category.assoc]
        · rw [← Category.assoc, hfCommonSection_comm, Category.assoc,
              hgCommonSection_comm, ← Category.assoc]
    ⟩

@[ext]
lemma ReflexiveGraph.hom_ext {X Y : ReflexiveGraph}
    (f g : X ⟶ Y) (hA : f.val.1 = g.val.1) (hD : f.val.2 = g.val.2)
    : f = g :=
  Subtype.ext (Prod.ext hA hD)

/-!
Exercise III.15 (p. 145)
-/
namespace ExIII_15

def e (X : ReflexiveGraph) : Set (X.A ⟶ X.A) :=
  {X.toInc ⊚ X.toSrc, X.toInc ⊚ X.toTgt}
example (X : ReflexiveGraph) : ∀ x y : e X, x.val ⊚ y.val = y.val := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  simp only
  simp only [e, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  cases hx with
  | inl h1 =>
    cases hy with
    | inl h2 =>
      subst x y
      rw [← Category.assoc, Category.assoc X.toSrc _, X.section_src, Category.comp_id]
    | inr h2 =>
      subst x y
      rw [← Category.assoc, Category.assoc X.toTgt _, X.section_src, Category.comp_id]
  | inr h1 =>
    cases hy with
    | inl h2 =>
      subst x y
      rw [← Category.assoc, Category.assoc X.toSrc _, X.section_tgt, Category.comp_id]
    | inr h2 =>
      subst x y
      rw [← Category.assoc, Category.assoc X.toTgt _, X.section_tgt, Category.comp_id]

end ExIII_15

/-!
Exercise III.16 (p. 145)
-/
namespace ExIII_16

variable (X Y : ReflexiveGraph) (f : X ⟶ Y)

-- Align to the notation in the book
set_option quotPrecheck false
local notation "fA" => f.val.1
local notation "fD" => f.val.2
set_option quotPrecheck true

local notation "s" => X.toSrc
local notation "s'" => Y.toSrc
local notation "t" => X.toTgt
local notation "t'" => Y.toTgt
local notation "i" => X.toInc
local notation "i'" => Y.toInc

example : fD = s' ⊚ fA ⊚ i := by
  have h1 := f.property.1
  rw [Category.assoc, ← h1, ← Category.assoc, X.section_src, Category.id_comp]

-- alternative solution
example : fD = t' ⊚ fA ⊚ i := by
  have h1 := f.property.2.2
  rw [h1, Category.assoc, Y.section_tgt, Category.comp_id]

end ExIII_16

/-!
Exercise III.17 (p. 145)
-/
namespace ExIII_17

structure ParentLike where
  M : Type
  F : Type
  φ : M ⟶ M
  φ' : F ⟶ M
  μ : F ⟶ F
  μ' : M ⟶ F

def ParentLikeHom (X Y : ParentLike) : Type :=
  { f : (X.M ⟶ Y.M) × (X.F ⟶ Y.F) //
      f.1 ⊚ X.φ = Y.φ ⊚ f.1 -- φ commutes
      ∧ f.1 ⊚ X.φ' = Y.φ' ⊚ f.2 -- φ' commutes
      ∧ f.2 ⊚ X.μ = Y.μ ⊚ f.2 -- μ commutes
      ∧ f.2 ⊚ X.μ' = Y.μ' ⊚ f.1
  }

instance : Category ParentLike where
  Hom := ParentLikeHom -- our map between ParentLike structures
  id X :=
    ⟨(𝟙 X.M, 𝟙 X.F), by
      constructor <;> simp [Category.id_comp, Category.comp_id]⟩
  comp := by
    rintro _ _ _ ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨
      (g.1 ⊚ f.1, g.2 ⊚ f.2),
      by
        obtain ⟨hfφ_comm, hfφ'_comm, hfμ_comm, hfμ'_comm⟩ := hf
        obtain ⟨hgφ_comm, hgφ'_comm, hgμ_comm, hgμ'_comm⟩ := hg
        constructor
        · grind
        · grind
    ⟩

end ExIII_17

/-!
Exercise III.18 (p. 146)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] {X Y T : 𝒞}
    {a : X ⟶ Y} {p : Y ⟶ X} {x₁ x₂ : T ⟶ X}
    (h₁ : p ⊚ a = 𝟙 X) (h₂ : a ⊚ x₁ = a ⊚ x₂)
    : x₁ = x₂ := by
  have h₃ := congr_arg (p ⊚ ·) h₂
  simp only [Category.assoc, h₁, Category.comp_id] at h₃
  exact h₃

namespace ExIII_19_24

inductive X
  | x | Ø -- 0 is reserved but we can use Ø for the second element.
  deriving Fintype, DecidableEq

inductive Y
  | ybar | y | Ø
  deriving Fintype

def α : X ⟶ X
  | X.x => X.Ø
  | X.Ø => X.Ø

def β : Y ⟶ Y
  | Y.ybar => Y.y
  | Y.y => Y.Ø
  | Y.Ø => Y.Ø

def a : X ⟶ Y
  | X.x => Y.y
  | X.Ø => Y.Ø

/-!
Exercise III.19 (p. 147)
-/
theorem ab_comm : a ⊚ α = β ⊚ a := by
  ext y
  cases y <;> rfl

def Xα : SetWithEndomap := ⟨X, α⟩
def Yβ : SetWithEndomap := ⟨Y, β⟩
def a' : Xα ⟶ Yβ := ⟨a, ab_comm⟩

/-!
Exercise III.20 (p. 147)
-/
example : ∀ {T : Type} (x₁ x₂ : T ⟶ X),
    a ⊚ x₁ = a ⊚ x₂ → x₁ = x₂ := by
  intros T x₁ x₂ h
  ext x
  have := congr_fun h x
  simp only [types_comp_apply] at this
  cases h : x₁ x with
  | x => cases h' : x₂ x with
    | x => rfl
    | Ø =>
      rw [h, h'] at this
      simp [a] at this
  | Ø => cases h' : x₂ x with
    | x =>
      rw [h, h'] at this
      simp [a] at this
    | Ø => rfl

/-!
Exercise III.21 (p. 147)
-/
-- y and 0 have to go back to x and 0
-- and ybar has choice.
def p₁ : Y ⟶ X
  | Y.ybar => X.x
  | Y.y => X.x
  | Y.Ø => X.Ø

example : p₁ ⊚ a = 𝟙 X := by
  funext y
  cases y <;> rfl

#eval Danilo's_formula a p₁
  (by
    funext y
    fin_cases y <;> rfl)

def p₂ : Y ⟶ X
  | Y.ybar => X.Ø
  | Y.y => X.x
  | Y.Ø => X.Ø

example : p₂ ⊚ a = 𝟙 X := by
  funext y
  cases y <;> rfl

/-!
Exercise III.22 (p. 147)
-/
example : ¬(p₁ ⊚ β = α ⊚ p₁) := by
  intro h
  have h1 := congr_fun h Y.ybar
  simp only [types_comp_apply] at h1
  simp [p₁, α, β] at h1

example : ¬(p₂ ⊚ β = α ⊚ p₂) := by
  intro h
  have h1 := congr_fun h Y.ybar
  simp only [types_comp_apply] at h1
  simp [p₂, α, β] at h1

/-!
Exercise III.23 (p. 147)
-/
def b₁ : Y ⟶ X
  | Y.ybar => X.Ø
  | Y.y => X.Ø
  | Y.Ø => X.Ø

example : b₁ ⊚ β = α ⊚ b₁ := by
  funext z
  cases z <;> rfl

def b₂ : Y ⟶ X
  | Y.ybar => X.x
  | Y.y => X.Ø
  | Y.Ø => X.Ø

example : b₂ ⊚ β = α ⊚ b₂ := by
  funext z
  cases z <;> rfl

def b₃ : Y ⟶ X
  | Y.ybar => X.Ø
  | Y.y => X.x
  | Y.Ø => X.Ø

example : b₃ ⊚ β ≠ α ⊚ b₃ := by
  intro h
  have h1 := congr_fun h Y.ybar
  simp only [types_comp_apply] at h1
  simp [b₃, α, β] at h1

def b₄ : Y ⟶ X
  | Y.ybar => X.x
  | Y.y => X.x
  | Y.Ø => X.Ø


example : b₄ ⊚ β ≠ α ⊚ b₄ := by
  intro h
  have h1 := congr_fun h Y.ybar
  simp only [types_comp_apply] at h1
  simp [b₄, α, β] at h1

def b₅ : Y ⟶ X
  | Y.ybar => X.Ø
  | Y.y => X.Ø
  | Y.Ø => X.x


example : b₅ ⊚ β ≠ α ⊚ b₅ := by
  intro h
  have h1 := congr_fun h Y.y
  simp only [types_comp_apply] at h1
  simp [b₅, α, β] at h1

def b₆ : Y ⟶ X
  | Y.ybar => X.x
  | Y.y => X.Ø
  | Y.Ø => X.x


example : b₆ ⊚ β ≠ α ⊚ b₆ := by
  intro h
  have h1 := congr_fun h Y.y
  simp only [types_comp_apply] at h1
  simp [b₆, α, β] at h1

def b₇ : Y ⟶ X
  | Y.ybar => X.Ø
  | Y.y => X.x
  | Y.Ø => X.x

example : b₇ ⊚ β ≠ α ⊚ b₇ := by
  intro h
  have h1 := congr_fun h Y.ybar
  simp only [types_comp_apply] at h1
  simp [b₇, α, β] at h1

def b₈ : Y ⟶ X
  | Y.ybar => X.x
  | Y.y => X.x
  | Y.Ø => X.x

example : b₈ ⊚ β ≠ α ⊚ b₈ := by
  intro h
  have h1 := congr_fun h Y.ybar
  simp only [types_comp_apply] at h1
  simp [b₈, α, β] at h1

/-!
Exercise III.24 (p. 147)
-/
def X' : SimpleGraph := funSetWithEndoToSimpG.obj Xα
def Y' : SimpleGraph := funSetWithEndoToSimpG.obj Yβ

example : ¬(∃ p : Y' ⟶ X', p ⊚ J a' = 𝟙 X') := by
  push Not
  intro ⟨p, hp⟩ hp'
  -- A retraction would make both graph components of `p ⊚ J a'` the identity.
  have h2 : p.2 ⊚ a = 𝟙 X := congr_arg (Prod.snd ∘ Subtype.val) hp'
  have hy := congr_fun h2 X.x
  have hb := congr_fun hp Y.ybar
  simp only [funSetWithEndoToSimpG, Xα, Yβ, a, α, β, types_comp_apply, types_id_apply,
    X', Y'] at hy hb
  rw [hy] at hb
  cases hpb : p.1 Y.ybar <;> simp [hpb] at hb


end ExIII_19_24

/-!
Exercise III.25 (p. 148)
-/
namespace ExIII_25

example {X Y : IrreflexiveGraph} (f : X ⟶ Y)
    : f.val.2 ⊚ X.toSrc = f.val.2 ⊚ X.toTgt ↔ Y.toSrc ⊚ f.val.1 = Y.toTgt ⊚ f.val.1 := by
  have h1 := f.property.1
  have h2 := f.property.2
  rw [h1, h2]

end ExIII_25

/-!
Exercise III.26 (p. 148)
-/
namespace ExIII_26

def f : ℤ ⟶ ℚ := fun x ↦ (x : ℚ)

def Z : SetWithEndomap := {
  carrier := ℤ
  toEnd := fun x ↦ 5 * x
}

def Q : SetWithEndomap := {
  carrier := ℚ
  toEnd := fun x ↦ 5 * x
}

def f' : Z ⟶ Q := ⟨f, by
  funext x
  simp [Z, Q, f]
⟩

example : ∃ f : ℚ → ℚ, Q.toEnd ∘ f = id ∧ f ∘ Q.toEnd = id := by
  use fun x ↦ (x / 5 : ℚ)
  constructor <;> funext x <;> simp [Q]; field_simp

example : ∀ {T : Type} (x₁ x₂ : T ⟶ ℤ),
    f ⊚ x₁ = f ⊚ x₂ → x₁ = x₂ := by
  intros T x₁ x₂ h
  ext t
  have := congr_fun h t
  simp only [types_comp_apply, f] at this
  exact Rat.intCast_inj.mp this

end ExIII_26

/-!
Exercise III.27 (p. 148)
-/
namespace ExIII_27

inductive X
  | x₀ | x₁

def α : X ⟶ X
    | X.x₀ => X.x₀
    | X.x₁ => X.x₀

def Xα : SetWithIdemEndomap := {
  carrier := X
  toEnd := α
  idem := by
    funext x
    cases x <;> rfl
}

example (Yβ : SetWithInvEndomap)
    (f : Xα.toSetWithEndomap ⟶ Yβ.toSetWithEndomap)
    : f.val X.x₀ = f.val X.x₁ := by
  -- get Yβ inverse
  -- then β f = f α, so f = β^-1 f α
  -- since α x₀ = α x₁, we have f x₀ = f x₁.
  have := f.property
  obtain ⟨g, hg, hg'⟩ := Yβ.inv
  have h1 := congr_arg (g ⊚ ·) this
  simp only [Category.assoc] at h1
  rw [hg, Category.comp_id] at h1
  rw [← h1]
  simp
  congr

end ExIII_27

/-- A left-cancellable (monic) map of endomaps is injective on the underlying
sets.  Given `a a'` with `f a = f a'`, view them as the two morphisms out of the
free endomap `(ℕ, succ)` sending `n ↦ αⁿ a` (resp. `αⁿ a'`); these agree after
composing with `f`, so cancelling `f` and evaluating at `0` gives `a = a'`. -/
theorem SetWithEndomap.injective_of_mono {X Y : SetWithEndomap} (f : X ⟶ Y)
    (hmono : ∀ {T : SetWithEndomap} (y₁ y₂ : T ⟶ X), f ⊚ y₁ = f ⊚ y₂ → y₁ = y₂)
    : Function.Injective f.val := by
  intro a a' haa
  have hcomm : ∀ z, f.val (X.toEnd z) = Y.toEnd (f.val z) := (congr_fun f.property ·)
  let orbit : X.carrier → ((⟨ℕ, Nat.succ⟩ : SetWithEndomap) ⟶ X) := fun b =>
    ⟨(X.toEnd^[·] b), funext (Function.iterate_succ_apply' X.toEnd · b)⟩
  have key : ∀ n, f.val (X.toEnd^[n] a) = f.val (X.toEnd^[n] a') := by
    intro n; induction n with
    | zero => exact haa
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        hcomm, hcomm, ih]
  simpa [orbit] using congr_fun (congr_arg Subtype.val
    (hmono (orbit a) (orbit a') (Subtype.ext (funext key)))) 0

/-!
Exercise III.28 (p. 148)
-/
example (Xα : SetWithEndomap) (Yβ : SetWithInvEndomap)
    (f : Xα ⟶ Yβ.toSetWithEndomap)
    (hf_inj : ∀ {T : SetWithEndomap} (y₁ y₂ : T ⟶ Xα),
        f ⊚ y₁ = f ⊚ y₂ → y₁ = y₂)
    : ∀ {T : Type} (x₁ x₂ : T → Xα.carrier),
        Xα.toEnd ⊚ x₁ = Xα.toEnd ⊚ x₂ → x₁ = x₂ := by
  -- `f` commutes with the endomaps (`f (α z) = β (f z)`), and `β` is injective.
  have hcomm : ∀ z, f.val (Xα.toEnd z) = Yβ.toEnd (f.val z) := (congr_fun f.property ·)
  obtain ⟨g, hg, -⟩ := Yβ.inv
  have hgL : Function.LeftInverse g Yβ.toEnd := (congr_fun hg ·)
  have hβ_inj : Function.Injective Yβ.toEnd := hgL.injective
  -- `f` monic ⟹ `f` injective (the reusable lemma above).
  have hf_val_inj : Function.Injective f.val := SetWithEndomap.injective_of_mono f hf_inj
  -- `α a = α a'` ⟹ `β (f a) = β (f a')` ⟹ `f a = f a'` ⟹ `a = a'`, i.e. `α` is injective.
  have hα_inj : Function.Injective Xα.toEnd :=
    fun a a' h => hf_val_inj (hβ_inj (by rw [← hcomm, ← hcomm, h]))
  intro _ x₁ x₂ h
  exact funext fun t => hα_inj (congr_fun h t)

/-!
🤖 `SetWithEndomap`, `IrreflexiveGraph`, and `ReflexiveGraph` are not three
unrelated categories: each is the category of `Type`-valued **diagrams** on a
fixed small "shape" (a presentation of a category by sorts, generating
operations, and equations).  Below we build that one construction and recover
all three by instantiating the shape.
-/

/-- A shape: sorts, generating operations (homs between sorts), and equations.
    Each equation names a composable pair of ops — a `sect` and a `retr` —
    required to compose to the identity, `retr ∘ sect = id`.  (These three
    categories only ever need such section equations.) -/
structure Shape where
  sorts : Type
  hom   : sorts → sorts → Type
  eqs   : Type
  dom   : eqs → sorts
  cod   : eqs → sorts
  sect  : (e : eqs) → hom (dom e) (cod e)
  retr  : (e : eqs) → hom (cod e) (dom e)

/-- A diagram of shape `S` in `Type`: a carrier per sort, a function per
    operation, with every equation's pair composing to the identity. -/
structure Diagram (S : Shape) where
  obj : S.sorts → Type
  map : ∀ a b, S.hom a b → obj a → obj b
  resp : ∀ e, map (S.cod e) (S.dom e) (S.retr e) ∘ map (S.dom e) (S.cod e) (S.sect e) = id

/-- A morphism of diagrams: a component per sort, commuting with every op. -/
@[ext]
structure DiagramHom {S : Shape} (X Y : Diagram S) where
  comp : (a : S.sorts) → X.obj a → Y.obj a
  natural : ∀ a b (e : S.hom a b), comp b ∘ X.map a b e = Y.map a b e ∘ comp a

/-- Diagrams of a fixed shape form a category — uniformly, for every shape. -/
instance (S : Shape) : Category (Diagram S) where
  Hom X Y := DiagramHom X Y
  id X := ⟨fun _ => id, fun _ _ _ => rfl⟩
  comp f g := ⟨fun a => g.comp a ∘ f.comp a, by
    intro a b e
    funext x
    have hf := congrFun (f.natural a b e) x
    have hg := congrFun (g.natural a b e) (f.comp a x)
    simp only [Function.comp_apply] at *
    rw [hf, hg]⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Shape of `SetWithEndomap`: one sort `•`, one op `e : • → •`, no equations. -/
def EndoShape : Shape where
  sorts := Unit
  hom _ _ := Unit
  eqs := Empty
  dom := nofun
  cod := nofun
  sect := nofun
  retr := nofun

/-- The two sorts of a graph: arrows `A` and dots `D`. -/
inductive GraphSort | A | D

/-- The two parallel operations of a graph: `toSrc, toTgt : A → D`. -/
inductive GraphArrow | toSrc | toTgt

/-- Shape of `IrreflexiveGraph`: sorts `A`, `D`; two ops `toSrc, toTgt : A → D`;
    no equations. -/
def IrrShape : Shape where
  sorts := GraphSort
  hom := fun a b => match a, b with
    | .A, .D => GraphArrow
    | _, _ => Empty
  eqs := Empty
  dom := nofun
  cod := nofun
  sect := nofun
  retr := nofun

/-- Shape of `ReflexiveGraph`: adds `inc : D → A` with `toSrc∘inc = toTgt∘inc = id_D`.
    Two equations (indexed by `Bool`), each pairing `inc` as `sect` with one of
    `toSrc`/`toTgt` as `retr`. -/
def ReflShape : Shape where
  sorts := GraphSort
  hom := fun a b => match a, b with
    | .A, .D => GraphArrow   -- toSrc, toTgt : A → D
    | .D, .A => Unit         -- inc : D → A
    | _, _ => Empty
  eqs := Bool
  dom := fun _ => .D
  cod := fun _ => .A
  sect := fun _ => ()                                          -- inc : D → A
  retr := fun e => match e with | true => .toSrc | false => .toTgt

-- Each structure is exactly a diagram of its shape, and back.
def SetWithEndomap.toDiagram (S : SetWithEndomap) : Diagram EndoShape where
  obj _ := S.carrier
  map _ _ _ := S.toEnd
  resp := nofun

def Diagram.toSetWithEndomap (X : Diagram EndoShape) : SetWithEndomap where
  carrier := X.obj ()
  toEnd := X.map () () ()

def IrreflexiveGraph.toDiagram (G : IrreflexiveGraph) : Diagram IrrShape where
  obj := fun s => match s with | .A => G.A | .D => G.D
  map := fun a b => match a, b with
    | .A, .D => fun e => match e with | .toSrc => G.toSrc | .toTgt => G.toTgt
    | .A, .A => fun e => e.elim
    | .D, .A => fun e => e.elim
    | .D, .D => fun e => e.elim
  resp := nofun

def Diagram.toIrreflexiveGraph (X : Diagram IrrShape) : IrreflexiveGraph where
  A := X.obj .A
  D := X.obj .D
  toSrc := X.map .A .D .toSrc
  toTgt := X.map .A .D .toTgt

def ReflexiveGraph.toDiagram (G : ReflexiveGraph) : Diagram ReflShape where
  obj := fun s => match s with | .A => G.A | .D => G.D
  map := fun a b => match a, b with
    | .A, .D => fun e => match e with | .toSrc => G.toSrc | .toTgt => G.toTgt
    | .D, .A => fun _ => G.toInc
    | .A, .A => fun e => e.elim
    | .D, .D => fun e => e.elim
  resp := fun e => match e with | true => G.section_src | false => G.section_tgt

def Diagram.toReflexiveGraph (X : Diagram ReflShape) : ReflexiveGraph where
  A := X.obj .A
  D := X.obj .D
  toSrc := X.map .A .D .toSrc
  toTgt := X.map .A .D .toTgt
  toInc := X.map .D .A ()
  section_src := X.resp true
  section_tgt := X.resp false

/-!
Exercise III.30 (p. 151)

An abstract structure type often arises from a particular example: take a small
family `𝒜` of objects and maps of a category `𝒳` (closed under domain and
codomain).  Read each object `A` as the name of "`A`-shaped figures", and each
map `a : B ⟶ A` as the name of a structural map `a*` going the other way.  Then
every object `X` of `𝒳` becomes an `𝒜`-structure: its `A`-component is the set
of figures `A ⟶ X`, and each structural map acts by precomposition, `a*(x) = x ∘ a`.
-/

/-- A realization of a shape `S` inside a category `𝒳` — the "small family
    `𝒜`": each sort names an object `pt a`, and each op `a → b` names a
    structural map going the other way, `pt b ⟶ pt a`.  `𝒳` may be large
    (e.g. `Type`), so we only require its hom-sets to be small. -/
structure Realization (S : Shape) (𝒳 : Type u) [Category.{0} 𝒳] where
  pt : S.sorts → 𝒳
  act : ∀ a b, S.hom a b → (pt b ⟶ pt a)
  -- each equation's pair composes (the other way round) to the identity in `𝒳`
  resp : ∀ e, act (S.dom e) (S.cod e) (S.sect e) ⊚ act (S.cod e) (S.dom e) (S.retr e)
             = 𝟙 (pt (S.dom e))

/-- Every object `X` of `𝒳` gives the `S`-diagram of its figures: the
    `a`-component is `pt a ⟶ X`, and each structural map acts by `a*(x) = x ∘ a`.
    The section equations hold because precomposition is functorial. -/
def Realization.figures {S : Shape} {𝒳 : Type u} [Category.{0} 𝒳]
    (R : Realization S 𝒳) (X : 𝒳) : Diagram S where
  obj a := R.pt a ⟶ X
  map a b e := fun x => x ⊚ R.act a b e
  resp := by
    intro e
    funext x
    change (x ⊚ R.act (S.dom e) (S.cod e) (S.sect e)) ⊚ R.act (S.cod e) (S.dom e) (S.retr e) = x
    rw [← Category.assoc, R.resp e, Category.id_comp]

/-- The figures construction is a functor `𝒳 ⥤ Diagram S`: a map `f : X ⟶ Y`
    acts on figures by postcomposition. -/
def Realization.figuresFunctor {S : Shape} {𝒳 : Type u} [Category.{0} 𝒳]
    (R : Realization S 𝒳) : Functor 𝒳 (Diagram S) where
  obj X := R.figures X
  map f :=
    { comp := fun _ x => f ⊚ x
      -- exercise 29
      natural := by
        intro a b e; funext x
        simp only [Realization.figures, Function.comp_apply, Category.assoc] }
  map_id := by
    intro X; apply DiagramHom.ext; funext a x
    change 𝟙 X ⊚ x = x
    rw [Category.comp_id]
  map_comp := by
    intro X Y Z f g; apply DiagramHom.ext; funext a x
    change (g ⊚ f) ⊚ x = g ⊚ (f ⊚ x)
    rw [Category.assoc]

/-!
Concretely, realize the graph shape `IrrShape` in the category `Type` of sets:
a dot `D` is a point `Unit`, an arrow `A` is the two-element set `Bool`, and
`toSrc`/`toTgt` are its two endpoints `Unit → Bool`.  The figures construction
then turns every set `X` into an irreflexive graph — recovering the whole
`IrreflexiveGraph` category (`≃ Diagram IrrShape`) as figures of sets.
-/
def irrRealization : Realization IrrShape Type where
  pt := fun s => match s with | .A => Bool | .D => Unit
  act := fun a b => match a, b with
    | .A, .D => fun e => match e with
        | .toSrc => (fun _ => false)
        | .toTgt => (fun _ => true)
    | .A, .A => fun e => e.elim
    | .D, .A => fun e => e.elim
    | .D, .D => fun e => e.elim
  resp := nofun

/-- The induced functor `Type ⥤ Diagram IrrShape`: every set `X` becomes the
    graph with vertices `X` and edges `Bool → X` (all ordered pairs). -/
def irrGraphFunctor : Functor Type (Diagram IrrShape) :=
  irrRealization.figuresFunctor

/-- …and, read back through `toIrreflexiveGraph`, an actual `IrreflexiveGraph`. -/
def irrGraph (X : Type) : IrreflexiveGraph :=
  (irrRealization.figures X).toIrreflexiveGraph

/-!
The reflexive-graph shape `ReflShape` needs the extra `inc` operation and its two
section equations.  Realize it in `Set` the same way — dot `D = 1 = Unit`, arrow
`A = S` for any set `S` carrying two points `s t : S` (the two maps `1 → S`) — and
supply `inc` by the *unique* map `S → 1`.  The section laws `toSrc∘inc = toTgt∘inc
= id` then hold automatically, because `1` is terminal: the round-trip `1 → S → 1`
is forced to be `𝟙 1`.  So `Diagram ReflShape` really is the reflexive-graph
category, with reflexivity coming from that unique map to `1`.

Effectively exercise 30
-/
def reflRealization (S : Type) (s t : S) : Realization ReflShape Type where
  pt := fun x => match x with | .A => S | .D => Unit
  act := fun a b => match a, b with
    | .A, .D => fun e => match e with | .toSrc => (fun _ => s) | .toTgt => (fun _ => t)
    | .D, .A => fun _ => (fun _ => ())      -- the unique map `S → 1`
    | .A, .A => fun e => e.elim
    | .D, .D => fun e => e.elim
  resp := fun _ => rfl      -- `S → 1 → S` composed the other way is `𝟙 1`, since `1` is terminal

/-- The induced functor `Type ⥤ Diagram ReflShape`. -/
def reflGraphFunctor (S : Type) (s t : S) : Functor Type (Diagram ReflShape) :=
  (reflRealization S s t).figuresFunctor

/-- …read back through `toReflexiveGraph`, an actual `ReflexiveGraph`: every set
    `X` becomes a reflexive graph, its reflexive loops supplied by `inc = (· → 1)`. -/
def reflGraph (S : Type) (s t : S) (X : Type) : ReflexiveGraph :=
  ((reflRealization S s t).figures X).toReflexiveGraph

end CM

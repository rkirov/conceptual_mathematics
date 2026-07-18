import ConceptualMathematics.Sorried.Article1
import ConceptualMathematics.Sorried.Article3
import ConceptualMathematics.Sorried.Session15
import Mathlib.Data.Fintype.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.CategoryTheory.Category.Bipointed
import Mathlib.CategoryTheory.Comma.Over.Basic
open CategoryTheory
open Limits
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Proposition (uniqueness of terminal objects) (pp. 213–214)
-/
theorem uniqueness_of_terminal_objects
    {𝒞 : Type u} [Category.{v, u} 𝒞] {S₁ S₂ : 𝒞}
    (hS₁ : IsTerminal S₁) (hS₂ : IsTerminal S₂)
    : ∃! s : S₁ ⟶ S₂, IsIso s := by
  let f : S₁ ⟶ S₂ := hS₂.from S₁
  let g : S₂ ⟶ S₁ := hS₁.from S₂
  have h_id₁ : g ⊚ f = 𝟙 S₁ := hS₁.hom_ext _ _
  have h_id₂ : f ⊚ g = 𝟙 S₂ := hS₂.hom_ext _ _
  use f
  constructor
  · exact { out := ⟨g, h_id₁, h_id₂⟩ }
  · intros
    exact hS₂.hom_ext _ _


/-!
Exercise IV.1 (p. 214)
-/

example {𝒞 : Type u} [Category.{v, u} 𝒞] (One : 𝒞) (hOne : IsTerminal One) :
  ∃! (_ : One ⟶ One), True := by
  have f := hOne.from One
  use f
  constructor
  · trivial
  · intro g
    simp only [forall_const]
    exact hOne.hom_ext _ _

-- doesn't need any property of One.
example {𝒞 : Type u} [Category.{v, u} 𝒞] {One X Y : 𝒞}
  (f : X ⟶ Y) (x : One ⟶ X) : ∃ y : One ⟶ Y, y = f ⊚ x := by
  simp only [↓existsAndEq]

/-!
Exercise IV.2 (p. 214)
-/
example (X : Type) : (∀ x : Point X, (∃! x' : X, x' = x ())) ∧
                     (∀ x' : X, (∃! x : Point X, x () = x')) := by
  constructor
  · simp only [existsUnique_eq, implies_true]
  · intro x'
    use (fun _ ↦ x')
    simp only [true_and]
    intro y hy
    funext z
    cases z
    rw [hy]

/-!
Exercise IV.3 (p. 214)
-/
def termSWE : SetWithEndomap := {
  carrier := Unit
  toEnd := id
}

example : Nonempty (IsTerminal termSWE) :=
  ⟨IsTerminal.ofUniqueHom
    (by
      rintro X
      exact ⟨fun _ => (), rfl⟩
    )
    (by
      intro X m
      rfl
    )
  ⟩

example : ∀ (X : SetWithEndomap) (x : termSWE ⟶ X),
    X.toEnd (x.val ()) = x.val () := by
  intro X f
  have := congr_fun f.prop ()
  simp only [types_comp_apply] at this
  rw [←this]
  simp only [termSWE, id_eq]

/-!
Exercise IV.4 (p. 214)
-/
def termIG : IrreflexiveGraph := {
  A := Unit
  D := Unit
  toSrc := fun _ ↦ ()
  toTgt := fun _ ↦ ()
}

example : Nonempty (IsTerminal termIG) :=
  ⟨IsTerminal.ofUniqueHom
    (by
      rintro X
      exact ⟨⟨fun _ => (), fun _ => ()⟩, by
        simp only
        constructor
        · rfl
        · rfl
      ⟩
    )
    (by
      intro X m
      rfl
    )
  ⟩

example : ∀ (X : IrreflexiveGraph) (x : termIG ⟶ X),
    X.toSrc (x.val.1 ()) = X.toTgt (x.val.1 ()) := by
  intro X x
  have h1 := congr_fun x.prop.1 ()
  have h2 := congr_fun x.prop.2 ()
  simp only [types_comp_apply] at h1 h2
  rw [←h1, ←h2]
  rfl

/-!
Exercise IV.5 (p. 214)
-/
namespace ExIV_5a

example (X Y : Type) (f g : X → Y) (h : ∀ pt : Point X, f ∘ pt = g ∘ pt)
  : f = g := by
  funext x
  specialize h (fun _ ↦ x)
  have := congr_fun h ()
  simp only [Function.comp_apply] at this
  exact this


-- construct counterexample for SetWithEndomap
-- we pick X s.t. there is no point in it, while it has two non-equal
-- maps to Y.

inductive X
  | x₁ | x₂

def α : X ⟶ X
  | X.x₁ => X.x₂
  | X.x₂ => X.x₁

def Xα : SetWithEndomap := {
  carrier := X
  toEnd := α
}

inductive Y
  | y₁ | y₂

def β : Y ⟶ Y
  | Y.y₁ => Y.y₁
  | Y.y₂ => Y.y₂

def Yβ : SetWithEndomap := {
  carrier := Y
  toEnd := β
}

def E : SetWithEndomap := {
  carrier := Empty
  toEnd := Empty.elim
}

def f : Xα ⟶ Yβ := ⟨
  fun
  | X.x₁ => Y.y₁
  | X.x₂ => Y.y₁, by
    ext x
    simp [Xα, Yβ, α, β]
    cases x <;> rfl
  ⟩

def g : Xα ⟶ Yβ := ⟨
  fun
  | X.x₁ => Y.y₂
  | X.x₂ => Y.y₂, by
    ext x
    simp [Xα, Yβ, α, β]
    cases x <;> rfl
  ⟩

theorem fgneq : f ≠ g := by
  intro h
  have hv : f.val = g.val := by grind
  have := congr_fun hv X.x₁
  contradiction

example : ¬((∀ x : termSWE ⟶ Xα, f ⊚ x = g ⊚ x) → f = g) := by
  push Not
  constructor
  · intro h
    exfalso
    have := h.prop
    have := congr_fun this ()
    simp [termSWE, id_eq, Xα, α] at this
    split at this <;> simp_all
  · exact fgneq

end ExIV_5a

namespace ExIV_5b

def X : IrreflexiveGraph := {
  A := Empty
  D := Fin 2
  toSrc := Empty.elim
  toTgt := Empty.elim
}

def Y : IrreflexiveGraph := {
  A := Unit
  D := Fin 2
  toSrc := fun _ ↦ 0
  toTgt := fun _ ↦ 1
}

def f : X ⟶ Y :=
  ⟨⟨Empty.elim,
    fun
    | ⟨0, _⟩ => ⟨0, by simp⟩
    | ⟨1, _⟩ => ⟨1, by simp⟩
    ⟩,
    (by ext x; cases x),
    (by ext x; cases x)
  ⟩

def g : X ⟶ Y :=
  ⟨⟨Empty.elim,
    fun
    | ⟨0, _⟩ => ⟨1, by simp⟩
    | ⟨1, _⟩ => ⟨0, by simp⟩
    ⟩,
    (by ext x; cases x),
    (by ext x; cases x)
  ⟩

theorem fgneqIG : f ≠ g := by
  intro h
  have hv : f.val.2 = g.val.2 := by grind
  have := congr_fun hv ⟨0, by simp⟩
  simp [f, g] at this
  grind

example : ¬((∀ x : termIG ⟶ X, f ⊚ x = g ⊚ x) → f = g) := by
  push Not
  constructor
  · intro h
    exfalso
    let f := h.1.1
    simp only [termIG, X] at f
    have x := f ()
    exact Aesop.BuiltinRules.empty_false x
  · exact fgneqIG

end ExIV_5b

/-!
Excerpt (p. 215)
-/
abbrev A : IrreflexiveGraph := {
  A := Unit
  D := Fin 2
  toSrc := fun _ ↦ 0
  toTgt := fun _ ↦ 1
}

abbrev D : IrreflexiveGraph := {
  A := Empty
  D := Unit
  toSrc := Empty.elim
  toTgt := Empty.elim
}

example
    (X Y : IrreflexiveGraph)
    (f g : X ⟶ Y)
    (ha : ∀ x : A ⟶ X, f ⊚ x = g ⊚ x)
    (hd : ∀ x : D ⟶ X, f ⊚ x = g ⊚ x)
    : f = g := by
  apply Subtype.ext
  apply Prod.ext
  -- Prove equality on ArrowMap
  · funext a
    let x : A ⟶ X := {
      val := (
        fun _ ↦ a,
        fun (i : Fin 2) ↦ if i = 0 then X.toSrc a else X.toTgt a
      )
      property := by
        constructor <;> rfl
    }
    have h := ha x
    apply_fun (fun k ↦ k.val.1 ()) at h
    exact h
  -- Prove equality on DotMap
  · funext d
    let x : D ⟶ X := {
      val := (Empty.elim, fun _ ↦ d)
      property := by
        constructor <;> (funext e; exact Empty.elim e)
    }
    have h := hd x
    apply_fun (fun k ↦ k.val.2 ()) at h
    exact h

/-!
Exercise IV.6 (p. 215)
-/
example
    (X Y : SetWithEndomap)
    (f g : X ⟶ Y)
    : ∃ N : SetWithEndomap,
        (∀ x : N ⟶ X, f ⊚ x = g ⊚ x) → f = g := by
  use ℕσ
  intro h
  apply Subtype.ext
  ext z
  simp only at z
  -- build a map from ℕσ to X
  -- 0 -> z
  -- 1 -> α z
  -- 2 -> α (α z)
  -- etc
  let xz : ℕσ ⟶ X := iter X (fun _ ↦ z)
  specialize h xz
  have h := (Subtype.ext_iff.mp h)
  have := congr_fun h (0 : ℕ)
  simpa [iter, xz] using this

/-!
Exercise IV.7 (p. 215)
-/
theorem initial_objects_unique_up_to_iso {𝒞 : Type u} [Category.{v, u} 𝒞] {S₁ S₂ : 𝒞}
    (hS₁ : IsInitial S₁) (hS₂ : IsInitial S₂)
    : ∃! s : S₁ ⟶ S₂, IsIso s := by
  let f := hS₁.to S₂
  let g := hS₂.to S₁
  use f
  constructor
  · simp only
    use g
    -- g comp f is S1 to S1 so it has to be unique but 1 is also S1 to S1
    constructor
    · exact IsInitial.hom_ext hS₁ (g ⊚ f) (𝟙 S₁)
    · exact IsInitial.hom_ext hS₂ (f ⊚ g) (𝟙 S₂)
  · intro h hs
    exact IsInitial.hom_ext hS₁ h f

/-!
Exercise IV.8 (p. 216)

The strategy is to define the initial objects in each category explicitly.
Since these are mostly empty sets or build of empty sets, the functions
from them are mostly Empty.elim or build thereof.
-/

theorem initial_objects_unique_in_types
    {Zero X : Type}
    (hZero : IsInitial Zero) (f : X ⟶ Zero)
    : (∀ g : X ⟶ Zero, g = f) ∧ Nonempty (IsInitial X) := by
  -- Zero might not be equal to Empty (just isomorphic),
  -- but we can find a map to Empty.
  -- and if there is a map to Empty, Zero is also empty.
  haveI : IsEmpty Zero := Function.isEmpty (hZero.to Empty)

  -- now because of f, X is also empty
  haveI hX : IsEmpty X := Function.isEmpty f
  constructor
  · intro g
    ext x
    exact isEmptyElim x
  · constructor
    exact IsInitial.ofUniqueHom (
      by
        exact fun Y ↦ fun x => isEmptyElim x
    ) (
      by
        exact fun Y ↦ fun X' ↦ funext fun x => isEmptyElim x
    )

def emptyIG : IrreflexiveGraph := {
  A := Empty
  D := Empty
  toSrc := Empty.elim
  toTgt := Empty.elim
}

example
    {Zero X : IrreflexiveGraph}
    (hZero : IsInitial Zero) (f : X ⟶ Zero)
    : (∀ g : X ⟶ Zero, g = f) ∧ Nonempty (IsInitial X) := by
  -- `Zero.A`, `Zero.D` map to `Empty` (via `hZero.to emptyIG`), so both are empty
  -- and initial in `Type`; apply the `Type`-level result on each coordinate.
  haveI : IsEmpty emptyIG.A := inferInstanceAs (IsEmpty Empty)
  haveI : IsEmpty emptyIG.D := inferInstanceAs (IsEmpty Empty)
  haveI : IsEmpty Zero.A := Function.isEmpty (hZero.to emptyIG).val.1
  haveI : IsEmpty Zero.D := Function.isEmpty (hZero.to emptyIG).val.2
  have initA : IsInitial Zero.A :=
    IsInitial.ofUniqueHom (fun _ z => isEmptyElim z)
      (fun _ _ => funext fun z => isEmptyElim z)
  have initD : IsInitial Zero.D :=
    IsInitial.ofUniqueHom (fun _ z => isEmptyElim z)
      (fun _ _ => funext fun z => isEmptyElim z)
  have hCA := initial_objects_unique_in_types initA f.val.1
  have hCD := initial_objects_unique_in_types initD f.val.2
  -- underlying arrow/dot maps agree ⇒ the graph morphisms agree (`hom_ext`)
  refine ⟨fun g => IrreflexiveGraph.hom_ext g f (hCA.1 g.val.1) (hCD.1 g.val.2), ⟨?_⟩⟩
  -- `X.A`, `X.D` are empty too, so `X` is initial in `IrreflexiveGraph`.
  haveI : IsEmpty X.A := Function.isEmpty f.val.1
  haveI : IsEmpty X.D := Function.isEmpty f.val.2
  exact IsInitial.ofUniqueHom
    (fun _ => ⟨(fun a => isEmptyElim a, fun d => isEmptyElim d),
      funext fun a => isEmptyElim a, funext fun a => isEmptyElim a⟩)
    (fun _ _ => IrreflexiveGraph.hom_ext _ _
      (funext fun a => isEmptyElim a) (funext fun d => isEmptyElim d))

def emptySWE : SetWithEndomap := {
  carrier := Empty
  toEnd := Empty.elim
}

example
    {Zero X : SetWithEndomap}
    (hZero : IsInitial Zero) (f : X ⟶ Zero)
    : (∀ g : X ⟶ Zero, g = f) ∧ Nonempty (IsInitial X) := by
  -- `Zero.carrier` maps to `Empty` (via `hZero.to emptySWE`), so it is empty and
  -- hence initial in `Type`; the `Type`-level result then does the real work.
  haveI : IsEmpty emptySWE.carrier := inferInstanceAs (IsEmpty Empty)
  haveI : IsEmpty Zero.carrier := Function.isEmpty (hZero.to emptySWE).val
  have hZeroC : IsInitial Zero.carrier :=
    IsInitial.ofUniqueHom (fun _ z => isEmptyElim z)
      (fun _ _ => funext fun z => isEmptyElim z)
  have hC := initial_objects_unique_in_types hZeroC f.val
  -- underlying maps agree ⇒ the `SetWithEndomap` morphisms agree (`Subtype.ext`)
  refine ⟨fun g => Subtype.ext (hC.1 g.val), ⟨?_⟩⟩
  -- `X.carrier` is empty too, so `X` is initial in `SetWithEndomap`.
  haveI : IsEmpty X.carrier := Function.isEmpty f.val
  exact IsInitial.ofUniqueHom
    (fun _ => ⟨fun x => isEmptyElim x, funext fun x => isEmptyElim x⟩)
    (fun _ _ => Subtype.ext (funext fun x => isEmptyElim x))

/-!
Exercise IV.9 (p. 216)
-/
structure PointedSet where
  carrier : Type
  point : One ⟶ carrier

instance : Category PointedSet where
  Hom X Y := {
    f : X.carrier ⟶ Y.carrier //
        f ⊚ X.point = Y.point -- commutes
  }
  id X := ⟨𝟙 X.carrier, rfl⟩
  comp f g := ⟨
    g.val ⊚ f.val,
    by
      obtain hf_comm := f.property
      obtain hg_comm := g.property
      rw [← Category.assoc, hf_comm, hg_comm]
  ⟩

example
    {T : PointedSet}
    (hT : IsTerminal T)
    : Nonempty (IsInitial T)
    ∧ ¬(∀ X : PointedSet, Nonempty (IsInitial X)) :=
  sorry

namespace ExIV_9

abbrev PointedSet := Under Unit

example
    {T : PointedSet}
    (hT : IsTerminal T)
    : Nonempty (IsInitial T)
    ∧ ¬(∀ X : PointedSet, Nonempty (IsInitial X)) :=
  sorry

end ExIV_9

example
    {T : Pointed.{0}}
    (hT : IsTerminal T)
    : Nonempty (IsInitial T)
    ∧ ¬(∀ X : Pointed.{0}, Nonempty (IsInitial X)) :=
  sorry

/-!
Exercise IV.10 (p. 216)
-/
abbrev Two := Fin 2

structure BipointedSet where
  carrier : Type
  point : Two ⟶ carrier

instance : Category BipointedSet where
  Hom X Y := {
    f : X.carrier ⟶ Y.carrier //
        f ⊚ X.point = Y.point -- commutes
  }
  id X := ⟨𝟙 X.carrier, rfl⟩
  comp f g := ⟨
    g.val ⊚ f.val,
    by
      obtain hf_comm := f.property
      obtain hg_comm := g.property
      rw [← Category.assoc, hf_comm, hg_comm]
  ⟩

namespace ExIV_10a

def BSTwo : BipointedSet := {
  carrier := Two
  point := 𝟙 Two
}

example : Nonempty (IsInitial BSTwo)
          ∧ ¬(∀ (X : BipointedSet) (f g : X ⟶ BSTwo), f = g) :=
  sorry

end ExIV_10a

namespace ExIV_10b

abbrev BipointedSet := Under (Fin 2)

def BSTwo : BipointedSet := Under.mk (𝟙 (Fin 2))

example : Nonempty (IsInitial BSTwo)
          ∧ ¬(∀ (X : BipointedSet) (f g : X ⟶ BSTwo), f = g) :=
  sorry

end ExIV_10b

namespace ExIV_10c

abbrev BSTwo : Bipointed := ⟨Fin 2, (0, 1)⟩

example : Nonempty (IsInitial BSTwo)
          ∧ ¬(∀ (X : Bipointed) (f g : X ⟶ BSTwo), f = g) :=
  sorry

end ExIV_10c

/-!
Exercise IV.11 (p. 216)
-/
example : ∀ X, IsEmpty (IsInitial X) → Nonempty (⊤_ Type ⟶ X) :=
  sorry

instance : HasTerminal SetWithEndomap where
  has_limit _ := HasLimit.mk' (
    exists_limit := Nonempty.intro {
      cone := {
        pt := {
          carrier := Unit
          toEnd := id
        }
        π := { app := fun j ↦ j.as.elim }
      }
      isLimit := {
        lift := fun _ ↦ {
          val := fun _ ↦ ()
          property := rfl
        }
        fac := fun _ j ↦ j.as.elim
        uniq _ _ _ := rfl
      }
    }
  )

example : ¬(∀ X : SetWithEndomap, IsEmpty (IsInitial X) →
    Nonempty (⊤_ SetWithEndomap ⟶ X)) :=
  sorry

instance : HasTerminal IrreflexiveGraph where
  has_limit _ := HasLimit.mk' (
    exists_limit := Nonempty.intro {
      cone := {
        pt := {
          A := Unit
          D := Unit
          toSrc := fun _ ↦ ()
          toTgt := fun _ ↦ ()
        }
        π := { app := fun j ↦ j.as.elim }
      }
      isLimit := {
        lift := fun _ ↦ {
          val := (fun _ ↦ (), fun _ ↦ ())
          property := by
            constructor <;> rfl
        }
        fac := fun _ j ↦ j.as.elim
        uniq _ _ _ := rfl
      }
    }
  )

example : ¬(∀ X : IrreflexiveGraph, IsEmpty (IsInitial X) →
    Nonempty (⊤_ IrreflexiveGraph ⟶ X)) :=
  sorry

/-!
Product (binary) (p. 217)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (P B₁ B₂ : 𝒞) (p₁ : P ⟶ B₁) (p₂ : P ⟶ B₂)
    : Nonempty (IsLimit (BinaryFan.mk p₁ p₂)) ↔
      ∀ (X : 𝒞) (f₁ : X ⟶ B₁) (f₂ : X ⟶ B₂),
          ∃! f : X ⟶ P, p₁ ⊚ f = f₁ ∧ p₂ ⊚ f = f₂ := by
  constructor
  · rintro ⟨h⟩ X f₁ f₂
    let s := BinaryFan.mk f₁ f₂
    use h.lift s
    and_intros
    · exact (h.fac s ⟨WalkingPair.left⟩)
    · exact (h.fac s ⟨WalkingPair.right⟩)
    · intro m ⟨h₁, h₂⟩
      apply h.uniq s
      rintro ⟨_ | _⟩
      all_goals
        dsimp
        first | erw [h₁] | erw [h₂]
        rfl
  · intro h
    constructor
    let hs (s : BinaryFan B₁ B₂) :=
      let f₁ : s.pt ⟶ B₁ := s.π.app ⟨WalkingPair.left⟩
      let f₂ : s.pt ⟶ B₂ := s.π.app ⟨WalkingPair.right⟩
      h s.pt f₁ f₂
    refine IsLimit.mk ?_ ?_ ?_
    · -- lift
      intro s
      exact (hs s).choose
    · -- fac
      intro s j
      rcases j with ⟨_ | _⟩
      · exact (hs s).choose_spec.1.1
      · exact (hs s).choose_spec.1.2
    · -- uniq
      intro s m w
      apply (hs s).choose_spec.2
      constructor
      · exact (w ⟨WalkingPair.left⟩)
      · exact (w ⟨WalkingPair.right⟩)

/-!
Exercise IV.12 (p. 217)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] (B₁ B₂ : 𝒞)
    (coneP coneQ : BinaryFan B₁ B₂)
    (prodP : IsLimit coneP) (prodQ : IsLimit coneQ)
    : ∃! f : coneP.pt ⟶ coneQ.pt,
        (coneQ.fst ⊚ f = coneP.fst ∧ coneQ.snd ⊚ f = coneP.snd)
        ∧ IsIso f :=
  sorry

/-!
Exercise IV.13 (p. 217)
-/
namespace ExIV_13

variable {𝒞 : Type u} [Category.{v, u} 𝒞]
         [HasBinaryProducts 𝒞] [HasTerminal 𝒞]

abbrev Point' (X : 𝒞) := ⊤_ 𝒞 ⟶ X

example (B₁ B₂ : 𝒞)
    : (∀ p : Point' (B₁ ⨯ B₂),
        ∃! b : Point' B₁ × Point' B₂, p = prod.lift b.1 b.2)
    ∧ (∀ (b₁ : Point' B₁) (b₂ : Point' B₂),
        ∃! p : Point' (B₁ ⨯ B₂),
        b₁ = prod.fst ⊚ p ∧ b₂ = prod.snd ⊚ p) :=
  sorry

end ExIV_13

/-!
Exercise IV.14 (p. 219)
-/
structure SetA (carrierA : Type) where
  carrier : Type
  action : carrierA × carrier ⟶ carrier

instance {carrierA : Type} : Category (SetA carrierA) where
  Hom X Y := sorry
  id X := sorry
  comp f g := sorry

/-!
Product (p. 220)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] {I : Type}
    (P : 𝒞) (Cᵢ : I → 𝒞) (pᵢ : (i : I) → (P ⟶ Cᵢ i))
    : Nonempty (IsLimit (Fan.mk P pᵢ)) ↔
      ∀ (X : 𝒞) (fᵢ : (i : I) → (X ⟶ Cᵢ i)),
          ∃! f : X ⟶ P, (∀ i : I, pᵢ i ⊚ f = fᵢ i) := by
  constructor
  · rintro ⟨h⟩ X fᵢ
    let s := Fan.mk X fᵢ
    use h.lift s
    constructor
    · intro i
      exact h.fac s ⟨i⟩
    · intro m hᵢ
      apply h.uniq s
      intro i
      exact hᵢ i.as
  · intro h
    constructor
    let hs (s : Fan Cᵢ) :=
      let fᵢ : (i : I) → (s.pt ⟶ Cᵢ i) := fun i ↦ s.π.app ⟨i⟩
      h s.pt fᵢ
    refine IsLimit.mk ?_ ?_ ?_
    · -- lift
      intro s
      exact (hs s).choose
    · -- fac
      intro s i
      exact (hs s).choose_spec.1 i.as
    · -- uniq
      intro s m w
      apply (hs s).choose_spec.2
      intro i
      exact w ⟨i⟩

/-!
Theorem (uniqueness of products) (p. 221)
-/
theorem uniqueness_of_products
    {𝒞 : Type u} [Category.{v, u} 𝒞] {I : Type} (Cᵢ : I → 𝒞)
    (coneP coneQ : Fan Cᵢ)
    (prodP : IsLimit coneP) (prodQ : IsLimit coneQ)
    : ∃! f : coneP.pt ⟶ coneQ.pt,
        (∀ i : I, coneQ.proj i ⊚ f = coneP.proj i)
        ∧ IsIso f := by
  use prodQ.lift coneP -- f
  and_intros
  · -- Show that qᵢ ⊚ f = pᵢ
    intro i
    exact prodQ.fac coneP ⟨i⟩
  · -- Show that f is an isomorphism
    apply IsIso.mk
    use prodP.lift coneQ -- f⁻¹
    constructor
    · -- f⁻¹ ⊚ f = 𝟙 P
      rw [prodP.uniq coneP (𝟙 coneP.pt) (fun _ ↦ Category.id_comp _)]
      apply prodP.uniq coneP
      intro i
      rw [Category.assoc, prodP.fac, prodQ.fac]
    · -- f ⊚ f⁻¹ = 𝟙 Q
      rw [prodQ.uniq coneQ (𝟙 coneQ.pt) (fun _ ↦ Category.id_comp _)]
      apply prodQ.uniq coneQ
      intro i
      rw [Category.assoc, prodQ.fac, prodP.fac]
  · -- Show that f is unique
    intro f ⟨hᵢ, _⟩
    apply prodQ.uniq coneP
    intro i
    exact hᵢ i.as

/-!
Exercise IV.16 (p. 221)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] (C_a C_b C_c : 𝒞)
    (P : 𝒞) (p_a : P ⟶ C_a) (p_b : P ⟶ C_b)
    (h_prodP : ∀ (X : 𝒞) (f₁ : X ⟶ C_a) (f₂ : X ⟶ C_b),
        ∃! f : X ⟶ P, p_a ⊚ f = f₁ ∧ p_b ⊚ f = f₂)
    (Q : 𝒞) (q : Q ⟶ P) (q_c : Q ⟶ C_c)
    (h_prodQ : ∀ (X : 𝒞) (f₁ : X ⟶ P) (f₂ : X ⟶ C_c),
        ∃! f : X ⟶ Q, q ⊚ f = f₁ ∧ q_c ⊚ f = f₂)
    : ∀ (X : 𝒞) (f_a : X ⟶ C_a) (f_b : X ⟶ C_b) (f_c : X ⟶ C_c),
        ∃! f : X ⟶ Q, p_a ⊚ q ⊚ f = f_a ∧
                       p_b ⊚ q ⊚ f = f_b ∧
                       q_c ⊚ f = f_c :=
  sorry

example {𝒞 : Type u} [Category.{v, u} 𝒞] (C_a C_b C_c : 𝒞)
    (coneP : Fan (fun | 0 => C_a | 1 => C_b : Fin 2 → 𝒞))
    (prodP : IsLimit coneP)
    (coneQ : Fan (fun | 0 => coneP.pt | 1 => C_c : Fin 2 → 𝒞))
    (prodQ : IsLimit coneQ)
    : IsLimit (
        Fan.mk coneQ.pt (fun i : Fin 3 ↦ match i with
          | 0 => coneP.π.app ⟨0⟩ ⊚ coneQ.π.app ⟨0⟩
          | 1 => coneP.π.app ⟨1⟩ ⊚ coneQ.π.app ⟨0⟩
          | 2 => coneQ.π.app ⟨1⟩)
          : Fan (fun | 0 => C_a | 1 => C_b | 2 => C_c)
      ) :=
  sorry

/-!
Sum (p. 222)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (S B₁ B₂ : 𝒞) (j₁ : B₁ ⟶ S) (j₂ : B₂ ⟶ S)
    : Nonempty (IsColimit (BinaryCofan.mk j₁ j₂)) ↔
      ∀ (Y : 𝒞) (g₁ : B₁ ⟶ Y) (g₂ : B₂ ⟶ Y),
          ∃! g : S ⟶ Y, g ⊚ j₁ = g₁ ∧ g ⊚ j₂ = g₂ := by
  constructor
  · rintro ⟨h⟩ Y g₁ g₂
    let s := BinaryCofan.mk g₁ g₂
    use h.desc s
    and_intros
    · exact (h.fac s ⟨WalkingPair.left⟩)
    · exact (h.fac s ⟨WalkingPair.right⟩)
    · intro m ⟨h₁, h₂⟩
      apply h.uniq s
      rintro ⟨_ | _⟩
      all_goals
        dsimp
        first | erw [h₁] | erw [h₂]
        rfl
  · intro h
    constructor
    let hs (s : BinaryCofan B₁ B₂) :=
      let g₁ : B₁ ⟶ s.pt := s.ι.app ⟨WalkingPair.left⟩
      let g₂ : B₂ ⟶ s.pt := s.ι.app ⟨WalkingPair.right⟩
      h s.pt g₁ g₂
    refine IsColimit.mk ?_ ?_ ?_
    · -- desc
      intro s
      exact (hs s).choose
    · -- fac
      intro s j
      rcases j with ⟨_ | _⟩
      · exact (hs s).choose_spec.1.1
      · exact (hs s).choose_spec.1.2
    · -- uniq
      intro s m w
      apply (hs s).choose_spec.2
      constructor
      · exact (w ⟨WalkingPair.left⟩)
      · exact (w ⟨WalkingPair.right⟩)

/-!
Exercise IV.17 (p. 222)
-/
example (S B₁ B₂ : Type) (j₁ : B₁ ⟶ S) (j₂ : B₂ ⟶ S)
    (h_sum : ∀ (Y : Type) (g₁ : B₁ ⟶ Y) (g₂ : B₂ ⟶ Y),
        ∃! g : S ⟶ Y, (g ⊚ j₁ = g₁ ∧ g ⊚ j₂ = g₂))
    : ∀ s : Unit ⟶ S,
        Xor' (∃ b₁ : Unit ⟶ B₁, j₁ ⊚ b₁ = s)
             (∃ b₂ : Unit ⟶ B₂, j₂ ⊚ b₂ = s) :=
  sorry

example (S B₁ B₂ : SetWithEndomap) (j₁ : B₁ ⟶ S) (j₂ : B₂ ⟶ S)
    (h_sum : ∀ (Y : SetWithEndomap) (g₁ : B₁ ⟶ Y) (g₂ : B₂ ⟶ Y),
        ∃! g : S ⟶ Y, (g ⊚ j₁ = g₁ ∧ g ⊚ j₂ = g₂))
    : ∀ s : termSWE ⟶ S,
        Xor' (∃ b₁ : termSWE ⟶ B₁, j₁ ⊚ b₁ = s)
             (∃ b₂ : termSWE ⟶ B₂, j₂ ⊚ b₂ = s) :=
  sorry

example (S B₁ B₂ : IrreflexiveGraph) (j₁ : B₁ ⟶ S) (j₂ : B₂ ⟶ S)
    (h_sum : ∀ (Y : IrreflexiveGraph) (g₁ : B₁ ⟶ Y) (g₂ : B₂ ⟶ Y),
        ∃! g : S ⟶ Y, (g ⊚ j₁ = g₁ ∧ g ⊚ j₂ = g₂))
    : ∀ s : termIG ⟶ S,
        Xor' (∃ b₁ : termIG ⟶ B₁, j₁ ⊚ b₁ = s)
             (∃ b₂ : termIG ⟶ B₂, j₂ ⊚ b₂ = s) :=
  sorry

/-!
Exercise IV.18 (p. 222)
-/
namespace ExIV_18

abbrev X := Fin 2

def f₁ : X ⟶ Unit := fun _ ↦ ()
def j₁ : Unit ⟶ Unit ⊕ Unit := fun _ ↦ Sum.inl ()
def f₂ : X ⟶ Unit := fun _ ↦ ()
def j₂ : Unit ⟶ Unit ⊕ Unit := fun _ ↦ Sum.inr ()

def f : X ⟶ Unit ⊕ Unit :=
  sorry

example : ∃ f' : X ⟶ Unit ⊕ Unit,
    f' ≠ j₁ ⊚ f₁ ∧ f' ≠ j₂ ⊚ f₂ :=
  sorry

end ExIV_18

/-!
Exercise IV.19 (p. 222)
-/
noncomputable example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (A B C AB BC AB_C A_BC : 𝒞)
    (j₁ : A ⟶ AB) (j₂ : B ⟶ AB) (j₃ : AB ⟶ AB_C) (j₄ : C ⟶ AB_C)
    (hAB : ∀ (Y : 𝒞) (g₁ : A ⟶ Y) (g₂ : B ⟶ Y),
        ∃! g : AB ⟶ Y, (g ⊚ j₁ = g₁ ∧ g ⊚ j₂ = g₂))
    (hAB_C : ∀ (Y : 𝒞) (g₁ : AB ⟶ Y) (g₂ : C ⟶ Y),
        ∃! g : AB_C ⟶ Y, (g ⊚ j₃ = g₁ ∧ g ⊚ j₄ = g₂))
    (k₁ : B ⟶ BC) (k₂ : C ⟶ BC) (k₃ : A ⟶ A_BC) (k₄ : BC ⟶ A_BC)
    (hBC : ∀ (Y : 𝒞) (g₁ : B ⟶ Y) (g₂ : C ⟶ Y),
        ∃! g : BC ⟶ Y, (g ⊚ k₁ = g₁ ∧ g ⊚ k₂ = g₂))
    (hA_BC : ∀ (Y : 𝒞) (g₁ : A ⟶ Y) (g₂ : BC ⟶ Y),
        ∃! g : A_BC ⟶ Y, (g ⊚ k₃ = g₁ ∧ g ⊚ k₄ = g₂)) :
    AB_C ≅ A_BC :=
  sorry

noncomputable example {𝒞 : Type u} [Category.{v, u} 𝒞]
    [HasBinaryCoproducts 𝒞] (A B C : 𝒞) :
    (A ⨿ B) ⨿ C ≅ A ⨿ (B ⨿ C) :=
  sorry

def DistributiveLaw (T : Type u) [Category.{v, u} T] : Prop :=
  ∀ (A B C AxB AxC AxB_AxC B_C AxB_C : T)
    (p₁ : AxB ⟶ A) (p₂ : AxB ⟶ B)
    (p₃ : AxC ⟶ A) (p₄ : AxC ⟶ C)
    (j₁ : AxB ⟶ AxB_AxC) (j₂ : AxC ⟶ AxB_AxC)
    (j₃ : B ⟶ B_C) (j₄ : C ⟶ B_C)
    (p₅ : AxB_C ⟶ A) (p₆ : AxB_C ⟶ B_C),
    (∀ X f₁ f₂, ∃! f : X ⟶ AxB, p₁ ⊚ f = f₁ ∧ p₂ ⊚ f = f₂) →
    (∀ X f₁ f₂, ∃! f : X ⟶ AxC, p₃ ⊚ f = f₁ ∧ p₄ ⊚ f = f₂) →
    (∀ Y g₁ g₂, ∃! g : AxB_AxC ⟶ Y, g ⊚ j₁ = g₁ ∧ g ⊚ j₂ = g₂) →
    (∀ Y g₁ g₂, ∃! g : B_C ⟶ Y, g ⊚ j₃ = g₁ ∧ g ⊚ j₄ = g₂) →
    (∀ X f₁ f₂, ∃! f : X ⟶ AxB_C, p₅ ⊚ f = f₁ ∧ p₆ ⊚ f = f₂) →
    Nonempty (AxB_AxC ≅ AxB_C)

/-!
Exercise IV.20 (p. 223)
-/
namespace ExIV_20

abbrev A : PointedSet := { carrier := Fin 2, point := fun _ ↦ 0 }
abbrev B : PointedSet := { carrier := Unit, point := id }
abbrev C : PointedSet := { carrier := Unit, point := id }

abbrev AxB : PointedSet := {
  carrier := Fin 2 × Unit
  point := fun _ ↦ (0, ())
}

abbrev AxC : PointedSet := {
  carrier := Fin 2 × Unit
  point := fun _ ↦ (0, ())
}

abbrev AxB_AxC : PointedSet := {
  carrier := (Fin 2 × Unit) ⊕ Unit
  point := fun _ ↦ Sum.inl (0, ())
}

abbrev B_C : PointedSet := { carrier := Unit, point := id }

abbrev AxB_C : PointedSet := {
  carrier := Fin 2 × Unit
  point := fun _ ↦ (0, ())
}

def p₁ : AxB ⟶ A := ⟨fun p ↦ p.1, rfl⟩
def p₂ : AxB ⟶ B := ⟨fun p ↦ p.2, rfl⟩
def p₃ : AxC ⟶ A := ⟨fun p ↦ p.1, rfl⟩
def p₄ : AxC ⟶ C := ⟨fun p ↦ p.2, rfl⟩

def j₁ : AxB ⟶ AxB_AxC := ⟨
  fun
  | (0, _) => Sum.inl (0, ())
  | (1, _) => Sum.inl (1, ()),
  rfl
⟩

def j₂ : AxC ⟶ AxB_AxC := ⟨
  fun
  | (0, _) => Sum.inl (0, ())
  | (1, _) => Sum.inr (),
  rfl
⟩

def j₃ : B ⟶ B_C := ⟨id, rfl⟩
def j₄ : C ⟶ B_C := ⟨id, rfl⟩

def p₅ : AxB_C ⟶ A := ⟨fun p ↦ p.1, rfl⟩
def p₆ : AxB_C ⟶ B_C := ⟨fun p ↦ p.2, rfl⟩

example : ¬ DistributiveLaw PointedSet :=
  sorry

end ExIV_20

/-!
Exercise IV.21 (p. 223)
-/
example
    (coneAA : BinaryFan A A)
    (limitAA : IsLimit coneAA)
    (coconeADD : Cofan (fun | 0 => A | 1 => D | 2 => D :
        Fin 3 → IrreflexiveGraph))
    (colimitADD : IsColimit coconeADD) :
  coneAA.pt ≅ coconeADD.pt :=
  sorry

end CM

#min_imports

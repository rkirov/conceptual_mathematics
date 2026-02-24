import ConceptualMathematics.Article1
import ConceptualMathematics.Article3
import ConceptualMathematics.Session15
import Mathlib
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
example {𝒞 : Type u} [Category.{v, u} 𝒞] {One X Y : 𝒞}
    {_ : IsTerminal One} (_ : Unique (One ⟶ One))
    (f : X ⟶ Y) (x : One ⟶ X)
    : ∃ y : One ⟶ Y, y = f ⊚ x := by
  use f ⊚ x

/-!
Exercise IV.2 (p. 214)
-/
example (X : Type) : (∀ x : Point X, (∃! x' : X, x' = x ())) ∧
                     (∀ x' : X, (∃! x : Point X, x () = x')) := by
  constructor
  · intro x
    use x ()
    dsimp
    constructor
    · rfl
    · intros
      assumption
  · intro x'
    use (fun _ : Unit ↦ x')
    dsimp
    constructor
    · rfl
    · intro x hx
      funext (_ : Unit)
      exact hx

/-!
Exercise IV.3 (p. 214)
-/
def termSWE : SetWithEndomap := {
  carrier := Unit
  toEnd := id
}

example : Nonempty (IsTerminal termSWE) := by
  apply Nonempty.intro
  refine @IsTerminal.ofUnique _ _ termSWE (fun Y ↦ ?_)
  exact {
    default := {
      val := fun _ ↦ ()
      property := rfl
    }
    uniq := by
      intro f
      rfl
  }

example : ∀ (X : SetWithEndomap) (x : termSWE ⟶ X),
    X.toEnd (x.val ()) = x.val () := by
  intro X x
  have : X.toEnd ⊚ x.val = x.val ⊚ termSWE.toEnd :=
      x.property.symm
  exact congr_fun this ()

/-!
Exercise IV.4 (p. 214)
-/
def termIG : IrreflexiveGraph := {
  carrierA := Unit
  carrierD := Unit
  toSrc := fun _ ↦ ()
  toTgt := fun _ ↦ ()
}

example : Nonempty (IsTerminal termIG) := by
  apply Nonempty.intro
  refine @IsTerminal.ofUnique _ _ termIG (fun Y ↦ ?_)
  exact {
    default := {
      val := (fun _ ↦ (), fun _ ↦ ())
      property := by
        constructor <;> (intros; trivial)
    }
    uniq := by
      intro f
      rfl
  }

example : ∀ (X : IrreflexiveGraph) (x : termIG ⟶ X),
    X.toSrc (x.val.1 ()) = X.toTgt (x.val.1 ()) := by
  intro X x
  obtain ⟨hxSrc_comm, hxTgt_comm⟩ := x.property
  have h₁ := congr_fun hxSrc_comm ()
  have h₂ := congr_fun hxTgt_comm ()
  dsimp [termIG] at h₁ h₂
  rw [← h₁, h₂]

/-!
Exercise IV.5 (p. 214)
-/
namespace ExIV_5a

inductive X
  | x₁ | x₂

def α : X ⟶ X
  | X.x₁ => X.x₁
  | X.x₂ => X.x₁

def Xα : SetWithEndomap := {
  carrier := X
  toEnd := α
}

inductive Y
  | y₁ | y₂

def β : Y ⟶ Y
  | Y.y₁ => Y.y₁
  | Y.y₂ => Y.y₁

def Yβ : SetWithEndomap := {
  carrier := Y
  toEnd := β
}

def f : Xα ⟶ Yβ := ⟨
  fun
    | X.x₁ => Y.y₁
    | X.x₂ => Y.y₁,
  by
    funext x
    cases x <;> rfl
⟩

def g : Xα ⟶ Yβ := ⟨
  fun
    | X.x₁ => Y.y₁
    | X.x₂ => Y.y₂,
  by
    funext x
    cases x <;> rfl
⟩

example : ¬(∀ x : termSWE ⟶ Xα, f ⊚ x = g ⊚ x → f = g) := by
  push_neg
  let x : termSWE ⟶ Xα := ⟨fun _ ↦ X.x₁, rfl⟩
  use x
  constructor
  · rfl
  · by_contra h_eq
    have hf : f.val X.x₂ = Y.y₁ := rfl
    have hg : g.val X.x₂ = Y.y₂ := rfl
    rw [h_eq] at hf
    contradiction

end ExIV_5a

namespace ExIV_5b

inductive XA
  | a₁ | a₂

inductive XD
  | d₁ | d₂

def X : IrreflexiveGraph := {
  carrierA := XA
  carrierD := XD
  toSrc := fun
    | XA.a₁ => XD.d₁
    | XA.a₂ => XD.d₂
  toTgt := fun
    | XA.a₁ => XD.d₁
    | XA.a₂ => XD.d₁
}

inductive YA
  | a₁ | a₂

inductive YD
  | d₁ | d₂

def Y : IrreflexiveGraph := {
  carrierA := YA
  carrierD := YD
  toSrc := fun
    | YA.a₁ => YD.d₁
    | YA.a₂ => YD.d₂
  toTgt := fun
    | YA.a₁ => YD.d₁
    | YA.a₂ => YD.d₁
}

def f : X ⟶ Y := ⟨
  (fun _ ↦ YA.a₁, fun _ ↦ YD.d₁),
  by
    constructor
    all_goals
      funext a
      cases a <;> rfl
⟩

def g : X ⟶ Y := ⟨
  (fun
    | XA.a₁ => YA.a₁
    | XA.a₂ => YA.a₂,
   fun
    | XD.d₁ => YD.d₁
    | XD.d₂ => YD.d₂),
  by
    constructor
    all_goals
      funext a
      cases a <;> rfl
⟩

example : ¬(∀ x : termIG ⟶ X, f ⊚ x = g ⊚ x → f = g) := by
  push_neg
  let x : termIG ⟶ X := ⟨
    (fun _ ↦ XA.a₁, fun _ ↦ XD.d₁),
    ⟨rfl, rfl⟩
  ⟩
  use x
  constructor
  · rfl
  · by_contra h_eq
    have hf : (f.val.1 XA.a₂) = YA.a₁ := rfl
    have hg : (g.val.1 XA.a₂) = YA.a₂ := rfl
    rw [h_eq] at hf
    contradiction

end ExIV_5b

/-!
Excerpt (p. 215)
-/
def IrreflexiveGraph.A : IrreflexiveGraph := {
  carrierA := Unit
  carrierD := Fin 2
  toSrc := fun _ ↦ 0
  toTgt := fun _ ↦ 1
}

def IrreflexiveGraph.D : IrreflexiveGraph := {
  carrierA := Empty
  carrierD := Unit
  toSrc := Empty.elim
  toTgt := Empty.elim
}

open IrreflexiveGraph in
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
  intro hx
  apply Subtype.ext
  funext x'
  let x : ℕσ ⟶ X := {
    -- n ↦ X.toEnd^[n] x' for n = 0,1,2,...
    val := fun n ↦ Nat.recOn n x' (fun _ prev ↦ X.toEnd prev)
    property := rfl
  }
  have h := hx x
  apply_fun (fun k ↦ k.val (0 : ℕ)) at h
  exact h

/-!
Exercise IV.7 (p. 215)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] {S₁ S₂ : 𝒞}
    (hS₁ : IsInitial S₁) (hS₂ : IsInitial S₂)
    : ∃! s : S₁ ⟶ S₂, IsIso s := by
  let f : S₁ ⟶ S₂ := hS₁.to S₂
  let g : S₂ ⟶ S₁ := hS₂.to S₁
  have h_id₁ : g ⊚ f = 𝟙 S₁ := hS₁.hom_ext _ _
  have h_id₂ : f ⊚ g = 𝟙 S₂ := hS₂.hom_ext _ _
  use f
  constructor
  · exact { out := ⟨g, h_id₁, h_id₂⟩ }
  · intros
    exact hS₁.hom_ext _ _

/-!
Exercise IV.8 (p. 216)
-/
example
    {Zero X : Type}
    (hZero : IsInitial Zero) (f : X ⟶ Zero)
    : (∀ g : X ⟶ Zero, g = f) ∧ Nonempty (IsInitial X) := by
  have e : Zero ⟶ Empty := hZero.to Empty
  constructor
  · intro g
    exact IsInitial.strict_hom_ext hZero g f
  · constructor
    apply IsInitial.ofUnique (
      h := fun Y ↦ {
        default := hZero.to Y ⊚ f
        uniq := by
          intros
          funext x
          exact (e (f x)).elim
      }
    )

example
    {Zero X : IrreflexiveGraph}
    (hZero : IsInitial Zero) (f : X ⟶ Zero)
    : (∀ g : X ⟶ Zero, g = f) ∧ Nonempty (IsInitial X) := by
  let emptyIG : IrreflexiveGraph := {
    carrierA := Empty
    carrierD := Empty
    toSrc := Empty.elim
    toTgt := Empty.elim
  }
  have e : Zero ⟶ emptyIG := hZero.to emptyIG
  constructor
  · intros
    ext x
    · exact (e.val.1 (f.val.1 x)).elim
    · exact (e.val.2 (f.val.2 x)).elim
  · constructor
    apply IsInitial.ofUnique (
      h := fun Y ↦ {
        default := hZero.to Y ⊚ f
        uniq := by
          intros
          ext x
          · exact (e.val.1 (f.val.1 x)).elim
          · exact (e.val.2 (f.val.2 x)).elim
      }
    )

example
    {Zero X : SetWithEndomap}
    (hZero : IsInitial Zero) (f : X ⟶ Zero)
    : (∀ g : X ⟶ Zero, g = f) ∧ Nonempty (IsInitial X) := by
  let emptySWE : SetWithEndomap := {
    carrier := Empty
    toEnd := Empty.elim
  }
  have e : Zero ⟶ emptySWE := hZero.to emptySWE
  constructor
  · intros
    apply Subtype.ext
    funext x
    exact (e.val (f.val x)).elim
  · constructor
    apply IsInitial.ofUnique (
      h := fun Y ↦ {
        default := hZero.to Y ⊚ f
        uniq := by
          intros
          apply Subtype.ext
          funext x
          exact (e.val (f.val x)).elim
      }
    )

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
    ∧ ¬(∀ X : PointedSet, Nonempty (IsInitial X)) := by
  constructor
  · -- Define the object PSOne,
    let PSOne : PointedSet := {
      carrier := One
      point := 𝟙 One
    }
    -- and show that PSOne is terminal
    have hT' : IsTerminal PSOne := by
      apply IsTerminal.ofUnique (
        h := fun X ↦ {
          default := by
            exact ⟨fun _ ↦ (), rfl⟩
          uniq := by
            intros
            rfl
        }
      )
    -- PSOne is isomorphic to T,
    have h_iso : PSOne ≅ T := IsTerminal.uniqueUpToIso hT' hT
    -- so it suffices to show that PSOne is initial
    constructor
    apply IsInitial.ofIso _ h_iso
    exact IsInitial.ofUnique (
      h := fun Y ↦ {
        default := by
          exact ⟨Y.point, rfl⟩
        uniq := by
          intro a
          exact Subtype.ext a.property
      }
    )
  · -- Consider the pointed set X with two elements
    let X : PointedSet := {
      carrier := Fin 2
      point := fun _ ↦ 0
    }
    -- and two distinct endomorphisms
    let f₁ : X ⟶ X := {
      val := fun
        | 0 => 0
        | 1 => 0
      property := rfl
    }
    let f₂ : X ⟶ X := {
      val := fun
        | 0 => 0
        | 1 => 1
      property := rfl
    }
    intro h
    -- If X is intial,
    obtain ⟨hI⟩ := h X
    -- then there is a unique morphism from X to itself, so f₁ = f₂
    have h_eq : f₁ = f₂ := hI.hom_ext f₁ f₂
    -- But f₁ and f₂ are distinct, so X is not initial
    have : f₁.val = f₂.val := congr_arg Subtype.val h_eq
    exact zero_ne_one (congr_fun this 1)

namespace ExIV_9

abbrev PointedSet := Under Unit

example
    {T : PointedSet}
    (hT : IsTerminal T)
    : Nonempty (IsInitial T)
    ∧ ¬(∀ X : PointedSet, Nonempty (IsInitial X)) := by
  constructor
  · -- Define the object PSOne,
    let PSOne : PointedSet := Under.mk (𝟙 Unit)
    -- and show that PSOne is terminal
    have hT' : IsTerminal PSOne := by
      apply IsTerminal.ofUnique (
        h := fun X ↦ {
          default := Under.homMk (fun _ ↦ ())
          uniq := by
            intros
            rfl
        }
      )
    -- PSOne is isomorphic to T,
    have h_iso : PSOne ≅ T := IsTerminal.uniqueUpToIso hT' hT
    -- so it suffices to show that PSOne is initial
    constructor
    apply IsInitial.ofIso _ h_iso
    exact IsInitial.ofUnique (
      h := fun Y ↦ {
        default := Under.homMk Y.hom
        uniq := by
          intro a
          exact Under.UnderMorphism.ext (Under.w a)
      }
    )
  · -- Consider the pointed set X with two elements
    let X : PointedSet := Under.mk (fun _ ↦ (0 : Fin 2))
    -- and two distinct endomorphisms
    let f₁ : X ⟶ X := Under.homMk (fun
      | 0 => 0
      | 1 => 0
      : Fin 2 ⟶ Fin 2)
    let f₂ : X ⟶ X := Under.homMk (fun
      | 0 => 0
      | 1 => 1
      : Fin 2 ⟶ Fin 2)
    intro h
    -- If X is intial,
    obtain ⟨hI⟩ := h X
    -- then there is a unique morphism from X to itself, so f₁ = f₂
    have h_eq : f₁ = f₂ := hI.hom_ext f₁ f₂
    -- But f₁ and f₂ are distinct, so X is not initial
    have : f₁.right = f₂.right := Under.UnderMorphism.ext_iff.mp h_eq
    exact Fin.zero_ne_one (congr_fun this (1 : Fin 2))

end ExIV_9

example
    {T : Pointed.{0}}
    (hT : IsTerminal T)
    : Nonempty (IsInitial T)
    ∧ ¬(∀ X : Pointed.{0}, Nonempty (IsInitial X)) := by
  constructor
  · -- Define the object PSOne,
    let PSOne : Pointed := {
      X := One
      point := ()
    }
    -- and show that PSOne is terminal
    have hT' : IsTerminal PSOne := by
      apply IsTerminal.ofUnique (
        h := fun X ↦ {
          default := by
            exact ⟨fun _ ↦ (), rfl⟩
          uniq := by
            intros
            rfl
        }
      )
    -- PSOne is isomorphic to T,
    have h_iso : PSOne ≅ T := IsTerminal.uniqueUpToIso hT' hT
    -- so it suffices to show that PSOne is initial
    constructor
    apply IsInitial.ofIso _ h_iso
    exact IsInitial.ofUnique (
      h := fun Y ↦ {
        default := by
          exact ⟨fun _ ↦ Y.point, rfl⟩
        uniq := by
          intro a
          apply Pointed.Hom.ext
          funext x
          exact a.map_point
      }
    )
  · -- Consider the pointed set X with two elements
    let X : Pointed := {
      X := Fin 2
      point := 0
    }
    -- and two distinct endomorphisms
    let f₁ : X ⟶ X := {
      toFun := fun
        | 0 => 0
        | 1 => 0
      map_point := rfl
    }
    let f₂ : X ⟶ X := {
      toFun := fun
        | 0 => 0
        | 1 => 1
      map_point := rfl
    }
    intro h
    -- If X is intial,
    have := h X
    obtain ⟨hI⟩ := h X
    -- then there is a unique morphism from X to itself, so f₁ = f₂
    have h_eq : f₁ = f₂ := hI.hom_ext f₁ f₂
    -- But f₁ and f₂ are distinct, so X is not initial
    have : f₁.toFun = f₂.toFun := Pointed.Hom.ext_iff.mp h_eq
    exact zero_ne_one (congr_fun this 1)

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
          ∧ ¬(∀ (X : BipointedSet) (f g : X ⟶ BSTwo), f = g) := by
  constructor
  · -- Show that BSTwo is initial
    constructor
    apply IsInitial.ofUnique (
      h := fun Y ↦ {
        default := by
          exact ⟨Y.point, rfl⟩
        uniq := by
          intro a
          exact Subtype.ext a.property
      }
    )
  · -- Consider the bipointed set X with three elements
    let X : BipointedSet := {
      carrier := Fin 3
      point := fun
        | 0 => 0
        | 1 => 1
    }
    -- and two distinct morphisms to the initial object
    let f : X ⟶ BSTwo := {
      val := (fun
      | 0 => 0
      | 1 => 1
      | 2 => 0
      : X.carrier ⟶ Two)
      property := by
        funext x
        fin_cases x <;> rfl
    }
    let g : X ⟶ BSTwo := {
      val := (fun
      | 0 => 0
      | 1 => 1
      | 2 => 1
      : X.carrier ⟶ Two)
      property := by
        funext x
        fin_cases x <;> rfl
    }
    intro h
    have : f.val = g.val := congr_arg Subtype.val (h X f g)
    exact Fin.zero_ne_one (congr_fun this 2)

end ExIV_10a

namespace ExIV_10b

abbrev BipointedSet := Under (Fin 2)

def BSTwo : BipointedSet := Under.mk (𝟙 (Fin 2))

example : Nonempty (IsInitial BSTwo)
          ∧ ¬(∀ (X : BipointedSet) (f g : X ⟶ BSTwo), f = g) := by
  constructor
  · -- Show that BSTwo is initial
    constructor
    apply IsInitial.ofUnique (
      h := fun Y ↦ {
        default := Under.homMk Y.hom
        uniq := by
          intro a
          exact Under.UnderMorphism.ext (Under.w a)
      }
    )
  · -- Consider the bipointed set X with three elements
    let X : BipointedSet := Under.mk (fun
      | 0 => 0
      | 1 => 1
      : Fin 2 ⟶ Fin 3)
    -- and two distinct morphisms to the initial object
    let f : X ⟶ BSTwo := Under.homMk (fun
      | 0 => 0
      | 1 => 1
      | 2 => 0
      : Fin 3 ⟶ Fin 2)
      (by
        funext (x : Fin 2)
        fin_cases x <;> rfl)
    let g : X ⟶ BSTwo := Under.homMk (fun
      | 0 => 0
      | 1 => 1
      | 2 => 1
      : Fin 3 ⟶ Fin 2)
      (by
        funext (x : Fin 2)
        fin_cases x <;> rfl)
    intro h
    have : f.right = g.right :=
        Under.UnderMorphism.ext_iff.mp (h X f g)
    exact Fin.zero_ne_one (congr_fun this (2 : Fin 3))

end ExIV_10b

namespace ExIV_10c

abbrev BSTwo : Bipointed := ⟨Fin 2, (0, 1)⟩

example : Nonempty (IsInitial BSTwo)
          ∧ ¬(∀ (X : Bipointed) (f g : X ⟶ BSTwo), f = g) := by
  constructor
  · -- Show that BSTwo is initial
    constructor
    apply IsInitial.ofUnique (
      h := fun Y ↦ {
        default := Bipointed.Hom.mk (fun
          | 0 => Y.toProd.1
          | 1 => Y.toProd.2
          : Fin 2 ⟶ Y.X)
          rfl
          rfl
        uniq := by
          intro a
          apply Bipointed.Hom.ext
          funext x
          fin_cases x
          · exact a.map_fst
          · exact a.map_snd
      }
    )
  · -- Consider the bipointed set X with three elements
    let X : Bipointed := ⟨Fin 3, (0, 1)⟩
    -- and two distinct morphisms to the initial object
    let f : X ⟶ BSTwo := Bipointed.Hom.mk (fun
      | 0 => 0
      | 1 => 1
      | 2 => 0
      : Fin 3 ⟶ Fin 2)
      rfl
      rfl
    let g : X ⟶ BSTwo := Bipointed.Hom.mk (fun
      | 0 => 0
      | 1 => 1
      | 2 => 1
      : Fin 3 ⟶ Fin 2)
      rfl
      rfl
    intro h
    have : f.toFun = g.toFun := Bipointed.Hom.ext_iff.mp (h X f g)
    exact Fin.zero_ne_one (congr_fun this (2 : Fin 3))

end ExIV_10c

/-!
Exercise IV.11 (p. 216)
-/
example : ∀ X, IsEmpty (IsInitial X) → Nonempty (⊤_ Type ⟶ X) := by
  intro X hX
  have h_nonempty : Nonempty X := by
    by_contra h_empty
    apply hX.false
    exact IsInitial.ofUnique (
      h := fun Y ↦ {
        default := fun x ↦ False.elim (h_empty (Nonempty.intro x))
        uniq := by
          intros
          funext x
          exact False.elim (h_empty (Nonempty.intro x))
      }
    )
  exact Nonempty.map (fun x _ ↦ x) h_nonempty

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
    Nonempty (⊤_ SetWithEndomap ⟶ X)) := by
  push_neg
  -- Define an object X which is not initial
  -- and has no morphism from the terminal object
  let X : SetWithEndomap := {
    carrier := Fin 2
    toEnd := fun
      | 0 => 1
      | 1 => 0
  }
  use X
  constructor
  · -- Assume towards a contradiction that X is initial
    refine ⟨fun hX : IsInitial X ↦ ?_⟩
    -- Define an object emptySWE (which is in fact initial)
    let emptySWE : SetWithEndomap := {
      carrier := Empty
      toEnd := Empty.elim
    }
    -- Since, by assumption, X is initial, there exists X ⟶ emptySWE
    let f : X ⟶ emptySWE := hX.to emptySWE
    -- But the assumption is false, since the carrier of emptySWE is ∅
    exact (f.val 0).elim
  · -- Assume towards a contradiction that there exists ⊤_ ⟶ X
    refine ⟨fun hX : ⊤_ SetWithEndomap ⟶ X ↦ ?_⟩
    -- Define a probe object U
    let U : SetWithEndomap := {
      carrier := Unit
      toEnd := id
    }
    let f : U ⟶ X := hX ⊚ terminal.from U
    -- Perform case analysis to show that the assumption is false
    have h_comm : (f.val ⊚ U.toEnd) () = (X.toEnd ⊚ f.val) () :=
        congr_fun f.property ()
    dsimp [U, X] at h_comm
    generalize f.val () = x at h_comm
    fin_cases x <;> trivial

instance : HasTerminal IrreflexiveGraph where
  has_limit _ := HasLimit.mk' (
    exists_limit := Nonempty.intro {
      cone := {
        pt := {
          carrierA := Unit
          carrierD := Unit
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
    Nonempty (⊤_ IrreflexiveGraph ⟶ X)) := by
  push_neg
  -- Define an object X which is not initial
  -- and has no morphism from the terminal object
  let X : IrreflexiveGraph := {
    carrierA := Fin 2
    carrierD := Fin 2
    toSrc := fun
      | 0 => 0
      | 1 => 1
    toTgt := fun
      | 0 => 1
      | 1 => 0
  }
  use X
  constructor
  · -- Assume towards a contradiction that X is initial
    refine ⟨fun hX : IsInitial X ↦ ?_⟩
    -- Define an object emptyIG (which is in fact initial)
    let emptyIG : IrreflexiveGraph := {
      carrierA := Empty
      carrierD := Empty
      toSrc := Empty.elim
      toTgt := Empty.elim
    }
    -- Since, by assumption, X is initial, there exists X ⟶ emptyIG
    let f : X ⟶ emptyIG := hX.to emptyIG
    -- But the assumption is false, since carrierA of emptyIG is ∅
    exact (f.val.1 0).elim
  · -- Assume towards a contradiction that there exists ⊤_ ⟶ X
    refine ⟨fun hX : ⊤_ IrreflexiveGraph ⟶ X ↦ ?_⟩
    -- Define a probe object U
    let U : IrreflexiveGraph := {
      carrierA := Unit
      carrierD := Unit
      toSrc := fun _ ↦ ()
      toTgt := fun _ ↦ ()
    }
    let f : U ⟶ X := hX ⊚ terminal.from U
    -- Perform case analysis to show that the assumption is false
    have h_src_comm := congr_fun f.property.1 ()
    have h_tgt_comm := congr_fun f.property.2 ()
    dsimp [U, X] at h_src_comm h_tgt_comm
    generalize f.val.1 () = x₁ at h_src_comm h_tgt_comm
    generalize f.val.2 () = x₂ at h_src_comm h_tgt_comm
    fin_cases x₁ <;> fin_cases x₂ <;> trivial

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
        first | rw [h₁] | rw [h₂]
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
        ∧ IsIso f := by
  use prodQ.lift coneP -- f
  and_intros
  · -- Show that q₁ ⊚ f = p₁
    exact prodQ.fac coneP ⟨WalkingPair.left⟩
  · -- Show that q₂ ⊚ f = p₂
    exact prodQ.fac coneP ⟨WalkingPair.right⟩
  · -- Show that f is an isomorphism
    apply IsIso.mk
    use prodP.lift coneQ -- f⁻¹
    constructor
    · -- f⁻¹ ⊚ f = 𝟙 P
      rw [prodP.uniq coneP (𝟙 coneP.pt)
                           (fun _ ↦ Category.id_comp _)]
      apply prodP.uniq coneP
      intro j
      rw [Category.assoc, prodP.fac, prodQ.fac]
    · -- f ⊚ f⁻¹ = 𝟙 Q
      rw [prodQ.uniq coneQ (𝟙 coneQ.pt)
                           (fun _ ↦ Category.id_comp _)]
      apply prodQ.uniq coneQ
      intro j
      rw [Category.assoc, prodQ.fac, prodP.fac]
  · -- Show that f is unique
    intro f ⟨⟨h_left, h_right⟩, _⟩
    apply prodQ.uniq coneP
    intro j
    rcases j with ⟨_ | _⟩
    · exact h_left
    · exact h_right

example {𝒞 : Type u} [Category.{v, u} 𝒞] (B₁ B₂ : 𝒞)
    (coneP coneQ : BinaryFan B₁ B₂)
    (prodP : IsLimit coneP) (prodQ : IsLimit coneQ)
    : ∃! f : coneP.pt ⟶ coneQ.pt,
        (coneQ.fst ⊚ f = coneP.fst ∧ coneQ.snd ⊚ f = coneP.snd)
        ∧ IsIso f := by
  use prodQ.lift coneP
  and_intros
  · -- Show that q₁ ⊚ f = p₁
    exact prodQ.fac coneP ⟨WalkingPair.left⟩
  · -- Show that q₂ ⊚ f = p₂
    exact prodQ.fac coneP ⟨WalkingPair.right⟩
  · -- Show that f is an isomorphism
    exact (IsLimit.nonempty_isLimit_iff_isIso_lift prodQ).mp ⟨prodP⟩
  · -- Show that f is unique
    intro f ⟨⟨h_left, h_right⟩, _⟩
    apply prodQ.uniq coneP
    intro j
    rcases j with ⟨_ | _⟩
    · exact h_left
    · exact h_right

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
        b₁ = prod.fst ⊚ p ∧ b₂ = prod.snd ⊚ p) := by
  constructor
  · intro p
    use (prod.fst ⊚ p, prod.snd ⊚ p)
    constructor
    · dsimp
      apply prod.hom_ext
      · rw [prod.lift_fst]
      · rw [prod.lift_snd]
    · intro b h
      rw [h, prod.lift_fst, prod.lift_snd, Prod.mk.eta]
  · intro b₁ b₂
    use prod.lift b₁ b₂
    and_intros
    · rw [prod.lift_fst]
    · rw [prod.lift_snd]
    · rintro p ⟨h₁, h₂⟩
      apply prod.hom_ext
      · rw [prod.lift_fst, h₁]
      · rw [prod.lift_snd, h₂]

end ExIV_13

/-!
Exercise IV.14 (p. 219)
-/
structure SetA (carrierA : Type) where
  carrier : Type
  action : carrierA × carrier ⟶ carrier

instance {carrierA : Type} : Category (SetA carrierA) where
  Hom X Y := {
    f : X.carrier ⟶ Y.carrier //
    f ⊚ X.action = Y.action ⊚ (Prod.map (𝟙 carrierA) f) -- commutes
  }
  id X := ⟨𝟙 X.carrier, rfl⟩
  comp f g := ⟨
    g.val ⊚ f.val,
    by
      obtain hf_comm := f.property
      obtain hg_comm := g.property
      rw [← Category.assoc, hf_comm, Category.assoc, hg_comm,
          ← Category.assoc]
      rfl
  ⟩

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
example {𝒞 : Type u} [Category.{v, u} 𝒞] {I : Type} (Cᵢ : I → 𝒞)
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
                       q_c ⊚ f = f_c := by
  intro X f_a f_b f_c
  obtain ⟨f_p, ⟨hf_a, hf_b⟩, h_uniqP⟩ := by exact h_prodP X f_a f_b
  obtain ⟨f, ⟨hf_p, hf_c⟩, h_uniqQ⟩ := by exact h_prodQ X f_p f_c
  use f
  and_intros
  · -- Show that p_a q f = f_a
    rw [hf_p, hf_a]
  · -- Show that p_b q f = f_b
    rw [hf_p, hf_b]
  · -- Show that q_c f = f_c
    rw [hf_c]
  · -- Show uniqueness
    intro m ⟨hm_a, hm_b, hm_c⟩
    apply h_uniqQ
    constructor
    · apply h_uniqP
      constructor
      · exact hm_a
      · exact hm_b
    · exact hm_c

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
      ) := by
  refine IsLimit.mk ?_ ?_ ?_
  · -- lift
    intro coneX
    exact prodQ.lift (Fan.mk coneX.pt (fun
      | 0 => prodP.lift (Fan.mk coneX.pt (fun
        | 0 => coneX.π.app ⟨0⟩
        | 1 => coneX.π.app ⟨1⟩))
      | 1 => coneX.π.app ⟨2⟩))
  · -- fac
    intro coneX i
    fin_cases i
    · -- Show that p_a q f = f_a
      dsimp
      rw [← Category.assoc, prodQ.fac]
      exact prodP.fac _ ⟨0⟩
    · -- Show that p_b q f = f_b
      dsimp
      rw [← Category.assoc, prodQ.fac]
      exact prodP.fac _ ⟨1⟩
    · -- Show that q_c f = f_c
      exact prodQ.fac _ ⟨1⟩
  · -- uniq
    intro coneX m hm
    refine prodQ.uniq (Fan.mk coneX.pt (fun
      | 0 => prodP.lift (Fan.mk coneX.pt (fun
              | 0 => coneX.π.app ⟨0⟩
              | 1 => coneX.π.app ⟨1⟩))
      | 1 => coneX.π.app ⟨2⟩)) m ?_
    intro i
    fin_cases i
    · refine prodP.uniq (Fan.mk coneX.pt (fun
        | 0 => coneX.π.app ⟨0⟩
        | 1 => coneX.π.app ⟨1⟩)) _ ?_
      intro i
      fin_cases i
      · rw [Category.assoc]
        exact hm ⟨0⟩
      · rw [Category.assoc]
        exact hm ⟨1⟩
    · exact hm ⟨2⟩

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
        first | rw [h₁] | rw [h₂]
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
             (∃ b₂ : Unit ⟶ B₂, j₂ ⊚ b₂ = s) := by
  intro s
  -- Construct a concrete disjoint union Y
  -- such that the left component tagged as true implies
  -- the right component contains an element of B₁
  -- and the left component tagged as false implies
  -- the right component contains an element of B₂
  let Y := (b : Bool) × (fun | true => B₁ | false => B₂) b
  -- Create the injections from B₁ and B₂ into Y
  let g₁ : B₁ ⟶ Y := fun x ↦ ⟨true, x⟩
  let g₂ : B₂ ⟶ Y := fun x ↦ ⟨false, x⟩
  -- Use the universal property to get a unique g : S ⟶ Y
  -- such that g ⊚ j₁ = g₁ and g ⊚ j₂ = g₂
  obtain ⟨g, ⟨hg₁, hg₂⟩, _⟩ := h_sum Y g₁ g₂
  -- Create a morphism f that sends the right component of Y to S
  -- via the injection j₁ (when tagged true) or j₂ (when tagged false)
  let f : Y ⟶ S := fun
    | ⟨true, val⟩ => j₁ val
    | ⟨false, val⟩ => j₂ val
  -- Show that f ⊚ g = 𝟙 S
  obtain ⟨e, _, h_uniq⟩ := h_sum S j₁ j₂
  have h_fg_e : f ⊚ g = e := by
    apply h_uniq
    and_intros
    · rw [← Category.assoc, hg₁]
      rfl
    · rw [← Category.assoc, hg₂]
      rfl
  have h_id_e : 𝟙 S = e := by
    apply h_uniq
    exact ⟨rfl, rfl⟩
  have h_fg_id : f ⊚ g = 𝟙 S := by
    rw [h_fg_e, h_id_e]
  have hfgs : f ⊚ g ⊚ s = s := by
    rw [Category.assoc, h_fg_id]
    rfl
  -- Perform case analysis on (g ⊚ s) ()
  match hgs : (g ⊚ s) () with
  | ⟨true, x₁⟩ =>
      left
      refine ⟨⟨fun _ => x₁, ?_⟩, ?_⟩
      · -- Prove existence
        funext ()
        calc j₁ x₁
         _ = f ⟨true, x₁⟩     := rfl
         _ = f ((g ⊚ s) ())  := by rw [hgs]
         _ = (f ⊚ g ⊚ s) () := by rw [types_comp_apply (g ⊚ s) f]
         _ = s ()             := by rw [hfgs]
      · -- Prove exclusivity
        rintro ⟨b₂, hb₂⟩
        have h_contra : ⟨false, b₂ ()⟩ = (⟨true, x₁⟩ : Y) :=
          calc ⟨false, b₂ ()⟩
            _ = (g₂ ⊚ b₂) ()        := rfl
            _ = ((g ⊚ j₂) ⊚ b₂) () := by rw [hg₂]
            _ = (g ⊚ j₂ ⊚ b₂) ()   := by rw [Category.assoc]
            _ = (g ⊚ s) ()          := by rw [hb₂]
            _ = ⟨true, x₁⟩           := hgs
        have : false = true := congr_arg Sigma.fst h_contra
        contradiction
  | ⟨false, x₂⟩ =>
      right
      refine ⟨⟨fun _ => x₂, ?_⟩, ?_⟩
      · -- Prove existence
        funext ()
        calc j₂ x₂
         _ = f ⟨false, x₂⟩    := rfl
         _ = f ((g ⊚ s) ())  := by rw [hgs]
         _ = (f ⊚ g ⊚ s) () := by rw [types_comp_apply (g ⊚ s) f]
         _ = s ()             := by rw [hfgs]
      · -- Prove exclusivity
        rintro ⟨b₁, hb₁⟩
        have h_contra : ⟨true, b₁ ()⟩ = (⟨false, x₂⟩ : Y) :=
          calc ⟨true, b₁ ()⟩
            _ = (g₁ ⊚ b₁) ()        := rfl
            _ = ((g ⊚ j₁) ⊚ b₁) () := by rw [hg₁]
            _ = (g ⊚ j₁ ⊚ b₁) ()   := by rw [Category.assoc]
            _ = (g ⊚ s) ()          := by rw [hb₁]
            _ = ⟨false, x₂⟩          := hgs
        have : true = false := congr_arg Sigma.fst h_contra
        contradiction

example (S B₁ B₂ : SetWithEndomap) (j₁ : B₁ ⟶ S) (j₂ : B₂ ⟶ S)
    (h_sum : ∀ (Y : SetWithEndomap) (g₁ : B₁ ⟶ Y) (g₂ : B₂ ⟶ Y),
        ∃! g : S ⟶ Y, (g ⊚ j₁ = g₁ ∧ g ⊚ j₂ = g₂))
    : ∀ s : termSWE ⟶ S,
        Xor' (∃ b₁ : termSWE ⟶ B₁, j₁ ⊚ b₁ = s)
             (∃ b₂ : termSWE ⟶ B₂, j₂ ⊚ b₂ = s) := by
  intro s
  -- Set up
  let Y : SetWithEndomap := {
    carrier := Sum B₁.carrier B₂.carrier
    toEnd := fun
      | Sum.inl b1 => Sum.inl (B₁.toEnd b1)
      | Sum.inr b2 => Sum.inr (B₂.toEnd b2)
  }
  let g₁ : B₁ ⟶ Y := ⟨Sum.inl, rfl⟩
  let g₂ : B₂ ⟶ Y := ⟨Sum.inr, rfl⟩
  obtain ⟨g, ⟨hg₁, hg₂⟩, _⟩ := h_sum Y g₁ g₂
  let f : Y ⟶ S := ⟨
    fun
      | Sum.inl b1 => j₁.val b1
      | Sum.inr b2 => j₂.val b2,
    by
      ext (b1 | b2)
      · exact congr_fun j₁.property b1
      · exact congr_fun j₂.property b2
  ⟩
  obtain ⟨e, _, h_uniq⟩ := h_sum S j₁ j₂
  have h_fg_e : f ⊚ g = e := by
    apply h_uniq
    and_intros
    · rw [← Category.assoc, hg₁]
      rfl
    · rw [← Category.assoc, hg₂]
      rfl
  have h_id_e : 𝟙 S = e := by
    apply h_uniq
    exact ⟨rfl, rfl⟩
  have h_fg_id : f ⊚ g = 𝟙 S := by
    rw [h_fg_e, h_id_e]
  have hfgs : f ⊚ g ⊚ s = s := by
    rw [Category.assoc, h_fg_id]
    rfl
  have hfgs' : (f ⊚ g ⊚ s).val () = s.val () := by
    rw [hfgs]
  -- Perform case analysis on (g ⊚ s).val ()
  match hgs : (g ⊚ s).val () with
  | Sum.inl x₁ =>
      left
      refine ⟨⟨⟨
        fun _ => x₁,
        by
          funext ()
          have hgs_comm := congr_fun (g ⊚ s).property ()
          dsimp [termSWE] at hgs_comm
          rw [hgs] at hgs_comm
          exact Sum.inl.inj hgs_comm
      ⟩, ?_⟩, ?_⟩
      · -- Prove existence
        apply Subtype.ext
        funext ()
        calc j₁.val x₁
          _ = f.val (Sum.inl x₁)      := rfl
          _ = f.val ((g ⊚ s).val ()) := by rw [hgs]
          _ = s.val ()                := hfgs'
      · -- Prove exclusivity
        rintro ⟨b₂, hb₂⟩
        have h_contra : Sum.inr (b₂.val ()) = Sum.inl x₁ :=
          calc Sum.inr (b₂.val ())
            _ = (g₂ ⊚ b₂).val ()        := rfl
            _ = ((g ⊚ j₂) ⊚ b₂).val () := by rw [hg₂]
            _ = (g ⊚ j₂ ⊚ b₂).val ()   := by rw [Category.assoc]
            _ = (g ⊚ s).val ()          := by rw [hb₂]
            _ = Sum.inl x₁               := hgs
        contradiction
  | Sum.inr x₂ =>
      right
      refine ⟨⟨⟨
        fun _ => x₂,
        by
          funext ()
          have hgs_comm := congr_fun (g ⊚ s).property ()
          dsimp [termSWE] at hgs_comm
          rw [hgs] at hgs_comm
          exact Sum.inr.inj hgs_comm
      ⟩, ?_⟩, ?_⟩
      · -- Prove existence
        apply Subtype.ext
        funext ()
        calc j₂.val x₂
          _ = f.val (Sum.inr x₂)      := rfl
          _ = f.val ((g ⊚ s).val ()) := by rw [hgs]
          _ = s.val ()                := hfgs'
      · -- Prove exclusivity
        rintro ⟨b₁, hb₁⟩
        have h_contra : Sum.inl (b₁.val ()) = Sum.inr x₂ :=
          calc Sum.inl (b₁.val ())
            _ = (g₁ ⊚ b₁).val ()        := rfl
            _ = ((g ⊚ j₁) ⊚ b₁).val () := by rw [hg₁]
            _ = (g ⊚ j₁ ⊚ b₁).val ()   := by rw [Category.assoc]
            _ = (g ⊚ s).val ()          := by rw [hb₁]
            _ = Sum.inr x₂               := hgs
        contradiction

example (S B₁ B₂ : IrreflexiveGraph) (j₁ : B₁ ⟶ S) (j₂ : B₂ ⟶ S)
    (h_sum : ∀ (Y : IrreflexiveGraph) (g₁ : B₁ ⟶ Y) (g₂ : B₂ ⟶ Y),
        ∃! g : S ⟶ Y, (g ⊚ j₁ = g₁ ∧ g ⊚ j₂ = g₂))
    : ∀ s : termIG ⟶ S,
        Xor' (∃ b₁ : termIG ⟶ B₁, j₁ ⊚ b₁ = s)
             (∃ b₂ : termIG ⟶ B₂, j₂ ⊚ b₂ = s) := by
  intro s
  -- Set up
  let Y : IrreflexiveGraph := {
    carrierA := Sum B₁.carrierA B₂.carrierA
    carrierD := Sum B₁.carrierD B₂.carrierD
    toSrc := fun
      | Sum.inl b1 => Sum.inl (B₁.toSrc b1)
      | Sum.inr b2 => Sum.inr (B₂.toSrc b2)
    toTgt := fun
      | Sum.inl b1 => Sum.inl (B₁.toTgt b1)
      | Sum.inr b2 => Sum.inr (B₂.toTgt b2)
  }
  let g₁ : B₁ ⟶ Y := ⟨⟨Sum.inl, Sum.inl⟩, ⟨rfl, rfl⟩⟩
  let g₂ : B₂ ⟶ Y := ⟨⟨Sum.inr, Sum.inr⟩, ⟨rfl, rfl⟩⟩
  obtain ⟨g, ⟨hg₁, hg₂⟩, _⟩ := h_sum Y g₁ g₂
  let f : Y ⟶ S := ⟨(
      fun
        | Sum.inl bA1 => j₁.val.1 bA1
        | Sum.inr bA2 => j₂.val.1 bA2,
      fun
        | Sum.inl bD1 => j₁.val.2 bD1
        | Sum.inr bD2 => j₂.val.2 bD2
    ),
    by
      constructor
      · ext (bA1 | bA2)
        · exact congr_fun j₁.property.1 bA1
        · exact congr_fun j₂.property.1 bA2
      · ext (bD1 | bD2)
        · exact congr_fun j₁.property.2 bD1
        · exact congr_fun j₂.property.2 bD2
  ⟩
  obtain ⟨e, _, h_uniq⟩ := h_sum S j₁ j₂
  have h_fg_e : f ⊚ g = e := by
    apply h_uniq
    and_intros
    · rw [← Category.assoc, hg₁]
      rfl
    · rw [← Category.assoc, hg₂]
      rfl
  have h_id_e : 𝟙 S = e := by
    apply h_uniq
    exact ⟨rfl, rfl⟩
  have h_fg_id : f ⊚ g = 𝟙 S := by
    rw [h_fg_e, h_id_e]
  have hfgs : f ⊚ g ⊚ s = s := by
    rw [Category.assoc, h_fg_id]
    rfl
  have hfgsA : (f ⊚ g ⊚ s).val.1 () = s.val.1 () := by
    rw [hfgs]
  have hfgsD : (f ⊚ g ⊚ s).val.2 () = s.val.2 () := by
    rw [hfgs]
  -- Perform case analysis on (g ⊚ s).val.1 (), (g ⊚ s).val.2 ()
  match hgsA : (g ⊚ s).val.1 (), hgsD : (g ⊚ s).val.2 () with
  | Sum.inl x₁A, Sum.inl x₁D =>
      left
      refine ⟨⟨⟨
        (fun _ => x₁A, fun _ => x₁D),
        by
          constructor
          · funext ()
            have hgsSrc_comm := congr_fun (g ⊚ s).property.1 ()
            dsimp [termIG] at hgsSrc_comm
            rw [hgsA, hgsD] at hgsSrc_comm
            exact Sum.inl.inj hgsSrc_comm
          · funext ()
            have hgsTgt_comm := congr_fun (g ⊚ s).property.2 ()
            dsimp [termIG] at hgsTgt_comm
            rw [hgsA, hgsD] at hgsTgt_comm
            exact Sum.inl.inj hgsTgt_comm
      ⟩, ?_⟩, ?_⟩
      · -- Prove existence
        apply Subtype.ext
        apply Prod.ext
        · funext ()
          calc j₁.val.1 x₁A
            _ = f.val.1 (Sum.inl x₁A)       := rfl
            _ = f.val.1 ((g ⊚ s).val.1 ()) := by rw [hgsA]
            _ = s.val.1 ()                  := hfgsA
        · funext ()
          calc j₁.val.2 x₁D
            _ = f.val.2 (Sum.inl x₁D)       := rfl
            _ = f.val.2 ((g ⊚ s).val.2 ()) := by rw [hgsD]
            _ = s.val.2 ()                  := hfgsD
      · -- Prove exclusivity
        rintro ⟨b₂, hb₂⟩
        have h_contra : Sum.inr (b₂.val.1 ()) = Sum.inl x₁A :=
          calc Sum.inr (b₂.val.1 ())
            _ = (g₂ ⊚ b₂).val.1 ()        := rfl
            _ = ((g ⊚ j₂) ⊚ b₂).val.1 () := by rw [hg₂]
            _ = (g ⊚ j₂ ⊚ b₂).val.1 ()   := by rw [Category.assoc]
            _ = (g ⊚ s).val.1 ()          := by rw [hb₂]
            _ = Sum.inl x₁A                := hgsA
        contradiction
  | Sum.inr x₂A, Sum.inr x₂D =>
      right
      refine ⟨⟨⟨
        (fun _ => x₂A, fun _ => x₂D),
        by
          constructor
          · funext ()
            have hgsSrc_comm := congr_fun (g ⊚ s).property.1 ()
            dsimp [termIG] at hgsSrc_comm
            rw [hgsA, hgsD] at hgsSrc_comm
            exact Sum.inr.inj hgsSrc_comm
          · funext ()
            have hgsTgt_comm := congr_fun (g ⊚ s).property.2 ()
            dsimp [termIG] at hgsTgt_comm
            rw [hgsA, hgsD] at hgsTgt_comm
            exact Sum.inr.inj hgsTgt_comm
      ⟩, ?_⟩, ?_⟩
      · -- Prove existence
        apply Subtype.ext
        apply Prod.ext
        · funext ()
          calc j₂.val.1 x₂A
            _ = f.val.1 (Sum.inr x₂A)       := rfl
            _ = f.val.1 ((g ⊚ s).val.1 ()) := by rw [hgsA]
            _ = s.val.1 ()                  := hfgsA
        · funext ()
          calc j₂.val.2 x₂D
            _ = f.val.2 (Sum.inr x₂D)       := rfl
            _ = f.val.2 ((g ⊚ s).val.2 ()) := by rw [hgsD]
            _ = s.val.2 ()                  := hfgsD
      · -- Prove exclusivity
        rintro ⟨b₁, hb₁⟩
        have h_contra : Sum.inl (b₁.val.1 ()) = Sum.inr x₂A :=
          calc Sum.inl (b₁.val.1 ())
            _ = (g₁ ⊚ b₁).val.1 ()        := rfl
            _ = ((g ⊚ j₁) ⊚ b₁).val.1 () := by rw [hg₁]
            _ = (g ⊚ j₁ ⊚ b₁).val.1 ()   := by rw [Category.assoc]
            _ = (g ⊚ s).val.1 ()          := by rw [hb₁]
            _ = Sum.inr x₂A                := hgsA
        contradiction
  -- Handle unreachable cases
  | Sum.inl xA, Sum.inr xD =>
      have h_contra := congr_fun (g ⊚ s).property.1 ()
      dsimp [termIG] at h_contra
      rw [hgsA, hgsD] at h_contra
      contradiction
  | Sum.inr xA, Sum.inl xD =>
      have h_contra := congr_fun (g ⊚ s).property.1 ()
      dsimp [termIG] at h_contra
      rw [hgsA, hgsD] at h_contra
      contradiction

/-!
Exercise IV.18 (p. 222)
-/
namespace ExIV_18

abbrev X := Fin 2

def f₁ : X ⟶ Unit := fun _ ↦ ()
def j₁ : Unit ⟶ Unit ⊕ Unit := fun _ ↦ Sum.inl ()
def f₂ : X ⟶ Unit := fun _ ↦ ()
def j₂ : Unit ⟶ Unit ⊕ Unit := fun _ ↦ Sum.inr ()

def f : X ⟶ Unit ⊕ Unit
  | 0 => Sum.inl ()
  | 1 => Sum.inr ()

example : ∃ f' : X ⟶ Unit ⊕ Unit,
    f' ≠ j₁ ⊚ f₁ ∧ f' ≠ j₂ ⊚ f₂ := by
  use f
  constructor
  · intro h
    have h_contra : Sum.inr () = Sum.inl () :=
      calc Sum.inr ()
        _ = f 1          := rfl
        _ = (j₁ ⊚ f₁) 1 := by rw [h]
        _ = (j₁ ⊚ f₁) 0 := rfl
        _ = f 0          := rfl
        _ = Sum.inl ()   := rfl
    contradiction
  · intro h
    have h_contra : Sum.inl () = Sum.inr () :=
      calc Sum.inl ()
        _ = f 0          := rfl
        _ = (j₂ ⊚ f₂) 0 := by rw [h]
        _ = (j₂ ⊚ f₂) 1 := rfl
        _ = f 1          := rfl
        _ = Sum.inr ()   := rfl
    contradiction

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
    AB_C ≅ A_BC := by
  -- get p : AB ⟶ A_BC from the universal property of AB
  have hp := hAB A_BC k₃ (k₄ ⊚ k₁)
  obtain ⟨⟨hp₁, hp₂⟩, _⟩ := hp.choose_spec
  set p : AB ⟶ A_BC := hp.choose
  -- get q : BC ⟶ AB_C from the universal property of BC
  have hq := hBC AB_C (j₃ ⊚ j₂) j₄
  obtain ⟨⟨hq₁, hq₂⟩, _⟩ := hq.choose_spec
  set q : BC ⟶ AB_C := hq.choose
  -- get f : AB_C ⟶ A_BC from the universal property of AB_C
  have hf := hAB_C A_BC p (k₄ ⊚ k₂)
  obtain ⟨⟨hf₁, hf₂⟩, _⟩ := hf.choose_spec
  set f : AB_C ⟶ A_BC := hf.choose
  -- get g : A_BC ⟶ AB_C from the universal property of A_BC
  have hg := hA_BC AB_C (j₃ ⊚ j₁) q
  obtain ⟨⟨hg₁, hg₂⟩, _⟩ := hg.choose_spec
  set g : A_BC ⟶ AB_C := hg.choose
  -- Show that g ⊚ f = 𝟙 AB_C
  have hgf : g ⊚ f = 𝟙 AB_C := by
    apply ExistsUnique.unique (hAB_C AB_C j₃ j₄)
    · constructor
      · rw [← Category.assoc, hf₁]
        apply ExistsUnique.unique (hAB AB_C (j₃ ⊚ j₁) (j₃ ⊚ j₂))
        · constructor
          · rw [← Category.assoc, hp₁, hg₁]
          · rw [← Category.assoc, hp₂, Category.assoc, hg₂, hq₁]
        · exact ⟨rfl, rfl⟩
      · rw [← Category.assoc, hf₂, Category.assoc, hg₂, hq₂]
    · exact ⟨Category.comp_id j₃, Category.comp_id j₄⟩
  -- Show that f ⊚ g = 𝟙 A_BC
  have hfg : f ⊚ g = 𝟙 A_BC := by
    apply ExistsUnique.unique (hA_BC A_BC k₃ k₄)
    · constructor
      · rw [← Category.assoc, hg₁, Category.assoc, hf₁, hp₁]
      · rw [← Category.assoc, hg₂]
        apply ExistsUnique.unique (hBC A_BC (k₄ ⊚ k₁) (k₄ ⊚ k₂))
        · constructor
          · rw [← Category.assoc, hq₁, Category.assoc, hf₁, hp₂]
          · rw [← Category.assoc, hq₂, hf₂]
        · exact ⟨rfl, rfl⟩
    · exact ⟨Category.comp_id k₃, Category.comp_id k₄⟩
  -- Create the isomorphism structure
  exact {
    hom := f
    inv := g
    hom_inv_id := hgf
    inv_hom_id := hfg
  }

noncomputable example {𝒞 : Type u} [Category.{v, u} 𝒞]
    [HasBinaryCoproducts 𝒞] (A B C : 𝒞) :
    (A ⨿ B) ⨿ C ≅ A ⨿ (B ⨿ C) :=
  coprod.associator A B C

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

example : ¬ DistributiveLaw PointedSet := by
  intro h_distrib
  -- Define a helper to prove the universal property for the products
  let h_univ_prod : ∀ (X : PointedSet) (f₁ : X ⟶ A) (f₂ : X ⟶ B),
      ∃! f, p₁ ⊚ f = f₁ ∧ p₂ ⊚ f = f₂ := by
      intro X f₁ f₂
      -- Provide the witness
      use ⟨fun x ↦ (f₁.val x, f₂.val x), by
        ext
        dsimp
        rw [← types_comp_apply _ f₁.val, f₁.property]; rfl
      ⟩
      constructor
      · -- Verify the diagram commutes
        constructor <;> rfl
      · -- Prove uniqueness
        intro f ⟨hf₁, hf₂⟩
        apply Subtype.ext
        rw [← hf₁]; rfl
  have h_iso := h_distrib A B C AxB AxC AxB_AxC B_C AxB_C
                          p₁ p₂ p₃ p₄ j₁ j₂ j₃ j₄ p₅ p₆
    -- Prove the universal property for AxB
    h_univ_prod
    -- Prove the universal property for AxC
    h_univ_prod
    -- Prove the universal property for AxB_AxC
    (by
      intro Y g₁ g₂
      -- Provide the witness
      use ⟨fun
        | Sum.inl (0, ()) => Y.point ()
        | Sum.inl (1, ()) => g₁.val (1, ())
        | Sum.inr _       => g₂.val (1, ()),
        rfl
      ⟩
      constructor
      · -- Verify the diagram commutes
        constructor
        all_goals
          apply Subtype.ext
          funext x
          match x with
          | (0, _) => first | exact (congr_fun g₁.property ()).symm
                            | exact (congr_fun g₂.property ()).symm
          | (1, _) => rfl
      · -- Prove uniqueness
        intro g ⟨hg₁, hg₂⟩
        apply Subtype.ext
        funext x
        match x with
        | Sum.inl (0, _) => exact (congr_fun g.property ())
        | Sum.inl (1, _) => rw [← hg₁]; rfl
        | Sum.inr _ => rw [← hg₂]; rfl
    )
    -- Prove the universal property for B_C
    (by
      intro Y g₁ g₂
      -- Provide the witness
      use ⟨fun _ ↦ Y.point (), rfl⟩
      constructor
      · -- Verify the diagram commutes
        constructor
        all_goals
          apply Subtype.ext
          funext
          first | exact (congr_fun g₁.property ()).symm
                | exact (congr_fun g₂.property ()).symm
      · -- Prove uniqueness
        intro g ⟨_, _⟩
        apply Subtype.ext
        funext x
        exact (congr_fun g.property ())
    )
    -- Prove the universal property for AxB_C
    h_univ_prod
  obtain ⟨iso⟩ := h_iso
  have h_equiv : AxB_AxC.carrier ≃ AxB_C.carrier := {
    toFun := iso.hom.val
    invFun := iso.inv.val
    left_inv := congrArg Subtype.val iso.hom_inv_id |> congrFun
    right_inv := congrArg Subtype.val iso.inv_hom_id |> congrFun
  }
  exact absurd (Fintype.card_congr h_equiv) (by decide)

end ExIV_20

/-!
Exercise IV.21 (p. 223)
-/
open IrreflexiveGraph
example
    (coneAA : BinaryFan A A)
    (limitAA : IsLimit coneAA)
    (coconeADD : Cofan (fun | 0 => A | 1 => D | 2 => D :
        Fin 3 → IrreflexiveGraph))
    (colimitADD : IsColimit coconeADD) :
  coneAA.pt ≅ coconeADD.pt := by
    -- Improve readability
    set AA : IrreflexiveGraph := coneAA.pt with hAA
    set ADD : IrreflexiveGraph := coconeADD.pt with hADD
    set p₁ := coneAA.π.app ⟨WalkingPair.left⟩ with hp₁ -- A ⟶ 𝐀×A
    set p₂ := coneAA.π.app ⟨WalkingPair.right⟩ with hp₂ -- A ⟶ A×𝐀
    set j₁ := coconeADD.ι.app ⟨0⟩ with hj₁ -- A ⟶ 𝐀+D+D
    set j₂ := coconeADD.ι.app ⟨1⟩ with hj₂ -- D ⟶ A+𝐃+D
    set j₃ := coconeADD.ι.app ⟨2⟩ with hj₃ -- D ⟶ A+D+𝐃
    dsimp at p₁ p₂ j₁ j₂ j₃
    let d₀ : Fin 2 := 0 -- first dot of A
    let d₁ : Fin 2 := 1 -- second dot of A
    -- Construct morphism f : A×A ⟶ A+D+D
    let f : AA ⟶ ADD :=
      let fA : AA.carrierA ⟶ ADD.carrierA := fun _ ↦ j₁.val.1 ()
      let fD : AA.carrierD ⟶ ADD.carrierD := fun x ↦
        match ((p₁.val.2 x, p₂.val.2 x) : Fin 2 × Fin 2) with
        | (0, 0) => j₁.val.2 d₀
        | (0, 1) => j₂.val.2 ()
        | (1, 0) => j₃.val.2 ()
        | (1, 1) => j₁.val.2 d₁
      ⟨(fA, fD), by
        constructor
        · -- Show that source commutes
          funext x
          dsimp [fA, fD]
          -- lhs (fD ⊚ AA.toSrc = j₁.val.2)
          have hl₁ : p₁.val.2 (AA.toSrc x) = d₀ :=
            congr_fun p₁.property.1 x
          have hl₂ : p₂.val.2 (AA.toSrc x) = d₀ :=
            congr_fun p₂.property.1 x
          -- rhs (j₁.val.2 = ADD.toSrc ⊚ fA)
          have hr : j₁.val.2 d₀ = ADD.toSrc (j₁.val.1 ()) :=
            congr_fun j₁.property.1 ()
          rw [hl₁, hl₂, hr]
        · -- Show that target commutes
          funext x
          dsimp [fA, fD]
          -- lhs (fD ⊚ AA.toTgt = j₁.val.2)
          have hl₁ : p₁.val.2 (AA.toTgt x) = d₁ :=
            congr_fun p₁.property.2 x
          have hl₂ : p₂.val.2 (AA.toTgt x) = d₁ :=
            congr_fun p₂.property.2 x
          -- rhs (j₁.val.2 = ADD.toTgt ⊚ fA)
          have hr : j₁.val.2 d₁ = ADD.toTgt (j₁.val.1 ()) :=
            congr_fun j₁.property.2 ()
          rw [hl₁, hl₂, hr]⟩
    -- Construct s which maps unique dot of D to first dot of A
    let s : D ⟶ A := ⟨
      (Empty.elim, fun _ ↦ d₀), ⟨rfl, funext fun e ↦ Empty.elim e⟩
    ⟩
    -- Construct t which maps unique dot of D to second dot of A
    let t : D ⟶ A := ⟨
      (Empty.elim, fun _ ↦ d₁), ⟨funext fun e ↦ Empty.elim e, rfl⟩
    ⟩
    -- Construct cocone over A, D, D with vertex A×A
    let coconeAA : Cofan (fun | 0 => A | 1 => D | 2 => D :
        Fin 3 → IrreflexiveGraph) :=
      Cofan.mk coneAA.pt (fun
        | 0 => limitAA.lift (BinaryFan.mk (𝟙 A) (𝟙 A))
        | 1 => limitAA.lift (BinaryFan.mk s t)
        | 2 => limitAA.lift (BinaryFan.mk t s))
    -- Construct morphism f⁻¹ : A+D+D ⟶ A×A
    let finv : ADD ⟶ AA := colimitADD.desc coconeAA
    exact {
      hom := f
      inv := finv
      hom_inv_id := by
        apply BinaryFan.IsLimit.hom_ext limitAA
        · -- Show that p₁ ⊚ finv ⊚ f = p₁ ⊚ 𝟙 AA
          apply IrreflexiveGraph.hom_ext
          · -- Case fA (morphisms for arrows)
            rfl
          · -- Case fD (morphisms for dots)
            funext x
            change (p₁ ⊚ finv).val.2 (f.val.2 x) = p₁.val.2 x
            dsimp [f]
            generalize p₁.val.2 x = x₁, p₂.val.2 x = x₂
            change Fin 2 at x₁ x₂
            fin_cases x₁ <;> fin_cases x₂
            · change (p₁ ⊚ finv ⊚ j₁).val.2 d₀ = d₀
              erw [colimitADD.fac coconeAA ⟨0⟩,
                   limitAA.fac _ ⟨WalkingPair.left⟩]; rfl
            · change (p₁ ⊚ finv ⊚ j₂).val.2 () = d₀
              erw [colimitADD.fac coconeAA ⟨1⟩,
                   limitAA.fac _ ⟨WalkingPair.left⟩]; rfl
            · change (p₁ ⊚ finv ⊚ j₃).val.2 () = d₁
              erw [colimitADD.fac coconeAA ⟨2⟩,
                   limitAA.fac _ ⟨WalkingPair.left⟩]; rfl
            · change (p₁ ⊚ finv ⊚ j₁).val.2 d₁ = d₁
              erw [colimitADD.fac coconeAA ⟨0⟩,
                   limitAA.fac _ ⟨WalkingPair.left⟩]; rfl
        · -- Show that p₂ ⊚ finv ⊚ f = p₂ ⊚ 𝟙 AA
          apply IrreflexiveGraph.hom_ext
          · -- Case fA (morphisms for arrows)
            rfl
          · -- Case fD (morphisms for dots)
            funext x
            change (p₂ ⊚ finv).val.2 (f.val.2 x) = p₂.val.2 x
            dsimp [f]
            generalize p₁.val.2 x = x₁, p₂.val.2 x = x₂
            change Fin 2 at x₁ x₂
            fin_cases x₁ <;> fin_cases x₂
            · change (p₂ ⊚ finv ⊚ j₁).val.2 d₀ = d₀
              erw [colimitADD.fac coconeAA ⟨0⟩,
                   limitAA.fac _ ⟨WalkingPair.right⟩]; rfl
            · change (p₂ ⊚ finv ⊚ j₂).val.2 () = d₁
              erw [colimitADD.fac coconeAA ⟨1⟩,
                   limitAA.fac _ ⟨WalkingPair.right⟩]; rfl
            · change (p₂ ⊚ finv ⊚ j₃).val.2 () = d₀
              erw [colimitADD.fac coconeAA ⟨2⟩,
                   limitAA.fac _ ⟨WalkingPair.right⟩]; rfl
            · change (p₂ ⊚ finv ⊚ j₁).val.2 d₁ = d₁
              erw [colimitADD.fac coconeAA ⟨0⟩,
                   limitAA.fac _ ⟨WalkingPair.right⟩]; rfl
      inv_hom_id := by
        apply colimitADD.hom_ext
        rintro ⟨j⟩
        fin_cases j
        · -- Show that f ⊚ finv ⊚ j₁ = 𝟙 ADD ⊚ j₁
          apply IrreflexiveGraph.hom_ext
          · -- Case fA (morphisms for arrows)
            rfl
          · -- Case fD (morphisms for dots)
            funext x
            change f.val.2 ((finv ⊚ j₁).val.2 x) = j₁.val.2 x
            dsimp [f]
            change Fin 2 at x
            have h₁ : (p₁ ⊚ finv ⊚ j₁).val.2 x = x := by
              erw [colimitADD.fac coconeAA ⟨0⟩,
                   limitAA.fac _ ⟨WalkingPair.left⟩]; rfl
            have h₂ : (p₂ ⊚ finv ⊚ j₁).val.2 x = x := by
              erw [colimitADD.fac coconeAA ⟨0⟩,
                   limitAA.fac _ ⟨WalkingPair.right⟩]; rfl
            erw [h₁, h₂]
            fin_cases x <;> rfl
        · -- Show that f ⊚ finv ⊚ j₂ = 𝟙 ADD ⊚ j₂
          apply IrreflexiveGraph.hom_ext
          · -- Case fA (morphisms for arrows)
            exact funext fun e ↦ Empty.elim e
          · -- Case fD (morphisms for dots)
            funext x
            change f.val.2 ((finv ⊚ j₂).val.2 x) = j₂.val.2 x
            dsimp [f]
            have h₁ : (p₁ ⊚ finv ⊚ j₂).val.2 x = d₀ := by
              erw [colimitADD.fac coconeAA ⟨1⟩,
                   limitAA.fac _ ⟨WalkingPair.left⟩]; rfl
            have h₂ : (p₂ ⊚ finv ⊚ j₂).val.2 x = d₁ := by
              erw [colimitADD.fac coconeAA ⟨1⟩,
                   limitAA.fac _ ⟨WalkingPair.right⟩]; rfl
            erw [h₁, h₂]; rfl
        · -- Show that f ⊚ finv ⊚ j₃ = 𝟙 ADD ⊚ j₃
          apply IrreflexiveGraph.hom_ext
          · -- Case fA (morphisms for arrows)
            exact funext fun e ↦ Empty.elim e
          · -- Case fD (morphisms for dots)
            funext x
            change f.val.2 ((finv ⊚ j₃).val.2 x) = j₃.val.2 x
            dsimp [f]
            have h₁ : (p₁ ⊚ finv ⊚ j₃).val.2 x = d₁ := by
              erw [colimitADD.fac coconeAA ⟨2⟩,
                   limitAA.fac _ ⟨WalkingPair.left⟩]; rfl
            have h₂ : (p₂ ⊚ finv ⊚ j₃).val.2 x = d₀ := by
              erw [colimitADD.fac coconeAA ⟨2⟩,
                   limitAA.fac _ ⟨WalkingPair.right⟩]; rfl
            erw [h₁, h₂]; rfl
    }

end CM


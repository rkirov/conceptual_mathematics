import ConceptualMathematics.Sorried.Article2
import ConceptualMathematics.Sorried.Review
import Mathlib
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
    : (g ⊚ f) ⊚ α = γ ⊚ (g ⊚ f) :=
  sorry

example {X Y Z : SetWithEndomap} (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ Z :=
  sorry

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

/-!
Exercise III.2 (p. 139)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] {A : 𝒞} {α β : A ⟶ A}
    (h_idem : α ⊚ α = α) (h_retraction : β ⊚ α = 𝟙 A)
    : α = 𝟙 A :=
  sorry

/-!
Exercise III.3 (p. 140)
-/
/-!
Exercise III.4 (p. 140)
-/
namespace ExIII_4

def α : ℤ ⟶ ℤ := fun x ↦ -x

example : ¬(IsIdempotent α) :=
  sorry

example : IsInvolution α :=
  sorry

example {x : ℤ} : Function.IsFixedPt α x ↔ x = 0 :=
  sorry

end ExIII_4

/-!
Exercise III.5 (p. 140)
-/
namespace ExIII_5

def α : ℤ ⟶ ℤ := fun x ↦ |x|

example : IsIdempotent α :=
  sorry

example : ¬(IsInvolution α) :=
  sorry

example {x : ℤ} : Function.IsFixedPt α x ↔ 0 ≤ x :=
  sorry

end ExIII_5

/-!
Exercise III.6 (p. 140)
-/
namespace ExIII_6

def α : ℤ ⟶ ℤ := fun x ↦ x + 3

example : IsIso α :=
  sorry

end ExIII_6

/-!
Exercise III.7 (p. 140)
-/
namespace ExIII_7

def α : ℤ ⟶ ℤ := fun x ↦ 5 * x

example : ¬(IsIso α) :=
  sorry

end ExIII_7

/-!
Exercise III.8 (p. 140)
-/
example {α : IdemEndomap}
    : α.toEnd ⊚ α.toEnd ⊚ α.toEnd = α.toEnd :=
  sorry

example {𝒞 : Type u} [Category.{v, u} 𝒞] {A : 𝒞}
    (α : A ⟶ A) [IsIdempotent α] : α ⊚ α ⊚ α = α :=
  sorry

example {α : InvolEndomap}
    : α.toEnd ⊚ α.toEnd ⊚ α.toEnd = α.toEnd :=
  sorry

example {𝒞 : Type u} [Category.{v, u} 𝒞] {A : 𝒞}
    (α : A ⟶ A) [IsInvolution α] : α ⊚ α ⊚ α = α :=
  sorry

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

example : α ⊚ α ⊚ α = α :=
  sorry

example : ¬(IsIdempotent α) :=
  sorry

example : ¬(IsInvolution α) :=
  sorry

end ExIII_9

/-!
Exercise III.10 (p. 141)
-/
namespace ExIII_10

inductive X
  | a | b | c | d | e

inductive P
  | k | m | n | p | q | r

def s : X ⟶ P :=
  sorry

def t : X ⟶ P :=
  sorry

example : s X.b = t X.b :=
  sorry

example : ¬(∃ x : X, t x = P.k) :=
  sorry

end ExIII_10

/-!
The category 𝑺⇊ of (irreflexive directed multi-) graphs (pp. 141–142)
-/
structure IrreflexiveGraph where
  carrierA : Type
  carrierD : Type
  toSrc : carrierA ⟶ carrierD
  toTgt : carrierA ⟶ carrierD

instance instCategoryIrreflexiveGraph : Category IrreflexiveGraph where
  Hom X Y := {
    f : (X.carrierA ⟶ Y.carrierA) × (X.carrierD ⟶ Y.carrierD) //
        f.2 ⊚ X.toSrc = Y.toSrc ⊚ f.1 -- source commutes
        ∧ f.2 ⊚ X.toTgt = Y.toTgt ⊚ f.1 -- target commutes
  }
  id X := ⟨(𝟙 X.carrierA, 𝟙 X.carrierD), ⟨rfl, rfl⟩⟩
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

variable (X P Y Q Z R : Type)
         (s t : X ⟶ P) (s' t' : Y ⟶ Q) (s'' t'' : Z ⟶ R)

example (fA : X ⟶ Y) (fD : P ⟶ Q) (gA : Y ⟶ Z) (gD : Q ⟶ R)
    (hfSrc_comm : fD ⊚ s = s' ⊚ fA)
    (hfTgt_comm : fD ⊚ t = t' ⊚ fA)
    (hgSrc_comm : gD ⊚ s' = s'' ⊚ gA)
    (hgTgt_comm : gD ⊚ t' = t'' ⊚ gA)
    : (gD ⊚ fD) ⊚ s = s'' ⊚ (gA ⊚ fA)
        ∧ (gD ⊚ fD) ⊚ t = t'' ⊚ (gA ⊚ fA)
    :=
  sorry

def graph (A D : Type) (src tgt : A ⟶ D) : IrreflexiveGraph := {
  carrierA := A
  carrierD := D
  toSrc := src
  toTgt := tgt
}

example (f : graph X P s t ⟶ graph Y Q s' t')
    (g : graph Y Q s' t' ⟶ graph Z R s'' t'')
    : graph X P s t ⟶ graph Z R s'' t'' :=
  sorry

end ExIII_11

/-!
Exercise III.12 (p. 143)
-/
def functorSetWithEndomapToIrreflexiveGraph
    : Functor SetWithEndomap IrreflexiveGraph := {
  obj (X : SetWithEndomap) := {
    carrierA := X.carrier
    carrierD := X.carrier
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
def I {X Y : SetWithEndomap} (f : X ⟶ Y) :=
  functorSetWithEndomapToIrreflexiveGraph.map f

example {X Y Z : SetWithEndomap}
    (f : X ⟶ Y) (g : Y ⟶ Z) : I (g ⊚ f) = I g ⊚ I f := rfl

/-!
Exercise III.13 (p. 144)
-/
namespace ExIII_13

variable (X' Y' : SetWithEndomap)

def graph₁ (S : SetWithEndomap) : IrreflexiveGraph := {
  carrierA := S.carrier
  carrierD := S.carrier
  toSrc := 𝟙 S.carrier
  toTgt := S.toEnd
}

variable (f₁ : graph₁ X' ⟶ graph₁ Y')

-- Align to the notation in the book: fA is f₁.val.1, fD is f₁.val.2
set_option quotPrecheck false
local notation "fA₁" => f₁.val.1
local notation "fD₁" => f₁.val.2
set_option quotPrecheck true

example : fA₁ = fD₁ :=
  sorry

def graph₂ (S : SetWithEndomap) : IrreflexiveGraph :=
  functorSetWithEndomapToIrreflexiveGraph.obj S

variable (f₂ : graph₂ X' ⟶ graph₂ Y')

set_option quotPrecheck false
local notation "fA₂" => f₂.val.1
local notation "fD₂" => f₂.val.2
set_option quotPrecheck true

example : fA₂ = fD₂ :=
  sorry

end ExIII_13

/-!
The category 𝑺↓ of simple directed graphs (pp. 144–145)
-/
structure SimpleGraph where
  carrierA : Type
  carrierD : Type
  toFun : carrierA ⟶ carrierD

instance : Category SimpleGraph where
  Hom X Y := {
    f : (X.carrierA ⟶ Y.carrierA) × (X.carrierD ⟶ Y.carrierD) //
        f.2 ⊚ X.toFun = Y.toFun ⊚ f.1 -- commutes
  }
  id X := ⟨(𝟙 X.carrierA, 𝟙 X.carrierD), rfl⟩
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

def functorSetWithEndomapToSimpleGraph
    : Functor SetWithEndomap SimpleGraph := {
  obj (X : SetWithEndomap) := {
    carrierA := X.carrier
    carrierD := X.carrier
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
def J {X Y : SetWithEndomap} (f : X ⟶ Y) :=
  functorSetWithEndomapToSimpleGraph.map f

example {X Y Z : SetWithEndomap}
    (f : X ⟶ Y) (g : Y ⟶ Z) : J (g ⊚ f) = J g ⊚ J f := rfl

/-!
Exercise III.14 (p. 144)
-/
namespace ExIII_14

inductive X
  | x₁ | x₂

inductive Y
  | y₁ | y₂

def α : X ⟶ X :=
  sorry

def β : Y ⟶ Y :=
  sorry

def fA : X ⟶ Y :=
  sorry

def fD : X ⟶ Y :=
  sorry

example : fD ⊚ α = β ⊚ fA ∧ fA ≠ fD :=
  sorry

end ExIII_14

/-!
The category of reflexive graphs (p. 145)
-/
structure ReflexiveGraph extends IrreflexiveGraph where
  toCommonSection : carrierD ⟶ carrierA
  section_src : toSrc ⊚ toCommonSection = 𝟙 carrierD
  section_tgt : toTgt ⊚ toCommonSection = 𝟙 carrierD

instance : Category ReflexiveGraph where
  Hom X Y := {
    f : (X.carrierA ⟶ Y.carrierA) × (X.carrierD ⟶ Y.carrierD) //
        f.2 ⊚ X.toSrc = Y.toSrc ⊚ f.1 -- source commutes
        ∧ f.2 ⊚ X.toTgt = Y.toTgt ⊚ f.1 -- target commutes
        ∧ f.1 ⊚ X.toCommonSection = Y.toCommonSection ⊚ f.2
  }
  id X := ⟨
    (𝟙 X.carrierA, 𝟙 X.carrierD),
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

variable (X : ReflexiveGraph)

variable (e₁ e₀ : X.carrierA ⟶ X.carrierA)
         (h₁ : e₁ = X.toCommonSection ⊚ X.toSrc)
         (h₀ : e₀ = X.toCommonSection ⊚ X.toTgt)

example : e₀ ⊚ e₀ = e₀ :=
  sorry

example : e₀ ⊚ e₁ = e₁ :=
  sorry

example : e₁ ⊚ e₀ = e₀ :=
  sorry

example : e₁ ⊚ e₁ = e₁ :=
  sorry

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
local notation "i" => X.toCommonSection
local notation "i'" => Y.toCommonSection

example : fD = s' ⊚ fA ⊚ i :=
  sorry

example : fD = t' ⊚ fA ⊚ i :=
  sorry

end ExIII_16

/-!
Exercise III.17 (p. 145)
-/
namespace ExIII_17

structure ParentLike where
  carrierM : Type
  carrierF : Type
  φ : carrierM ⟶ carrierM
  φ' : carrierF ⟶ carrierM
  μ : carrierF ⟶ carrierF
  μ' : carrierM ⟶ carrierF

def ParentLikeHom (X Y : ParentLike) : Type :=
  sorry

instance : Category ParentLike where
  Hom := ParentLikeHom -- our map between ParentLike structures
  id X :=
    sorry
  comp :=
    sorry

end ExIII_17

/-!
Exercise III.18 (p. 146)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] {X Y T : 𝒞}
    {a : X ⟶ Y} {p : Y ⟶ X} {x₁ x₂ : T ⟶ X}
    (h₁ : p ⊚ a = 𝟙 X) (h₂ : a ⊚ x₁ = a ⊚ x₂)
    : x₁ = x₂ :=
  sorry

namespace ExIII_19_24

inductive X
  | x₀ | x₁
  deriving Fintype

inductive Y
  | y₀ | y₁ | y₂
  deriving Fintype

def α : X ⟶ X
  | X.x₀ => X.x₀
  | X.x₁ => X.x₀

def β : Y ⟶ Y
  | Y.y₀ => Y.y₀
  | Y.y₁ => Y.y₀
  | Y.y₂ => Y.y₁

def a : X ⟶ Y
  | X.x₀ => Y.y₀
  | X.x₁ => Y.y₁

/-!
Exercise III.19 (p. 147)
-/
example : a ⊚ α = β ⊚ a :=
  sorry

def Xα : SetWithEndomap :=
  sorry

def Yβ : SetWithEndomap :=
  sorry

def a' : Xα ⟶ Yβ :=
  sorry

/-!
Exercise III.20 (p. 147)
-/
example : ∀ {T : Type} (x₁ x₂ : T ⟶ X),
    a ⊚ x₁ = a ⊚ x₂ → x₁ = x₂ :=
  sorry

/-!
Exercise III.21 (p. 147)
-/
def p₁ : Y ⟶ X
  | Y.y₀ => X.x₀
  | Y.y₁ => X.x₁
  | Y.y₂ => X.x₁

example : p₁ ⊚ a = 𝟙 X := by
  funext x
  cases x <;> rfl

#eval Danilo's_formula (Finset.univ) (Finset.univ) a p₁
  (by
    funext x
    fin_cases x <;> rfl)
  (by
    intro x y _
    fin_cases x <;> fin_cases y
    all_goals
      first | rfl
            | simp only [reduceCtorEq]; trivial)

def p₂ : Y ⟶ X :=
  sorry

example : p₂ ⊚ a = 𝟙 X :=
  sorry

/-!
Exercise III.22 (p. 147)
-/
example : ¬(p₁ ⊚ β = α ⊚ p₁) :=
  sorry

example : ¬(p₂ ⊚ β = α ⊚ p₂) :=
  sorry

/-!
Exercise III.23 (p. 147)
-/
def b₁ : Y ⟶ X
  | Y.y₀ => X.x₀
  | Y.y₁ => X.x₀
  | Y.y₂ => X.x₀

example : b₁ ⊚ β = α ⊚ b₁ :=
  sorry

def b₂ : Y ⟶ X
  | Y.y₀ => X.x₀
  | Y.y₁ => X.x₀
  | Y.y₂ => X.x₁

example : b₂ ⊚ β = α ⊚ b₂ :=
  sorry

def b₃ : Y ⟶ X
  | Y.y₀ => X.x₁
  | Y.y₁ => X.x₀
  | Y.y₂ => X.x₀

example : b₃ ⊚ β ≠ α ⊚ b₃ :=
  sorry

def b₄ : Y ⟶ X
  | Y.y₀ => X.x₁
  | Y.y₁ => X.x₀
  | Y.y₂ => X.x₁

example : b₄ ⊚ β ≠ α ⊚ b₄ :=
  sorry

def b₅ : Y ⟶ X
  | Y.y₀ => X.x₀
  | Y.y₁ => X.x₁
  | Y.y₂ => X.x₀

example : b₅ ⊚ β ≠ α ⊚ b₅ :=
  sorry

def b₆ : Y ⟶ X
  | Y.y₀ => X.x₀
  | Y.y₁ => X.x₁
  | Y.y₂ => X.x₁

example : b₆ ⊚ β ≠ α ⊚ b₆ :=
  sorry

def b₇ : Y ⟶ X
  | Y.y₀ => X.x₁
  | Y.y₁ => X.x₁
  | Y.y₂ => X.x₀

example : b₇ ⊚ β ≠ α ⊚ b₇ :=
  sorry

def b₈ : Y ⟶ X
  | Y.y₀ => X.x₁
  | Y.y₁ => X.x₁
  | Y.y₂ => X.x₁

example : b₈ ⊚ β ≠ α ⊚ b₈ :=
  sorry

/-!
Exercise III.24 (p. 147)
-/
def X' : SimpleGraph := {
  carrierA := X
  carrierD := X
  toFun := α
}

def Y' : SimpleGraph := {
  carrierA := Y
  carrierD := Y
  toFun := β
}

def a'' : X' ⟶ Y' := ⟨
  (a, a),
  by
    funext x
    cases x <;> rfl
⟩

example : ¬(∃ p : Y' ⟶ X', p ⊚ a'' = 𝟙 X') :=
  sorry

example : ¬(∃ p : Yβ ⟶ Xα, J p ⊚ J a' = J (𝟙 Xα)) :=
  sorry

end ExIII_19_24

/-!
Exercise III.25 (p. 148)
-/
namespace ExIII_25

example {X P Y Q : Type}
    (s t : X ⟶ P) (s' t' : Y ⟶ Q) (fA : X ⟶ Y) (fD : P ⟶ Q)
    (hfSrc_comm : fD ⊚ s = s' ⊚ fA) (hfTgt_comm : fD ⊚ t = t' ⊚ fA)
    : fD ⊚ s = fD ⊚ t ↔ ∀ x, s' (fA x) = t' (fA x) :=
  sorry

variable (XP YQ : IrreflexiveGraph) (f : XP ⟶ YQ)

-- Align to the notation in the book
set_option quotPrecheck false
local notation "fA" => f.val.1
local notation "fD" => f.val.2
set_option quotPrecheck true

local notation "s" => XP.toSrc
local notation "s'" => YQ.toSrc
local notation "t" => XP.toTgt
local notation "t'" => YQ.toTgt

example : (fD ⊚ s = fD ⊚ t) ↔ (∀ x, s' (fA x) = t' (fA x)) :=
  sorry

end ExIII_25

/-!
Exercise III.26 (p. 148)
-/
namespace ExIII_26

def f : ℤ ⟶ ℚ :=
  sorry

def Z : SetWithEndomap := {
  carrier := ℤ
  toEnd := fun x ↦ 5 * x
}

def Q : SetWithEndomap := {
  carrier := ℚ
  toEnd := fun x ↦ 5 * x
}

example : Z ⟶ Q :=
  sorry

example : SetWithInvEndomap :=
  sorry

example : ∀ {T : Type} (x₁ x₂ : T ⟶ ℤ),
    f ⊚ x₁ = f ⊚ x₂ → x₁ = x₂ :=
  sorry

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
    : f X.x₀ = f X.x₁ :=
  sorry

end ExIII_27

/-!
Exercise III.28 (p. 148)
-/
example (Xα : SetWithEndomap) (Yβ : SetWithInvEndomap)
    (f : Xα ⟶ Yβ.toSetWithEndomap)
    (hf_inj : ∀ {U : Type} (y₁ y₂ : U ⟶ Xα.carrier),
        f.val ⊚ y₁ = f.val ⊚ y₂ → y₁ = y₂)
    : ∀ {T : Type} (x₁ x₂ : T ⟶ Xα.carrier),
        Xα.toEnd ⊚ x₁ = Xα.toEnd ⊚ x₂ → x₁ = x₂ :=
  sorry

/-!
Exercise III.29 (p. 150)
-/
/-!
Exercise III.30 (p. 151)
-/
end CM

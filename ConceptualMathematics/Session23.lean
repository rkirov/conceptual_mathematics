import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article4
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory
open Limits


#doc (Manual) "Session 23: More on universal mapping properties" =>

%%%
htmlSplit := .never
number := false
%%%

```savedImport
import ConceptualMathematics.Article4
import Mathlib
open CategoryTheory
open Limits
```

```savedLean -show
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

# 1. A category of pairs of maps

:::question (questionTitle := "Exercise 1") (questionPage := "256")
Formulate and prove in two ways the theorem of uniqueness of the product of two objects $`B_1` and $`B_2` of the category 𝒞. (One way is the direct proof and the other way is to define the category $`𝒞_{B_{1}B_{2}}`, to prove that it is a category, to prove that its terminal object is the same as a product of $`B_1` and $`B_2` in 𝒞, and to appeal to the theorem on uniqueness of terminal objects.)
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise 23.1 (p. 256)
```

```savedLean -show
namespace Ex23_1
```

The direct proof was already given in Article IV. In Exercise 12 of Article IV, we proved uniqueness of the product in the case of two objects, and on p. 221 we proved uniqueness in the case of an arbitrary family of objects.

We now give the second proof, starting with the definition of the category $`𝒞_{B_{1}B_{2}}`.

```savedLean
variable {𝒞 : Type u} [Category.{v, u} 𝒞]

structure PairOfMaps (B₁ B₂ : 𝒞) where
  carrier : 𝒞
  p₁ : carrier ⟶ B₁
  p₂ : carrier ⟶ B₂
```

We show that $`𝒞_{B_{1}B_{2}}` is a valid category.

```savedLean
instance {B₁ B₂ : 𝒞} : Category (PairOfMaps B₁ B₂) where
  Hom X Y := {
    f : X.carrier ⟶ Y.carrier //
        Y.p₁ ⊚ f = X.p₁ ∧ Y.p₂ ⊚ f = X.p₂
  }
  id X := ⟨𝟙 X.carrier, by constructor <;> rw [Category.id_comp]⟩
  comp f g := ⟨g.val ⊚ f.val, by
    constructor
    · rw [Category.assoc, g.property.1, f.property.1]
    · rw [Category.assoc, g.property.2, f.property.2]⟩
```

Next we show that the terminal object of $`𝒞_{B_{1}B_{2}}` is the same as a product of $`B_1` and $`B_2` in 𝒞.

```savedLean
example {B₁ B₂ : 𝒞} {T : PairOfMaps B₁ B₂} (hT : IsTerminal T) :
    ∀ (X : 𝒞) (f₁ : X ⟶ B₁) (f₂ : X ⟶ B₂),
        ∃! f : X ⟶ T.carrier, T.p₁ ⊚ f = f₁ ∧ T.p₂ ⊚ f = f₂ := by
  intro X f₁ f₂
  let XP : PairOfMaps B₁ B₂ := {
    carrier := X
    p₁ := f₁
    p₂ := f₂
  }
  let fP := hT.from XP
  use fP.val
  constructor
  · exact fP.property
  · intro f hf
    let fP' : XP ⟶ T := ⟨f, hf⟩
    exact congr_arg Subtype.val (hT.hom_ext fP' fP)
```

Finally we appeal to the theorem on uniqueness of terminal objects.

```savedLean
example {B₁ B₂ : 𝒞} {T₁ T₂ : PairOfMaps B₁ B₂}
    (hT₁ : IsTerminal T₁) (hT₂ : IsTerminal T₂) :
    Nonempty (T₁.carrier ≅ T₂.carrier) := by
  obtain ⟨t, ⟨ht_iso, _⟩⟩ := uniqueness_of_terminal_objects hT₁ hT₂
  apply Nonempty.intro
  exact {
    hom := t.val
    inv := (inv t).val
    hom_inv_id := congr_arg Subtype.val (IsIso.hom_inv_id t)
    inv_hom_id := congr_arg Subtype.val (IsIso.inv_hom_id t)
  }
```

```savedLean -show
end Ex23_1
```
:::

# 2. How to calculate products

:::definition (definitionTerm := "⟨f₁, f₂⟩") (definitionPage := "257")
For any pair of maps $`{A \xrightarrow{f_1} B_1}`, $`{A \xrightarrow{f_2} B_2}`, $`{\langle f_1, f_2 \rangle}` is the unique map $`{A \rightarrow B_1 \times B_2}` that satisfies the equations $`{p_1 \langle f_1, f_2 \rangle = f_1}` and $`{p_2 \langle f_1, f_2 \rangle = f_2}`.
:::

The relevant mathlib definition here is `prod.lift`, which we print below for reference.

```lean (name := out_prod_lift)
#print prod.lift
```

```leanOutput out_prod_lift
@[reducible] def CategoryTheory.Limits.prod.lift.{v, u} : {C : Type u} →
  [inst : Category.{v, u} C] → {W X Y : C} → [inst_1 : HasBinaryProduct X Y] → (W ⟶ X) → (W ⟶ Y) → (W ⟶ X ⨯ Y) :=
fun {C} [Category.{v, u} C] {W X Y} [HasBinaryProduct X Y] f g ↦ limit.lift (pair X Y) (BinaryFan.mk f g)
```

:::question (questionTitle := "Exercise 2") (questionPage := "260")
Try to create the definition of 'sum' of two objects, in terms of a universal mapping property 'dual' to that of product, by reversing all maps in the definition of product. Then verify that in the category of sets and in the category of graphs, this property actually is satisfied by the intuitive idea of sum: 'Put together with no overlap and no interaction'.
:::

:::solution (solutionTo := "Exercise 2")
```savedComment
Exercise 23.2 (p. 260)
```

```savedLean -show
namespace Ex23_2
```

We start by defining a `CategorySum` structure to represent the sum of two objects in an arbitrary category as the dual of the product.

```savedLean
variable {𝒞 : Type u} [Category.{v, u} 𝒞]

structure CategorySum (B₁ B₂ : 𝒞) where
  carrier : 𝒞
  j₁ : B₁ ⟶ carrier
  j₂ : B₂ ⟶ carrier
  h_univ : ∀ (Y : 𝒞) (g₁ : B₁ ⟶ Y) (g₂ : B₂ ⟶ Y),
      ∃! g : carrier ⟶ Y, g ⊚ j₁ = g₁ ∧ g ⊚ j₂ = g₂
```

In the category of sets (types), the intuitive idea of sum as the disjoint union of two sets (types) is given by the `Sum` type, so we show that `Sum` satisfies the universal mapping property of our `CategorySum` structure.

```savedLean
example {B₁ B₂ : Type} : CategorySum B₁ B₂ := {
  carrier := Sum B₁ B₂
  j₁ := Sum.inl
  j₂ := Sum.inr
  h_univ Y g₁ g₂:= by
    use fun
      | Sum.inl b₁ => g₁ b₁
      | Sum.inr b₂ => g₂ b₂
    constructor
    · constructor <;> rfl
    · intro g ⟨hg₁, hg₂⟩
      funext x
      cases x with
      | inl b₁ => exact congrFun hg₁ b₁
      | inr b₂ => exact congrFun hg₂ b₂
}
```

In the category of graphs, the intuitive idea of sum can be formalised as follows:

```savedLean
def IGSum (B₁ B₂ : IrreflexiveGraph) : IrreflexiveGraph := {
  carrierA := Sum B₁.carrierA B₂.carrierA
  carrierD := Sum B₁.carrierD B₂.carrierD
  toSrc := fun
    | Sum.inl a₁ => Sum.inl (B₁.toSrc a₁)
    | Sum.inr a₂ => Sum.inr (B₂.toSrc a₂)
  toTgt := fun
    | Sum.inl a₁ => Sum.inl (B₁.toTgt a₁)
    | Sum.inr a₂ => Sum.inr (B₂.toTgt a₂)
}

def IGSum.inl {B₁ B₂ : IrreflexiveGraph} : B₁ ⟶ IGSum B₁ B₂ := ⟨
  (Sum.inl, Sum.inl), by constructor <;> rfl
⟩

def IGSum.inr {B₁ B₂ : IrreflexiveGraph} : B₂ ⟶ IGSum B₁ B₂ := ⟨
  (Sum.inr, Sum.inr), by constructor <;> rfl
⟩
```

We then show that `IGSum` satisfies the universal mapping property of our `CategorySum` structure.

```savedLean
example {B₁ B₂ : IrreflexiveGraph} : CategorySum B₁ B₂ := {
  carrier := IGSum B₁ B₂
  j₁ := IGSum.inl
  j₂ := IGSum.inr
  h_univ Y g₁ g₂:= by
    use ⟨
      (fun
         | Sum.inl a₁ => g₁.val.1 a₁
         | Sum.inr a₂ => g₂.val.1 a₂,
       fun
         | Sum.inl d₁ => g₁.val.2 d₁
         | Sum.inr d₂ => g₂.val.2 d₂),
      by
        constructor <;> funext x
        · cases x with
          | inl a₁ => exact congrFun g₁.property.1 a₁
          | inr a₂ => exact congrFun g₂.property.1 a₂
        · cases x with
          | inl a₁ => exact congrFun g₁.property.2 a₁
          | inr a₂ => exact congrFun g₂.property.2 a₂
    ⟩
    constructor
    · constructor <;> rfl
    · intro g ⟨hg₁, hg₂⟩
      obtain ⟨hg₁1, hg₁2⟩ := IrreflexiveGraph.hom_ext_iff.mp hg₁
      obtain ⟨hg₂1, hg₂2⟩ := IrreflexiveGraph.hom_ext_iff.mp hg₂
      apply IrreflexiveGraph.hom_ext <;> funext x
      · cases x with
        | inl a₁ => exact congrFun hg₁1 a₁
        | inr a₂ => exact congrFun hg₂1 a₂
      · cases x with
        | inl d₁ => exact congrFun hg₁2 d₁
        | inr d₂ => exact congrFun hg₂2 d₂
}
```

```savedLean -show
end Ex23_2
```
:::

```savedLean -show
end CM
```

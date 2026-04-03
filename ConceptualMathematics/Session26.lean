import VersoManual
import ConceptualMathematics.Meta.Lean
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory
open Limits


#doc (Manual) "Session 26: Distributive categories and linear categories" =>

%%%
htmlSplit := .never
number := false
%%%

```savedImport
import Mathlib
open CategoryTheory
open Limits
```

```savedLean -show
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

# 2. Matrix multiplication in linear categories

:::definition (definitionTerm := "Linear category") (definitionPage := "279")
A category with zero maps in which every 'identity matrix'...
$$`f = \begin{bmatrix} 1_{X} & 0_{XY} \\ 0_{YX} & 1_{Y} \end{bmatrix} : X + Y \rightarrow X \times Y`
is an isomorphism is called a _linear category_.
:::

Linear categories can be formalised in Lean using a combination of the `HasZeroMorphisms` and `HasBinaryBiproducts` type classes, which we print below for reference.

```lean (name := out_HasZeroMorphisms)
#print HasZeroMorphisms
```

```leanOutput out_HasZeroMorphisms
class CategoryTheory.Limits.HasZeroMorphisms.{v, u} (C : Type u) [Category.{v, u} C] : Type (max u v)
number of parameters: 2
fields:
  CategoryTheory.Limits.HasZeroMorphisms.zero : (X Y : C) → Zero (X ⟶ Y)
  CategoryTheory.Limits.HasZeroMorphisms.comp_zero : ∀ {X Y : C} (f : X ⟶ Y) (Z : C), 0 ⊚ f = 0 := by
    cat_disch
  CategoryTheory.Limits.HasZeroMorphisms.zero_comp : ∀ (X : C) {Y Z : C} (f : Y ⟶ Z), f ⊚ 0 = 0 := by
    cat_disch
constructor:
  CategoryTheory.Limits.HasZeroMorphisms.mk.{v, u} {C : Type u} [Category.{v, u} C] [zero : (X Y : C) → Zero (X ⟶ Y)]
    (comp_zero : ∀ {X Y : C} (f : X ⟶ Y) (Z : C), 0 ⊚ f = 0 := by cat_disch)
    (zero_comp : ∀ (X : C) {Y Z : C} (f : Y ⟶ Z), f ⊚ 0 = 0 := by cat_disch) : HasZeroMorphisms C
```

```lean (name := out_HasBinaryBiproducts)
#print HasBinaryBiproducts
```

```leanOutput out_HasBinaryBiproducts
class CategoryTheory.Limits.HasBinaryBiproducts.{uC', uC} (C : Type uC) [Category.{uC', uC} C] [HasZeroMorphisms C] :
  Prop
number of parameters: 3
fields:
  CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct : ∀ (P Q : C), HasBinaryBiproduct P Q
constructor:
  CategoryTheory.Limits.HasBinaryBiproducts.mk.{uC', uC} {C : Type uC} [Category.{uC', uC} C] [HasZeroMorphisms C]
    (has_binary_biproduct : ∀ (P Q : C), HasBinaryBiproduct P Q) : HasBinaryBiproducts C
```

In a category with zero morphisms, a binary biproduct is a `BinaryBicone` whose cone is a limit cone and whose cocone is a colimit cocone. We print the definition of `BinaryBicone` below for reference.

```lean (name := out_BinaryBicone)
#print BinaryBicone
```

```leanOutput out_BinaryBicone
structure CategoryTheory.Limits.BinaryBicone.{uC', uC} {C : Type uC} [Category.{uC', uC} C] [HasZeroMorphisms C]
  (P Q : C) : Type (max uC uC')
number of parameters: 5
fields:
  CategoryTheory.Limits.BinaryBicone.pt : C
  CategoryTheory.Limits.BinaryBicone.fst : self.pt ⟶ P
  CategoryTheory.Limits.BinaryBicone.snd : self.pt ⟶ Q
  CategoryTheory.Limits.BinaryBicone.inl : P ⟶ self.pt
  CategoryTheory.Limits.BinaryBicone.inr : Q ⟶ self.pt
  CategoryTheory.Limits.BinaryBicone.inl_fst : self.fst ⊚ self.inl = 𝟙 P := by
    aesop
  CategoryTheory.Limits.BinaryBicone.inl_snd : self.snd ⊚ self.inl = 0 := by
    aesop
  CategoryTheory.Limits.BinaryBicone.inr_fst : self.fst ⊚ self.inr = 0 := by
    aesop
  CategoryTheory.Limits.BinaryBicone.inr_snd : self.snd ⊚ self.inr = 𝟙 Q := by
    aesop
constructor:
  CategoryTheory.Limits.BinaryBicone.mk.{uC', uC} {C : Type uC} [Category.{uC', uC} C] [HasZeroMorphisms C] {P Q : C}
    (pt : C) (fst : pt ⟶ P) (snd : pt ⟶ Q) (inl : P ⟶ pt) (inr : Q ⟶ pt) (inl_fst : fst ⊚ inl = 𝟙 P := by aesop)
    (inl_snd : snd ⊚ inl = 0 := by aesop) (inr_fst : fst ⊚ inr = 0 := by aesop)
    (inr_snd : snd ⊚ inr = 𝟙 Q := by aesop) : BinaryBicone P Q
```

# 3. Sum of maps in a linear category

:::question (questionTitle := "Exercise 1") (questionPage := "280")
Using the \[given\] definitions of matrix multiplication and addition of maps, prove the following _formula for matrix multiplication_:
$$`\begin{bmatrix} f_{AX} & f_{AY} \\ f_{BX} & f_{BY} \end{bmatrix} \cdot \begin{bmatrix} g_{XU} & g_{XV} \\ g_{YU} & g_{YV} \end{bmatrix} = \begin{bmatrix} g_{XU} \circ f_{AX} + g_{YU} \circ f_{AY} & g_{XV} \circ f_{AX} + g_{YV} \circ f_{AY} \\ g_{XU} \circ f_{BX} + g_{YU} \circ f_{BY} & g_{XV} \circ f_{BX} + g_{YV} \circ f_{BY} \end{bmatrix}`
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise 26.1 (p. 280)
```

```savedLean -show
namespace Ex26_1
```

We start by defining the required 2×2 matrix of morphisms in a linear category.

```savedLean
noncomputable def matrix2x2 {𝒞 : Type u} [Category.{v, u} 𝒞]
    [HasZeroMorphisms 𝒞] [HasBinaryBiproducts 𝒞]
    {C₁ C₂ A B : 𝒞}
    (f₁₁ : C₁ ⟶ A) (f₁₂ : C₁ ⟶ B)
    (f₂₁ : C₂ ⟶ A) (f₂₂ : C₂ ⟶ B) :
    C₁ ⊞ C₂ ⟶ A ⊞ B :=
  biprod.lift (biprod.desc f₁₁ f₂₁) (biprod.desc f₁₂ f₂₂)
```

In the solution below, we make our linear category `Preadditive` in order to have access to addition of morphisms. (We also use `simp` to discharge the last three of the four required equalities, since all four follow the same pattern.)

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    [Preadditive 𝒞] [HasBinaryBiproducts 𝒞]
    {A B X Y U V : 𝒞}
    (fAX : A ⟶ X) (fAY : A ⟶ Y) (fBX : B ⟶ X) (fBY : B ⟶ Y)
    (gXU : X ⟶ U) (gXV : X ⟶ V) (gYU : Y ⟶ U) (gYV : Y ⟶ V) :
    matrix2x2 gXU gXV gYU gYV ⊚ matrix2x2 fAX fAY fBX fBY =
    matrix2x2
    ((gXU ⊚ fAX) + (gYU ⊚ fAY)) ((gXV ⊚ fAX) + (gYV ⊚ fAY))
    ((gXU ⊚ fBX) + (gYU ⊚ fBY)) ((gXV ⊚ fBX) + (gYV ⊚ fBY)) := by
  apply biprod.hom_ext
      <;> apply biprod.hom_ext' <;> unfold matrix2x2
  · rw [Category.assoc]
    rw [biprod.lift_fst]
    rw [biprod.lift_desc]
    rw [Preadditive.comp_add]
    rw [← Category.assoc]
    rw [biprod.inl_desc]
    rw [← Category.assoc]
    rw [biprod.inl_desc]
    rw [biprod.lift_fst]
    rw [biprod.inl_desc]
  · simp
  · simp
  · simp
```

```savedLean -show
end Ex26_1
```
:::

:::question (questionTitle := "Exercise 2") (questionPage := "280")
Prove that a category with initial and terminal objects has zero maps if and only if an initial object is isomorphic to a terminal object.
:::

:::solution (solutionTo := "Exercise 2")
```savedComment
Exercise 26.2 (p. 280)
```

The equivalence follows from the universal properties of initial and terminal objects.

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    [HasInitial 𝒞] [HasTerminal 𝒞] :
    Nonempty (HasZeroMorphisms 𝒞) ↔ Nonempty (⊥_ 𝒞 ≅ ⊤_ 𝒞) := by
  constructor
  · intro ⟨hZero⟩
    constructor
    exact {
      hom := 0
      inv := 0
      hom_inv_id :=
          initial.hom_ext (0 ⊚ 0 : ⊥_ 𝒞 ⟶ ⊥_ 𝒞) (𝟙 (⊥_ 𝒞))
      inv_hom_id :=
          terminal.hom_ext (0 ⊚ 0 : ⊤_ 𝒞 ⟶ ⊤_ 𝒞) (𝟙 (⊤_ 𝒞))
    }
  · intro ⟨hIso⟩
    constructor
    exact {
      zero X Y := ⟨initial.to Y ⊚ hIso.inv ⊚ terminal.from X⟩
      comp_zero := by
        intros X Y f Z
        change (initial.to Z ⊚ hIso.inv ⊚ terminal.from Y) ⊚ f =
            initial.to Z ⊚ hIso.inv ⊚ terminal.from X
        repeat rw [← Category.assoc]
        rw [terminal.hom_ext (terminal.from Y ⊚ f)]
      zero_comp := by
        intros X Y Z f
        change f ⊚ (initial.to Y ⊚ hIso.inv ⊚ terminal.from X) =
            initial.to Z ⊚ hIso.inv ⊚ terminal.from X
        rw [Category.assoc]
        rw [initial.hom_ext (f ⊚ initial.to Y)]
    }
```
:::

```savedLean -show
end CM
```

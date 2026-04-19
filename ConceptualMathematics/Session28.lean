import VersoManual
import ConceptualMathematics.Meta.Lean
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory
open Limits


#doc (Manual) "Session 28: The category of pointed sets" =>

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

# 1. An example of a non-distributive category

:::question (questionTitle := "Exercise 1") (questionPage := "298")
Both parts of the distributive law are false in the category of pointed sets:

(a) Find an object $`A` for which the map
$$`\mathbf{0} \rightarrow \mathbf{0} \times A`
is not an isomorphism.

(b) Find objects $`A`, $`B_1`, and $`B_2` for which the standard map
$$`A \times B_1 + A \times B_2 \rightarrow A \times (B_1 + B_2)`
is not an isomorphism.
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise 28.1 (p. 298)
```

```savedLean -show
namespace Ex28_1_a
```

For part (a), taking $`A` to be

```savedLean
def A : Pointed := {
  X := Fin 2
  point := 0
}
```

we can show that the map $`{\mathbf{0} \rightarrow \mathbf{0} \times A}` is not an isomorphism, as follows:

```savedLean
example [HasInitial Pointed] [HasBinaryProduct (⊥_ Pointed) A] :
    IsEmpty ((⊥_ Pointed) ≅ (⊥_ Pointed) ⨯ A) := by
  constructor
  intro e
  let a₀ : ⊥_ Pointed ⟶ A := ⟨fun _ ↦ A.point, rfl⟩
  let pA : (⊥_ Pointed) ⨯ A ⟶ A := prod.snd
  let s : A ⟶ (⊥_ Pointed) ⨯ A := prod.lift
      ⟨fun _ ↦ (⊥_ Pointed).point, rfl⟩ (𝟙 A)
  have h_comm : pA ⊚ e.hom = a₀ := initial.hom_ext _ _
  let one : A.X := (1 : Fin 2)
  have h_contra : one = A.point := calc one
    _ = (𝟙 A) one                           := rfl
    _ = (pA ⊚ s) one                       := by rw [prod.lift_snd]
    _ = pA ((𝟙 ((⊥_ Pointed) ⨯ A)) (s one)) := rfl
    _ = pA ((e.hom ⊚ e.inv) (s one))       := by rw [e.inv_hom_id]
    _ = (pA ⊚ e.hom) (e.inv (s one))       := rfl
    _ = a₀ (e.inv (s one))                  := by rw [h_comm]
    _ = A.point                             := rfl
  exact Fin.zero_ne_one h_contra.symm
```

```savedLean -show
end Ex28_1_a
```

```savedLean -show
namespace Ex28_1_b
```

For part (b), taking $`A`, $`B_1`, and $`B_2` to be, respectively,

```savedLean
def A : Pointed := {
  X := Fin 2
  point := 0
}

def B₁ : Pointed := {
  X := Unit
  point := ()
}

def B₂ : Pointed := {
  X := Unit
  point := ()
}
```

we can use the pigeonhole principle (and grind to aid readability) to show that the map $`{A \times B_1 + A \times B_2 \rightarrow A \times (B_1 + B_2)}` is not an isomorphism, as follows:

```savedLean
instance : OfNat A.X 0 where
  ofNat := (0 : Fin 2)

instance : OfNat A.X 1 where
  ofNat := (1 : Fin 2)

example [HasBinaryProduct A B₁] [HasBinaryProduct A B₂]
    [HasBinaryCoproduct (A ⨯ B₁) (A ⨯ B₂)]
    [HasBinaryCoproduct B₁ B₂] [HasBinaryProduct A (B₁ ⨿ B₂)] :
    IsEmpty ((A ⨯ B₁) ⨿ (A ⨯ B₂) ≅ A ⨯ (B₁ ⨿ B₂)) := by
  constructor
  intro e
  -- Alias longer types for convenience
  let L := (A ⨯ B₁) ⨿ (A ⨯ B₂)
  let Z := B₁ ⨿ B₂
  -- Define constant basepoint endomorphism of A
  let cAA : A ⟶ A := ⟨fun _ ↦ A.point, rfl⟩
  -- Construct 3 distinct pathways from A to L
  let cAL : A ⟶ L := ⟨fun _ ↦ L.point, rfl⟩
  let j₁ : A ⟶ L :=
      coprod.inl ⊚ prod.lift (𝟙 A) ⟨fun _ ↦ B₁.point, rfl⟩
  let j₂ : A ⟶ L :=
      coprod.inr ⊚ prod.lift (𝟙 A) ⟨fun _ ↦ B₂.point, rfl⟩
  -- Push pathways through isomorphism to obtain 3 target elements
  let v₀ : A.X := (prod.fst ⊚ e.hom ⊚ cAL) 1
  let v₁ : A.X := (prod.fst ⊚ e.hom ⊚ j₁) 1
  let v₂ : A.X := (prod.fst ⊚ e.hom ⊚ j₂) 1
  -- Define 'detector' morphisms
  let m10 : L ⟶ A := coprod.desc prod.fst (cAA ⊚ prod.fst)
  let m01 : L ⟶ A := coprod.desc (cAA ⊚ prod.fst) prod.fst
  -- Evaluate detector compositions for each pathway
  have h10₀ : m10 ⊚ cAL = cAA := by
    ext
    exact m10.map_point
  have h01₀ : m01 ⊚ cAL = cAA := by
    ext
    exact m01.map_point
  have h10₁ : m10 ⊚ j₁ = 𝟙 A := by
    grind [coprod.inl_desc, prod.lift_fst]
  have h01₁ : m01 ⊚ j₁ = cAA := by
    clear h10₀
    grind [coprod.inl_desc]
  have h10₂ : m10 ⊚ j₂ = cAA := by
    clear h10₁ h01₁
    grind [coprod.inr_desc, prod.lift_fst]
  have h01₂ : m01 ⊚ j₂ = 𝟙 A := by
    clear h10₁ h01₁
    grind [coprod.inr_desc, prod.lift_fst]
  -- Prove all morphisms into Z map to basepoint
  have h_fXZ {X : Pointed} (f : X ⟶ Z) :
      f = ⟨fun _ ↦ Z.point, rfl⟩ := by
    have : 𝟙 Z = ⟨fun _ ↦ Z.point, rfl⟩ := by
      have ext_B₁ {Y : Pointed} (f g : B₁ ⟶ Y) : f = g := by
        ext
        exact f.map_point.trans g.map_point.symm
      have ext_B₂ {Y : Pointed} (f g : B₂ ⟶ Y) : f = g := by
        ext
        exact f.map_point.trans g.map_point.symm
      apply coprod.hom_ext
      · exact ext_B₁ _ _
      · exact ext_B₂ _ _
    calc
      f = 𝟙 Z ⊚ f                     := by rw [Category.comp_id]
      _ = ⟨fun _ ↦ Z.point, rfl⟩ ⊚ f := by rw [this]
      _ = ⟨fun _ ↦ Z.point, rfl⟩      := rfl
  -- Lift element equality to morphism equality for morphisms A ⟶ L
  have h_fAL {a b : A ⟶ L}
      (h_v : (prod.fst ⊚ e.hom ⊚ a) 1 =
          (prod.fst ⊚ e.hom ⊚ b) 1) : a = b := by
    have : e.hom ⊚ a = e.hom ⊚ b := by
      have ext_A {f g : A ⟶ A} (h : f 1 = g 1) : f = g := by
        ext x
        change Fin 2 at x
        fin_cases x
        · exact f.map_point.trans g.map_point.symm
        · exact h
      apply prod.hom_ext
      · exact ext_A h_v
      · rw [h_fXZ (prod.snd ⊚ e.hom ⊚ a),
            h_fXZ (prod.snd ⊚ e.hom ⊚ b)]
    rw [← Category.comp_id a, ← Category.comp_id b, ← e.hom_inv_id,
        ← Category.assoc, ← Category.assoc, this]
  -- Apply pigeonhole principle
  have h_pigeon : v₀ = v₁ ∨ v₀ = v₂ ∨ v₁ = v₂ := by
    cases v₀; cases v₁; cases v₂; grind
  -- Derive contradiction for each collision
  rcases h_pigeon with h01 | h02 | h12
  · have h_contra : (1 : Fin 2) = 0 := calc
      1 = (𝟙 A) 1        := rfl
      _ = (m10 ⊚ j₁) 1  := by rw [h10₁]
      _ = (m10 ⊚ cAL) 1 := by rw [h_fAL h01]
      _ = cAA 1          := by rw [h10₀]
      _ = 0              := rfl
    contradiction
  · have h_contra : (1 : Fin 2) = 0 := calc
      1 = (𝟙 A) 1        := rfl
      _ = (m01 ⊚ j₂) 1  := by rw [h01₂]
      _ = (m01 ⊚ cAL) 1 := by rw [h_fAL h02]
      _ = cAA 1          := by rw [h01₀]
      _ = 0              := rfl
    contradiction
  · have h_contra : (1 : Fin 2) = 0  := calc
      1 = (𝟙 A) 1        := rfl
      _ = (m10 ⊚ j₁) 1  := by rw [h10₁]
      _ = (m10 ⊚ j₂) 1  := by rw [h_fAL h12]
      _ = cAA 1          := by rw [h10₂]
      _ = 0              := rfl
    contradiction
```

```savedLean -show
end Ex28_1_b
```
:::

:::question (questionTitle := "Exercise 2") (questionPage := "298")
As we saw, in the category of pointed sets, the (only) map $`{\mathbf{0} \rightarrow \mathbf{1}}` is an isomorphism. Show that the other clause in the definition of _linear category_ fails, i.e. find objects $`A` and $`B` in $`\mathbf{1}`/𝑺 for which the 'identity matrix'
$$`A + B \rightarrow A \times B`
is not an isomorphism.
:::

:::solution (solutionTo := "Exercise 2")
```savedComment
Exercise 28.2 (p. 298)
```

```savedLean -show
namespace Ex28_2
```

Taking $`A` and $`B` to be, respectively,

```savedLean
def A : Pointed := {
  X := Fin 2
  point := 0
}

def B : Pointed := {
  X := Fin 2
  point := 0
}
```

we can show that the identity matrix is not an isomorphism, as follows:

```savedLean
instance : OfNat A.X 0 where
  ofNat := (0 : Fin 2)

instance : OfNat A.X 1 where
  ofNat := (1 : Fin 2)

instance : OfNat B.X 0 where
  ofNat := (0 : Fin 2)

instance : OfNat B.X 1 where
  ofNat := (1 : Fin 2)

-- Define helper functions
lemma eval_zero {X Y : Pointed} [HasZeroMorphisms Pointed] (x : X.X) :
    (0 : X ⟶ Y) x = Y.point := by
  have : ⟨fun _ ↦ Y.point, rfl⟩ ⊚ (0 : X ⟶ X) = 0 := zero_comp
  rw [← this]; rfl

abbrev d11 : Fin 2 → Fin 2 → Fin 2
  | 1, 1 => 1
  | _, _ => 0

example [HasZeroMorphisms Pointed]
    [HasBinaryProduct A B] [HasBinaryCoproduct A B] :
    IsEmpty (IsIso
        (coprod.desc (prod.lift (𝟙 A) 0) (prod.lift 0 (𝟙 B)))) := by
  constructor
  intro h_iso
  -- Construct identity matrix
  let I := coprod.desc (prod.lift (𝟙 A) 0) (prod.lift 0 (𝟙 B))
  -- Construct morphism v mapping (1, 1) to 1 and everything else to 0
  let v : A ⨯ B ⟶ A := {
    toFun := fun x ↦
      d11 ((prod.fst : A ⨯ B ⟶ A).toFun x)
          ((prod.snd : A ⨯ B ⟶ B).toFun x)
    map_point := by
      rw [(prod.fst : A ⨯ B ⟶ A).map_point,
          (prod.snd : A ⨯ B ⟶ B).map_point]; rfl
  }
  -- Construct diagonal morphism mapping 1 to (1, 1)
  let f11 : A ⟶ A ⨯ B := prod.lift (𝟙 A) ⟨fun x ↦ x, rfl⟩
  -- Evaluate projections on left (a, 0) and right (0, b) axes
  have eval_inl_fst (x : A.X) :
      ((prod.fst : A ⨯ B ⟶ A) ⊚ prod.lift (𝟙 A) 0) x = x := by
    rw [prod.lift_fst]; rfl
  have eval_inl_snd (x : A.X) :
      ((prod.snd : A ⨯ B ⟶ B) ⊚ prod.lift (𝟙 A) 0) x = 0 := by
    rw [prod.lift_snd]
    exact eval_zero x
  have eval_inr_fst (x : B.X) :
      ((prod.fst : A ⨯ B ⟶ A) ⊚ prod.lift 0 (𝟙 B)) x = 0 := by
    rw [prod.lift_fst]
    exact eval_zero x
  have eval_inr_snd (x : B.X) :
      ((prod.snd : A ⨯ B ⟶ B) ⊚ prod.lift 0 (𝟙 B)) x = x := by
    rw [prod.lift_snd]; rfl
  -- Show v acts exactly like zero morphism on left axis
  have hv_inl :
      (v ⊚ I) ⊚ coprod.inl = (0 ⊚ I) ⊚ coprod.inl := by
    have : I ⊚ coprod.inl = prod.lift (𝟙 A) 0 :=
      coprod.inl_desc _ _
    rw [← Category.assoc, ← Category.assoc, this]
    ext x
    change d11 (((prod.fst : A ⨯ B ⟶ A) ⊚ prod.lift (𝟙 A) 0) x)
        (((prod.snd : A ⨯ B ⟶ B) ⊚ prod.lift (𝟙 A) 0) x) =
        (0 : A ⨯ B ⟶ A) ((prod.lift (𝟙 A) 0) x)
    rw [eval_inl_fst, eval_inl_snd, eval_zero]
    change Fin 2 at x
    fin_cases x <;> rfl
  -- Show v acts exactly like zero morphism on right axis
  have hv_inr :
      (v ⊚ I) ⊚ coprod.inr = (0 ⊚ I) ⊚ coprod.inr := by
    have : I ⊚ coprod.inr = prod.lift 0 (𝟙 B) :=
      coprod.inr_desc _ _
    rw [← Category.assoc, ← Category.assoc, this]
    ext x
    change d11 (((prod.fst : A ⨯ B ⟶ A) ⊚ prod.lift 0 (𝟙 B)) x)
        (((prod.snd : A ⨯ B ⟶ B) ⊚ prod.lift 0 (𝟙 B)) x) =
        (0 : A ⨯ B ⟶ A) ((prod.lift 0 (𝟙 B)) x)
    rw [eval_inr_fst, eval_inr_snd, eval_zero]
    change Fin 2 at x
    fin_cases x <;> rfl
  -- Hence v must be zero morphism
  have hv_eq : v = 0 := by
    rw [← Category.id_comp v, ← Category.id_comp 0]
    rw [← h_iso.inv_hom_id I]
    repeat rw [Category.assoc]
    rw [coprod.hom_ext hv_inl hv_inr]
  -- Derive 1 = 0 contradiction by evaluating v at (1, 1)
  have h_contra : (1 : Fin 2) = 0 := calc
    1 = d11 1 1 := rfl
    _ = d11 (((prod.fst : A ⨯ B ⟶ A) ⊚ f11) 1)
            (((prod.snd : A ⨯ B ⟶ B) ⊚ f11) 1) := by
      rw [prod.lift_fst, prod.lift_snd]; rfl
    _ = v (f11 1) := rfl
    _ = (0 : A ⨯ B ⟶ A) (f11 1) := by rw [hv_eq]
    _ = 0 := eval_zero (f11 1)
  contradiction
```

```savedLean -show
end Ex28_2
```
:::

```savedLean -show
end CM
```

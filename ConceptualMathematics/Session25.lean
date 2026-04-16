import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article3
import ConceptualMathematics.Article4
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory
open Limits


#doc (Manual) "Session 25: Labelings and products of graphs" =>

%%%
htmlSplit := .never
number := false
%%%

```savedImport
import ConceptualMathematics.Article3
import ConceptualMathematics.Article4
import Mathlib
open CategoryTheory
open Limits
```

```savedLean -show
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

# 1. Detecting the structure of a graph by means of labelings

The book defines the graph $`2_D` on p. 271, and we formalise it here since it will be used in Exercise 2.

```savedLean
def IrreflexiveGraph.TwoD : IrreflexiveGraph where
  carrierA := Fin 4
  carrierD := Fin 2
  toSrc := fun
    | 0 => 0 -- a
    | 1 => 1 -- b
    | 2 => 0 -- u
    | 3 => 1 -- v
  toTgt := fun
    | 0 => 1 -- a
    | 1 => 0 -- b
    | 2 => 0 -- u
    | 3 => 1 -- v
```

:::question (questionTitle := "Exercise 1") (questionPage := "271")
Find a graph $`2_A` such that a map $`{X \rightarrow 2_A}` amounts to a division of the arrows of $`X` into two sorts.
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise 25.1 (p. 271)
```

A graph $`2_A` has one dot and two arrows, with both arrows being loops on the single dot. Since all morphisms $`{X \rightarrow 2_A}` map every dot in $`X` to the single dot in $`2_A`, each arrow in $`X` can be mapped to either one of the two arrows in $`2_A`. The choice of mapping for each arrow divides the arrows of $`X` into two sorts. We formalise the graph $`2_A` as follows:

```savedLean
def IrreflexiveGraph.TwoA : IrreflexiveGraph where
  carrierA := Fin 2
  carrierD := Unit
  toSrc := fun _ => ()
  toTgt := fun _ => ()
```
:::

:::question (questionTitle := "Exercise 2") (questionPage := "272")
(a) Show that if a diagram of _sets_
$$`B_1 \xrightarrow{j_1} S \xleftarrow{j_2} B_2`
has the property of a coproduct, but restricted to testing against only the one cofigure-type $`{Y = \mathbf{2}}`, then it is actually a coproduct, i.e. has that property for each object $`Y`.

(b) Show that if a diagram of _graphs_
$$`B_1 \xrightarrow{j_1} S \xleftarrow{j_2} B_2`
has the property of a coproduct, but restricted to testing against only the two cofigure-types $`{Y = 2_A}` and $`{Y = 2_D}`, then it is actually a coproduct, i.e. has that property for each object $`Y`.
:::

:::solution (solutionTo := "Exercise 2")
```savedComment
Exercise 25.2 (p. 272)
```

```savedLean -show
namespace Ex25_2
```

For part (a), we use the restricted universal property (testing against $`\mathbf{2}`) to establish a bijection between $`S` and $`{B_1 \oplus B_2}`, the canonical coproduct in the category `Type`. We can then use the resulting equivalence to show that $`S` inherits the full universal property for any arbitrary type $`Y`.

```savedLean
example (B₁ B₂ S : Type) (j₁ : B₁ ⟶ S) (j₂ : B₂ ⟶ S)
    (hS : ∀ (f₁ : B₁ ⟶ Two) (f₂ : B₂ ⟶ Two),
        (∃! f : S ⟶ Two, f₁ = f ⊚ j₁ ∧ f₂ = f ⊚ j₂))
    : ∀ (Y : Type) (g₁ : B₁ ⟶ Y) (g₂ : B₂ ⟶ Y),
        (∃! g : S ⟶ Y, g₁ = g ⊚ j₁ ∧ g₂ = g ⊚ j₂) := by
  classical
  -- Bundle j₁, j₂ into single morphism j from disjoint union B₁ ⊕ B₂
  let j : B₁ ⊕ B₂ ⟶ S := Sum.elim j₁ j₂
  -- Show that j satisfies universal property for Two
  have hj : ∀ k : B₁ ⊕ B₂ ⟶ Two, ∃! f : S ⟶ Two, k = f ⊚ j := by
    intro k
    obtain ⟨f, ⟨hf₁, hf₂⟩, hf_uniq⟩ :=
        hS (k ⊚ Sum.inl) (k ⊚ Sum.inr)
    use f
    constructor
    · funext x
      cases x with
      | inl b₁ => exact congr_fun hf₁ b₁
      | inr b₂ => exact congr_fun hf₂ b₂
    · intro f' hf'
      apply hf_uniq
      constructor <;> (rw [hf']; rfl)
  -- Show that j is injective
  have hj_inj : Function.Injective j := by
    intro x y hxy
    obtain ⟨f, hf, _⟩ := hj (fun b ↦ if x = b then 1 else 0)
    have h : (1 : Two) = if x = y then 1 else 0 :=
      calc (1 : Two)
        _ = if x = x then 1 else 0 := (if_pos rfl).symm
        _ = f (j x)                := congr_fun hf x
        _ = f (j y)                := by rw [hxy]
        _ = if x = y then 1 else 0 := congr_fun hf.symm y
    split_ifs at h with heq
    · exact heq
    · contradiction
  -- Show that j is surjective
  have hj_surj : Function.Surjective j := by
    intro s
    by_contra h_not_mem
    let f₀ : S ⟶ Two := fun _ ↦ 0
    let f₁ : S ⟶ Two := fun x ↦ if x = s then 1 else 0
    have h₀ : (fun _ : B₁ ⊕ B₂ ↦ (0 : Two)) = f₀ ⊚ j := rfl
    have h₁ : (fun _ : B₁ ⊕ B₂ ↦ (0 : Two)) = f₁ ⊚ j := by
      funext x
      have hnc : ¬(j x = s) := fun h ↦ h_not_mem ⟨x, h⟩
      dsimp [f₁]
      exact (if_neg hnc).symm
    have heq : f₀ = f₁ := (hj (fun _ ↦ 0)).unique h₀ h₁
    have h_absurd : (0 : Two) = 1 :=
      calc (0 : Two)
        _ = f₀ s                   := rfl
        _ = f₁ s                   := by rw [heq]
        _ = if s = s then 1 else 0 := rfl
        _ = 1                      := if_pos rfl
    contradiction
  intro Y g₁ g₂
  -- Since j is bijective, we can construct equivalence B₁ ⊕ B₂ ≃ S
  let e : B₁ ⊕ B₂ ≃ S := Equiv.ofBijective j ⟨hj_inj, hj_surj⟩
  -- Construct morphism g : S ⟶ Y
  use fun s ↦ Sum.elim g₁ g₂ (e.symm s)
  constructor
  · -- Prove commutativity
    constructor <;> funext b
    · change g₁ b = Sum.elim g₁ g₂ (e.symm (e (Sum.inl b)))
      rw [Equiv.symm_apply_apply]; rfl
    · change g₂ b = Sum.elim g₁ g₂ (e.symm (e (Sum.inr b)))
      rw [Equiv.symm_apply_apply]; rfl
  · -- Prove uniqueness
    intro f' ⟨h₁, h₂⟩
    funext s
    nth_rw 1 [← Equiv.apply_symm_apply e s]
    cases e.symm s with
    | inl b₁ => exact congr_fun h₁.symm b₁
    | inr b₂ => exact congr_fun h₂.symm b₂
```

For part (b), we follow closely the proof strategy used in part (a). The task is rather more complicated, however, since we need to account for the additional structure of objects and morphisms in the category of graphs.

We begin with a few definitions and lemmas to facilitate moving, in the main proof, between objects in the `IrreflexiveGraph` category and their underlying sets (types) of dots and arrows. The definitions `liftTwoA` and `liftTwoD` construct morphisms from an arbitrary graph $`X` to the graphs $`2_A` and $`2_D`, respectively, given maps from the underlying sets of dots and arrows of $`X` to those of $`2_A` and $`2_D`. The lemmas `liftTwoA_comp` and `liftTwoD_comp` show that these constructions are compatible with composition of morphisms in the category of graphs.

```savedLean
open IrreflexiveGraph

def liftTwoA {X : IrreflexiveGraph} (f : X.carrierA ⟶ TwoA.carrierA)
    : X ⟶ TwoA := ⟨(f, fun _ ↦ ()), by constructor <;> rfl⟩

def mkTwoDArrow (s t : Fin 2) : Fin 4 := match (s, t) with
  | (0, 1) => 0 -- a
  | (1, 0) => 1 -- b
  | (0, 0) => 2 -- u
  | (1, 1) => 3 -- v

lemma mkTwoDArrow_src (s t : Fin 2)
    : TwoD.toSrc (mkTwoDArrow s t) = s := by
  fin_cases s <;> fin_cases t <;> rfl

lemma mkTwoDArrow_tgt (s t : Fin 2)
    : TwoD.toTgt (mkTwoDArrow s t) = t := by
  fin_cases s <;> fin_cases t <;> rfl

def liftTwoD {X : IrreflexiveGraph} (f : X.carrierD ⟶ TwoD.carrierD)
    : X ⟶ TwoD := ⟨
  (fun a ↦ mkTwoDArrow (f (X.toSrc a)) (f (X.toTgt a)), f),
  by
    constructor <;> (funext a; apply Eq.symm)
    · exact mkTwoDArrow_src (f (X.toSrc a)) (f (X.toTgt a))
    · exact mkTwoDArrow_tgt (f (X.toSrc a)) (f (X.toTgt a))
⟩

lemma liftTwoA_comp {X Y : IrreflexiveGraph}
    (f : X ⟶ Y) (g : Y.carrierA ⟶ TwoA.carrierA)
    : liftTwoA (g ⊚ f.val.1) = liftTwoA g ⊚ f := by
  apply IrreflexiveGraph.hom_ext <;> rfl

lemma liftTwoD_comp {X Y : IrreflexiveGraph}
    (f : X ⟶ Y) (g : Y.carrierD ⟶ TwoD.carrierD)
    : liftTwoD (g ⊚ f.val.2) = liftTwoD g ⊚ f := by
  apply IrreflexiveGraph.hom_ext
  · funext a
    change mkTwoDArrow (g ((f.val.2 ⊚ X.toSrc) a))
                       (g ((f.val.2 ⊚ X.toTgt) a)) = _
    rw [f.property.1, f.property.2]; rfl
  · rfl
```

Our main proof now follows. It sacrifices brevity in order to remain as close as possible to the proof strategy in part (a).

```savedLean
example (B₁ B₂ S : IrreflexiveGraph) (j₁ : B₁ ⟶ S) (j₂ : B₂ ⟶ S)
    (hS₁ : ∀ (f₁ : B₁ ⟶ TwoA) (f₂ : B₂ ⟶ TwoA),
        (∃! f : S ⟶ TwoA, f₁ = f ⊚ j₁ ∧ f₂ = f ⊚ j₂))
    (hS₂ : ∀ (f₁ : B₁ ⟶ TwoD) (f₂ : B₂ ⟶ TwoD),
        (∃! f : S ⟶ TwoD, f₁ = f ⊚ j₁ ∧ f₂ = f ⊚ j₂))
    : ∀ (Y : IrreflexiveGraph) (g₁ : B₁ ⟶ Y) (g₂ : B₂ ⟶ Y),
        (∃! g : S ⟶ Y, g₁ = g ⊚ j₁ ∧ g₂ = g ⊚ j₂) := by
  classical
  -- Extract set-level hypothesis for arrows from hS₁
  have hSA : ∀ (fA₁ : B₁.carrierA ⟶ TwoA.carrierA)
      (fA₂ : B₂.carrierA ⟶ TwoA.carrierA),
          ∃! fA : S.carrierA ⟶ TwoA.carrierA,
              fA₁ = fA ⊚ j₁.val.1 ∧ fA₂ = fA ⊚ j₂.val.1 := by
    intro fA₁ fA₂
    obtain ⟨f, ⟨hf₁, hf₂⟩, hf_uniq⟩ :=
      hS₁ (liftTwoA fA₁) (liftTwoA fA₂)
    use f.val.1
    constructor
    · constructor
      · exact congr_arg (·.val.1) hf₁
      · exact congr_arg (·.val.1) hf₂
    · intro fA' ⟨hfA'₁, hfA'₂⟩
      have := hf_uniq (liftTwoA fA') ⟨
        by rw [hfA'₁, liftTwoA_comp],
        by rw [hfA'₂, liftTwoA_comp]
      ⟩
      exact congr_arg (·.val.1) this
  -- Bundle j₁, j₂ for arrows into single morphism jA from B₁ ⊕ B₂
  let jA : B₁.carrierA ⊕ B₂.carrierA ⟶ S.carrierA :=
    Sum.elim j₁.val.1 j₂.val.1
  -- Show that jA satisfies universal property for TwoA.carrierA
  have hjA : ∀ kA : B₁.carrierA ⊕ B₂.carrierA ⟶ TwoA.carrierA,
      ∃! fA : S.carrierA ⟶ TwoA.carrierA, kA = fA ⊚ jA := by
    intro kA
    obtain ⟨fA, ⟨hfA₁, hfA₂⟩, hfA_uniq⟩ :=
      hSA (kA ⊚ Sum.inl) (kA ⊚ Sum.inr)
    use fA
    constructor
    · funext x
      cases x with
      | inl bA₁ => exact congr_fun hfA₁ bA₁
      | inr bA₂ => exact congr_fun hfA₂ bA₂
    · intro fA' hfA'
      apply hfA_uniq
      constructor <;> (rw [hfA']; rfl)
  -- Show that jA is injective
  have hjA_inj : Function.Injective jA := by
    intro x y hxy
    obtain ⟨fA, hfA, _⟩ :=
      hjA (fun b ↦ if x = b then (1 : Fin 2) else (0 : Fin 2))
    have h : (1 : Fin 2) = (if x = x then 1 else 0) :=
        (if_pos rfl).symm
    erw [congr_fun hfA x] at h
    rw [types_comp_apply, hxy, ← types_comp_apply jA fA] at h
    rw [congr_fun hfA.symm y] at h
    split_ifs at h with heq
    · exact heq
    · contradiction
  -- Show that jA is surjective
  have hjA_surj : Function.Surjective jA := by
    intro sA
    by_contra h_not_mem
    let f₀ : S.carrierA ⟶ TwoA.carrierA := fun _ ↦ (0 : Fin 2)
    let f₁ : S.carrierA ⟶ TwoA.carrierA :=
      fun x ↦ if x = sA then (1 : Fin 2) else (0 : Fin 2)
    have h₀ : (fun _ ↦ (0 : Fin 2)) = f₀ ⊚ jA := rfl
    have h₁ : (fun _ ↦ (0 : Fin 2)) = f₁ ⊚ jA := by
      funext x
      have hnc : ¬(jA x = sA) := fun h ↦ h_not_mem ⟨x, h⟩
      dsimp [f₁]
      exact (if_neg hnc).symm
    have heq : f₀ = f₁ := (hjA (fun _ ↦ (0 : Fin 2))).unique h₀ h₁
    have h_absurd : (0 : Fin 2) = f₀ sA := rfl
    rw [heq] at h_absurd
    change (0 : Fin 2) = (if sA = sA then 1 else (0 : Fin 2))
        at h_absurd
    rw [if_pos rfl] at h_absurd
    contradiction
  -- Extract set-level hypothesis for dots from hS₂
  have hSD : ∀ (fD₁ : B₁.carrierD ⟶ TwoD.carrierD)
      (fD₂ : B₂.carrierD ⟶ TwoD.carrierD),
          ∃! fD : S.carrierD ⟶ TwoD.carrierD,
              fD₁ = fD ⊚ j₁.val.2 ∧ fD₂ = fD ⊚ j₂.val.2 := by
    intro fD₁ fD₂
    obtain ⟨f, ⟨hf₁, hf₂⟩, hf_uniq⟩ :=
      hS₂ (liftTwoD fD₁) (liftTwoD fD₂)
    use f.val.2
    constructor
    · constructor
      · exact congr_arg (·.val.2) hf₁
      · exact congr_arg (·.val.2) hf₂
    · intro fD' ⟨hfD'₁, hfD'₂⟩
      have := hf_uniq (liftTwoD fD') ⟨
        by rw [hfD'₁, liftTwoD_comp],
        by rw [hfD'₂, liftTwoD_comp]
      ⟩
      exact congr_arg (·.val.2) this
  -- Bundle j₁, j₂ for dots into single morphism jD from B₁ ⊕ B₂
  let jD : B₁.carrierD ⊕ B₂.carrierD ⟶ S.carrierD :=
    Sum.elim j₁.val.2 j₂.val.2
  -- Show that jD satisfies universal property for TwoD.carrierD
  have hjD : ∀ kD : B₁.carrierD ⊕ B₂.carrierD ⟶ TwoD.carrierD,
      ∃! fD : S.carrierD ⟶ TwoD.carrierD, kD = fD ⊚ jD := by
    intro kD
    obtain ⟨fD, ⟨hfD₁, hfD₂⟩, hfD_uniq⟩ :=
      hSD (kD ⊚ Sum.inl) (kD ⊚ Sum.inr)
    use fD
    constructor
    · funext x
      cases x with
      | inl bD₁ => exact congr_fun hfD₁ bD₁
      | inr hD₂ => exact congr_fun hfD₂ hD₂
    · intro fD' hfD'
      apply hfD_uniq
      constructor <;> (rw [hfD']; rfl)
  -- Show that jD is injective
  have hjD_inj : Function.Injective jD := by
    intro x y hxy
    obtain ⟨fD, hfD, _⟩ :=
      hjD (fun b ↦ if x = b then (1 : Fin 2) else (0 : Fin 2))
    have h : (1 : Fin 2) = (if x = x then 1 else 0) :=
        (if_pos rfl).symm
    erw [congr_fun hfD x] at h
    rw [types_comp_apply, hxy, ← types_comp_apply jD fD] at h
    rw [congr_fun hfD.symm y] at h
    split_ifs at h with heq
    · exact heq
    · contradiction
  -- Show that jD is surjective
  have hjD_surj : Function.Surjective jD := by
    intro sD
    by_contra h_not_mem
    let f₀ : S.carrierD ⟶ TwoD.carrierD := fun _ ↦ (0 : Fin 2)
    let f₁ : S.carrierD ⟶ TwoD.carrierD :=
      fun x ↦ if x = sD then (1 : Fin 2) else (0 : Fin 2)
    have h₀ : (fun _ ↦ (0 : Fin 2)) = f₀ ⊚ jD := rfl
    have h₁ : (fun _ ↦ (0 : Fin 2)) = f₁ ⊚ jD := by
      funext x
      have hnc : ¬(jD x = sD) := fun h ↦ h_not_mem ⟨x, h⟩
      dsimp [f₁]
      exact (if_neg hnc).symm
    have heq : f₀ = f₁ := (hjD (fun _ ↦ (0 : Fin 2))).unique h₀ h₁
    have h_absurd : (0 : Fin 2) = f₀ sD := rfl
    rw [heq] at h_absurd
    change (0 : Fin 2) = (if sD = sD then 1 else (0 : Fin 2))
        at h_absurd
    rw [if_pos rfl] at h_absurd
    contradiction
  intro Y g₁ g₂
  -- Since jA is bijective, we can construct equivalence for arrows
  let eA : B₁.carrierA ⊕ B₂.carrierA ≃ S.carrierA :=
    Equiv.ofBijective jA ⟨hjA_inj, hjA_surj⟩
  -- Since jD is bijective, we can construct equivalence for dots
  let eD : B₁.carrierD ⊕ B₂.carrierD ≃ S.carrierD :=
    Equiv.ofBijective jD ⟨hjD_inj, hjD_surj⟩
  -- Construct morphism g : S ⟶ Y
  use ⟨
    (fun sA ↦ Sum.elim g₁.val.1 g₂.val.1 (eA.symm sA),
     fun sD ↦ Sum.elim g₁.val.2 g₂.val.2 (eD.symm sD)),
    ⟨by -- Prove that source commutes
      funext sA
      obtain ⟨bA, rfl⟩ := eA.surjective sA
      dsimp
      rw [Equiv.symm_apply_apply]
      cases bA with
      | inl bA₁ =>
        change Sum.elim g₁.val.2 g₂.val.2
            (eD.symm ((S.toSrc ⊚ j₁.val.1) bA₁)) = _
        rw [← j₁.property.1]
        change Sum.elim g₁.val.2 g₂.val.2
            (eD.symm (eD (Sum.inl (B₁.toSrc bA₁)))) = _
        rw [Equiv.symm_apply_apply]
        exact congr_fun g₁.property.1 bA₁
      | inr bA₂ =>
        change Sum.elim g₁.val.2 g₂.val.2
            (eD.symm ((S.toSrc ⊚ j₂.val.1) bA₂)) = _
        rw [← j₂.property.1]
        change Sum.elim g₁.val.2 g₂.val.2
            (eD.symm (eD (Sum.inr (B₂.toSrc bA₂)))) = _
        rw [Equiv.symm_apply_apply]
        exact congr_fun g₂.property.1 bA₂,
     by -- Prove that target commutes
      funext sA
      obtain ⟨bA, rfl⟩ := eA.surjective sA
      dsimp
      rw [Equiv.symm_apply_apply]
      cases bA with
      | inl bA₁ =>
        change Sum.elim g₁.val.2 g₂.val.2
            (eD.symm ((S.toTgt ⊚ j₁.val.1) bA₁)) = _
        rw [← j₁.property.2]
        change Sum.elim g₁.val.2 g₂.val.2
            (eD.symm (eD (Sum.inl (B₁.toTgt bA₁)))) = _
        rw [Equiv.symm_apply_apply]
        exact congr_fun g₁.property.2 bA₁
      | inr bA₂ =>
        change Sum.elim g₁.val.2 g₂.val.2
            (eD.symm ((S.toTgt ⊚ j₂.val.1) bA₂)) = _
        rw [← j₂.property.2]
        change Sum.elim g₁.val.2 g₂.val.2
            (eD.symm (eD (Sum.inr (B₂.toTgt bA₂)))) = _
        rw [Equiv.symm_apply_apply]
        exact congr_fun g₂.property.2 bA₂⟩
  ⟩
  constructor
  · -- Prove commutativity
    constructor <;> ext b
    · change _ = Sum.elim g₁.val.1 g₂.val.1
          (eA.symm (eA (Sum.inl b)))
      rw [Equiv.symm_apply_apply]; rfl
    · change _ = Sum.elim g₁.val.2 g₂.val.2
          (eD.symm (eD (Sum.inl b)))
      rw [Equiv.symm_apply_apply]; rfl
    · change _ = Sum.elim g₁.val.1 g₂.val.1
          (eA.symm (eA (Sum.inr b)))
      rw [Equiv.symm_apply_apply]; rfl
    · change _ = Sum.elim g₁.val.2 g₂.val.2
          (eD.symm (eD (Sum.inr b)))
      rw [Equiv.symm_apply_apply]; rfl
  · -- Prove uniqueness
    intro f' ⟨h₁, h₂⟩
    ext s <;> dsimp
    · nth_rw 1 [← Equiv.apply_symm_apply eA s]
      cases eA.symm s with
      | inl bA₁ =>
        exact congr_fun (congr_arg (·.val.1) h₁.symm) bA₁
      | inr bA₂ =>
        exact congr_fun (congr_arg (·.val.1) h₂.symm) bA₂
    · nth_rw 1 [← Equiv.apply_symm_apply eD s]
      cases eD.symm s with
      | inl bD₁ =>
        exact congr_fun (congr_arg (·.val.2) h₁.symm) bD₁
      | inr bD₂ =>
        exact congr_fun (congr_arg (·.val.2) h₂.symm) bD₂
```

```savedLean -show
end Ex25_2
```
:::

:::question (questionTitle := "Exercise 3") (questionPage := "273")
_Tricoloring_ a graph means assigning to each dot one of the three colors white, red, or green, in such a way that for each arrow, the source and target have different colors. If you fix a tricoloring of a graph $`X`, and you have a map of graphs $`{Y \xrightarrow{f} X}`, then you can color the dots of $`Y` also: just color each dot $`{D \xrightarrow{y} Y}` the same color as $`{f y}`. This is called the 'tricoloring of $`Y` _induced_ by $`f`'.

(a) Show that this induced coloring is a tricoloring; i.e. no arrow of $`Y` has source and target the same color.

(b) Find _Fatima's tricolored graph_ $`F`. It is the best tricolored graph: For any graph $`Y`, each tricoloring of $`Y` is induced by exactly one map $`{Y \rightarrow F}`.
:::

:::solution (solutionTo := "Exercise 3")
```savedComment
Exercise 25.3 (p. 273)
```

```savedLean -show
namespace Ex25_3
```

We first define an inductive type to represent the three colours.

```savedLean
inductive Tricolour
  | white | red | green
```

For part (a), we define what it means for a colouring of an irreflexive graph to be a tricolouring. We then show that if we have a tricolouring of a graph $`X`, we can induce a tricolouring of any graph $`Y` that maps to $`X`.

```savedLean
def IsTricolouring (X : IrreflexiveGraph)
    (c : X.carrierD ⟶ Tricolour) : Prop :=
  ∀ a : X.carrierA, c (X.toSrc a) ≠ c (X.toTgt a)

def inducedColouring {Y X : IrreflexiveGraph} (f : Y ⟶ X)
    (c : X.carrierD ⟶ Tricolour) : Y.carrierD ⟶ Tricolour :=
  c ⊚ f.val.2

example {Y X : IrreflexiveGraph} (f : Y ⟶ X)
    (c : X.carrierD ⟶ Tricolour) (h : IsTricolouring X c) :
    IsTricolouring Y (inducedColouring f c) := by
  intro a
  change c ((f.val.2 ⊚ Y.toSrc) a) ≠ c ((f.val.2 ⊚ Y.toTgt) a)
  rw [f.property.1, f.property.2]
  exact h (f.val.1 a)
```

Strictly speaking, since the exercise defines a 'dot' as a morphism $`{D \xrightarrow{y} Y}`, we should be working only with morphisms and not elements of the carrier types. We can reformulate the above definitions and proof exclusively in terms of morphisms, as follows:

```savedLean
def Dot (X : IrreflexiveGraph) := IrreflexiveGraph.D ⟶ X

def srcDot {X : IrreflexiveGraph} (a : X.carrierA) : Dot X := ⟨
  (Empty.elim, fun _ ↦ X.toSrc a),
  ⟨by funext x; exact Empty.elim x,
   by funext x; exact Empty.elim x⟩
⟩

def tgtDot {X : IrreflexiveGraph} (a : X.carrierA) : Dot X := ⟨
  (Empty.elim, fun _ ↦ X.toTgt a),
  ⟨by funext x; exact Empty.elim x,
   by funext x; exact Empty.elim x⟩
⟩

def IsTricolouring' (X : IrreflexiveGraph)
    (c : Dot X ⟶ Tricolour) : Prop :=
  ∀ a : X.carrierA, c (srcDot a) ≠ c (tgtDot a)

def inducedColouring' {Y X : IrreflexiveGraph} (f : Y ⟶ X)
    (c : Dot X ⟶ Tricolour) : Dot Y ⟶ Tricolour :=
  fun y ↦ c (f ⊚ y)

example {Y X : IrreflexiveGraph} (f : Y ⟶ X)
    (c : Dot X ⟶ Tricolour) (h : IsTricolouring' X c) :
    IsTricolouring' Y (inducedColouring' f c) := by
  intro a
  change c (f ⊚ srcDot a) ≠ c (f ⊚ tgtDot a)
  have h_src : f ⊚ srcDot a = srcDot (f.val.1 a) := by
    apply IrreflexiveGraph.hom_ext <;> funext x
    · exact Empty.elim x
    · exact congrFun f.property.1 a
  have h_tgt : f ⊚ tgtDot a = tgtDot (f.val.1 a) := by
    apply IrreflexiveGraph.hom_ext <;> funext x
    · exact Empty.elim x
    · exact congrFun f.property.2 a
  rw [h_src, h_tgt]
  exact h (f.val.1 a)
```

In part (b), we find that Fatima's tricoloured graph $`F` consists of exactly six arrows: white-to-red, white-to-green, red-to-white, red-to-green, green-to-white, and green-to-red. That is, $`F` consists of exactly one arrow for each ordered pair of distinct colours, which we formalise as follows:

```savedLean
def F : IrreflexiveGraph := {
  carrierA := { p : Tricolour × Tricolour // p.1 ≠ p.2 }
  carrierD := Tricolour
  toSrc := fun p ↦ p.val.1
  toTgt := fun p ↦ p.val.2
}
```

We then prove that for any graph $`Y`, each tricolouring of $`Y` is induced by exactly one map $`{Y \rightarrow F}`.

```savedLean
example : IsTricolouring F (𝟙 F.carrierD) := fun a ↦ a.property

example {Y : IrreflexiveGraph}
    (c : Y.carrierD ⟶ Tricolour) (h : IsTricolouring Y c) :
    ∃! g : Y ⟶ F, inducedColouring g (𝟙 F.carrierD) = c := by
  refine ⟨
    ⟨(fun a ↦ ⟨(c (Y.toSrc a), c (Y.toTgt a)), h a⟩, c), ⟨rfl, rfl⟩⟩,
    rfl,
    ?_
  ⟩
  rintro ⟨⟨_, gD⟩, h_src, h_tgt⟩ (rfl : gD = c)
  apply IrreflexiveGraph.hom_ext
  · funext a
    apply Subtype.ext
    exact Prod.ext (congr_fun h_src.symm a) (congr_fun h_tgt.symm a)
  · rfl
```

```savedLean -show
end Ex25_3
```
:::

:::question (questionTitle := "Exercise 4") (questionPage := "273")
```savedComment
Exercise 25.4 (p. 273)
```

In this exercise, $`\mathbf{0}` is the initial graph, with no dots (and, of course, no arrows)

```savedLean
abbrev IrreflexiveGraph.Zero : IrreflexiveGraph := emptyIG
```

and $`A_2` is the graph

```savedLean
def IrreflexiveGraph.A₂ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 3
  toSrc := fun
    | 0 => 0
    | 1 => 1
  toTgt := fun
    | 0 => 1
    | 1 => 2
}
```

Show that for each graph $`X`:

(a) there is either a map $`{X \rightarrow \mathbf{0}}` or a map $`{D \rightarrow X}`, but not both; and

(b) there is either a map $`{X \rightarrow D}` or $`{A \rightarrow X}`, but not both; and

(c) there is either a map $`{X \rightarrow A}` or $`{A_2 \rightarrow X}`, but not both.

Can the sequence $`\mathbf{0}`, $`D`, $`A`, $`A_2` be continued? That is, is there a graph $`C` such that for each graph $`X`

(d) there is either a map $`{X \rightarrow A_2}` or $`{C \rightarrow X}`, but not both?
:::

:::solution (solutionTo := "Exercise 4")
Our proof of part (a) relies on the fact that a map $`{X \rightarrow \mathbf{0}}` can only exist if $`X` has no dots, while a map $`{D \rightarrow X}` can only exist if $`X` has at least one dot.

```savedLean
open IrreflexiveGraph in
example : ∀ X : IrreflexiveGraph,
    Xor' (Nonempty (X ⟶ Zero)) (Nonempty (D ⟶ X)) := by
  intro X
  by_cases h : Nonempty X.carrierD
  · right
    constructor <;> obtain ⟨dX⟩ := h
    · refine ⟨⟨(Empty.elim, fun _ ↦ dX), ⟨?_, ?_⟩⟩⟩
      all_goals
        funext aD
        nomatch aD
    · rintro ⟨f⟩
      nomatch (f.val.2 dX)
  · left
    constructor
    · refine ⟨⟨(fun aX ↦ False.elim (h ⟨X.toSrc aX⟩),
          fun dX ↦ False.elim (h ⟨dX⟩)), ⟨?_, ?_⟩⟩⟩
      all_goals
        funext aX
      · exact False.elim (h ⟨X.toSrc aX⟩)
      · exact False.elim (h ⟨X.toTgt aX⟩)
    · rintro ⟨g⟩
      exact h ⟨g.val.2 ()⟩
```

Our proof of part (b) follows a similar approach to that of part (a) but relies instead on reasoning about the existence of arrows in $`X`.

```savedLean
open IrreflexiveGraph in
example : ∀ X : IrreflexiveGraph,
    Xor' (Nonempty (X ⟶ D)) (Nonempty (A ⟶ X)) := by
  intro X
  by_cases h : Nonempty X.carrierA
  · right
    constructor <;> obtain ⟨aX⟩ := h
    · refine ⟨⟨(fun _ ↦ aX,
          fun | (0 : Fin 2) => X.toSrc aX
              | (1 : Fin 2) => X.toTgt aX), ⟨?_, ?_⟩⟩⟩
      all_goals
        funext aA
        rfl
    · rintro ⟨f⟩
      nomatch (f.val.1 aX)
  · left
    rw [not_nonempty_iff] at h
    constructor
    · refine ⟨⟨(fun aX ↦ IsEmpty.elim h aX, fun _ ↦ ()),
               ⟨?_, ?_⟩⟩⟩
      all_goals
        funext aX
        rfl
    · rintro ⟨g⟩
      exact IsEmpty.elim h (g.val.1 ())
```

Our proof of part (c) again follows a similar approach but relies this time on reasoning about the existence of a path of length two in $`X`.

```savedLean
open IrreflexiveGraph in
example : ∀ X : IrreflexiveGraph,
    Xor' (Nonempty (X ⟶ A)) (Nonempty (A₂ ⟶ X)) := by
  intro X
  by_cases h : ∃ a₁ a₂ : X.carrierA, X.toSrc a₂ = X.toTgt a₁
  · right
    constructor <;> obtain ⟨aX₁, aX₂, haX⟩ := h
    · refine ⟨⟨(fun | (0 : Fin 2) => aX₁ | (1 : Fin 2) => aX₂,
          fun | (0 : Fin 3) => X.toSrc aX₁
              | (1 : Fin 3) => X.toSrc aX₂
              | (2 : Fin 3) => X.toTgt aX₂), ⟨?_, ?_⟩⟩⟩
      all_goals
        funext aA2
        change Fin 2 at aA2
        fin_cases aA2
        try (rw [haX]; rfl)
        rfl
    · rintro ⟨f⟩
      have h_src : f.val.2 (X.toSrc aX₂) = A.toSrc (f.val.1 aX₂) :=
        congr_fun f.property.1 aX₂
      have h_tgt : f.val.2 (X.toTgt aX₁) = A.toTgt (f.val.1 aX₁) :=
        congr_fun f.property.2 aX₁
      rw [haX, h_tgt] at h_src
      change (1 : Fin 2) = (0 : Fin 2) at h_src
      contradiction
  · left
    push Not at h
    constructor
    · classical
      refine ⟨⟨(fun _ ↦ (), fun dX ↦ if ∃ aX : X.carrierA,
          X.toTgt aX = dX then (1 : Fin 2) else (0 : Fin 2)),
          ⟨?_, ?_⟩⟩⟩
      all_goals
        funext aX
      · exact if_neg (fun ⟨a, ha⟩ ↦ h a aX ha.symm)
      · dsimp
        exact if_pos ⟨aX, rfl⟩
    · rintro ⟨g⟩
      have h_src := congr_fun g.property.1 (1 : Fin 2)
      have h_tgt := congr_fun g.property.2 (0 : Fin 2)
      have := h_src.symm.trans h_tgt
      exact h (g.val.1 (0 : Fin 2)) (g.val.1 (1 : Fin 2)) this
```

{htmlSpan (class := "todo")}[TODO Exercise 25.4 (d)]
:::

# 2. Calculating the graphs A ⨯ Y

:::question (questionTitle := "Exercise 5") (questionPage := "274")
```savedComment
Exercise 25.5 (p. 274)
```

```savedLean -show
namespace Ex25_5
```

In this exercise, $`{B =}`

```savedLean
def B : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 3
  toSrc := fun
    | 0 => 0
    | 1 => 1
  toTgt := fun
    | 0 => 1
    | 1 => 2
}
```

and $`{C =}`

```savedLean
def C : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 3
  toSrc := fun
    | 0 => 0
    | 1 => 1
  toTgt := fun
    | 0 => 1
    | 1 => 0
}
```

Show that $`B` is not isomorphic to $`C`, but that $`{A \times B}` is isomorphic to $`{A \times C}`. (We already know examples of the 'failure of cancellation': $`{\mathbf{0} \times X}` and $`{\mathbf{0} \times Y}` are isomorphic for every $`X` and $`Y`; we also saw that $`{D \times A}` is isomorphic to $`{D \times \mathbf{2}}`. This exercise shows that cancellation can fail even when the factor we want to cancel is more 'substantial'.)
:::

:::solution (solutionTo := "Exercise 5")
We show that $`B` is not isomorphic to $`C` by proving that there is no valid morphism from $`C` to $`B`.

```savedLean
example : IsEmpty (B ≅ C) := by
  constructor
  intro ⟨_, g, _, _⟩
  have h_false : ∀ (gA : Fin 2 → Fin 2) (gD : Fin 3 → Fin 3),
      (∀ a : Fin 2, gD (C.toSrc a) = B.toSrc (gA a)) →
      (∀ a : Fin 2, gD (C.toTgt a) = B.toTgt (gA a)) →
      False := by decide
  exact h_false g.val.1 g.val.2
      (congr_fun g.property.1) (congr_fun g.property.2)
```

```savedLean -show
end Ex25_5
```

To show that $`{A \times B}` is isomorphic to $`{A \times C}`, we first extend our `IrreflexiveGraph` category to allow use of the infix operator `⨯` for the categorical product.

```savedLean
def IrreflexiveGraph.prodObj (X Y : IrreflexiveGraph) :
    IrreflexiveGraph := {
  carrierA := X.carrierA × Y.carrierA
  carrierD := X.carrierD × Y.carrierD
  toSrc := fun p ↦ (X.toSrc p.1, Y.toSrc p.2)
  toTgt := fun p ↦ (X.toTgt p.1, Y.toTgt p.2)
}

def IrreflexiveGraph.fstHom (X Y : IrreflexiveGraph) :
    prodObj X Y ⟶ X := ⟨(Prod.fst, Prod.fst), ⟨rfl, rfl⟩⟩

def IrreflexiveGraph.sndHom (X Y : IrreflexiveGraph) :
    prodObj X Y ⟶ Y := ⟨(Prod.snd, Prod.snd), ⟨rfl, rfl⟩⟩

def IrreflexiveGraph.binaryFan (X Y : IrreflexiveGraph) :
    BinaryFan X Y := BinaryFan.mk (fstHom X Y) (sndHom X Y)

def IrreflexiveGraph.isLimit (X Y : IrreflexiveGraph) :
    IsLimit (binaryFan X Y) :=
  BinaryFan.isLimitMk
    (fun s ↦ ⟨
      (fun a ↦ (s.fst.val.1 a, s.snd.val.1 a),
       fun d ↦ (s.fst.val.2 d, s.snd.val.2 d)),
      by
        constructor <;> (funext a; apply Prod.ext)
        · exact congr_fun s.fst.property.1 a
        · exact congr_fun s.snd.property.1 a
        · exact congr_fun s.fst.property.2 a
        · exact congr_fun s.snd.property.2 a⟩)
    (fun _ ↦ by apply hom_ext <;> rfl)
    (fun _ ↦ by apply hom_ext <;> rfl)
    (fun _ _ hm₁ hm₂ ↦ by
      apply hom_ext <;> (funext x; apply Prod.ext)
      · exact congr_fun (congr_arg (fun k ↦ k.val.1) hm₁) x
      · exact congr_fun (congr_arg (fun k ↦ k.val.1) hm₂) x
      · exact congr_fun (congr_arg (fun k ↦ k.val.2) hm₁) x
      · exact congr_fun (congr_arg (fun k ↦ k.val.2) hm₂) x)

open IrreflexiveGraph in
instance (X Y : IrreflexiveGraph) : HasBinaryProduct X Y :=
  HasLimit.mk ⟨binaryFan X Y, isLimit X Y⟩
```

```savedLean -show
namespace Ex25_5
```

We then construct an isomorphism between $`{A \times B}` and $`{A \times C}` by applying the identity mapping to the arrows and swapping the dots $`{(1, 2)}` and $`{(1, 0)}`. This permutation aligns the target of the second arrow in the product graphs, exactly compensating for the structural difference between $`B` and $`C`.

```savedLean
def swapD : Fin 2 × Fin 3 → Fin 2 × Fin 3
  | (1, 2) => (1, 0)
  | (1, 0) => (1, 2)
  | d => d

open IrreflexiveGraph in
noncomputable example : A ⨯ B ≅ A ⨯ C := by
  have h_iso : prodObj A B ≅ prodObj A C := {
    hom := ⟨(id, swapD),
      by
        constructor
        all_goals
          funext ⟨_, aB⟩
          change Fin 2 at aB
          fin_cases aB <;> rfl⟩
    inv := ⟨(id, swapD),
      by
        constructor
        all_goals
          funext ⟨_, aB⟩
          change Fin 2 at aB
          fin_cases aB <;> rfl⟩
    hom_inv_id := by
      apply hom_ext
      · rfl
      · funext ⟨dA, dB⟩
        change Fin 2 at dA
        change Fin 3 at dB
        fin_cases dA <;> fin_cases dB <;> rfl
    inv_hom_id := by
      apply hom_ext
      · rfl
      · funext ⟨dA, dB⟩
        change Fin 2 at dA
        change Fin 3 at dB
        fin_cases dA <;> fin_cases dB <;> rfl
  }
  calc A ⨯ B
    _ ≅ prodObj A B := limit.isoLimitCone ⟨_, isLimit A B⟩
    _ ≅ prodObj A C := h_iso
    _ ≅ A ⨯ C := (limit.isoLimitCone ⟨_, isLimit A C⟩).symm
```

```savedLean -show
end Ex25_5
```
:::

# 3. The distributive law

:::question (questionTitle := "Exercise 6") (questionPage := "275")
Assuming that $`X`, $`B_1` and $`B_2` are objects of a category with sums and products, construct a map from the sum of $`{X \times B_1}` and $`{X \times B_2}` to the product of $`X` with $`{B_1 + B_2}`, i.e. construct a map
$$`(X \times B_1) + (X \times B_2) \rightarrow X \times (B_1 + B_2)`
Hint: Use the universal mapping properties of sum and product, and combine appropriate injections and projections.
:::

:::solution (solutionTo := "Exercise 6")
```savedComment
Exercise 25.6 (p. 275)
```

By the universal mapping property of the sum, to construct a map from $`{(X \times B_1) + (X \times B_2)}` to $`{X \times (B_1 + B_2)}`, it suffices to construct maps from $`{X \times B_1}` and $`{X \times B_2}` to $`{X \times (B_1 + B_2)}`. We can construct these maps using the universal mapping property of the product.

```savedLean
noncomputable example {𝒞 : Type u} [Category.{v, u} 𝒞] {X B₁ B₂ : 𝒞}
    [HasBinaryProducts 𝒞] [HasBinaryCoproducts 𝒞] :
    (X ⨯ B₁) ⨿ (X ⨯ B₂) ⟶ X ⨯ (B₁ ⨿ B₂) :=
  coprod.desc
    (prod.lift prod.fst (coprod.inl ⊚ prod.snd))
    (prod.lift prod.fst (coprod.inr ⊚ prod.snd))
```
:::

```savedLean -show
end CM
```

import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article3
import ConceptualMathematics.Article4
import ConceptualMathematics.Session21
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory
open Limits


#doc (Manual) "Session 24: Uniqueness of products and definition of sum" =>

%%%
htmlSplit := .never
number := false
%%%

```savedImport
import ConceptualMathematics.Article3
import ConceptualMathematics.Article4
import ConceptualMathematics.Session21
import Mathlib
open CategoryTheory
open Limits
```

```savedLean -show
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

# 2. The uniqueness theorem for products

:::theoremDirective (theoremTitle := "Theorem (uniqueness of products)") (theoremPage := "263")
Suppose that both of
$$`B_1 \xleftarrow{p_1} P \xrightarrow{p_2} B_2 \quad\text{and}\quad {B_1 \xleftarrow{q_1} Q \xrightarrow{q_2} B_2}`
are product projection pairs (i.e. the $`p`s as well as the $`q`s satisfy the universal mapping property). Then there is exactly one map $`{P \xrightarrow{f} Q}` for which
$$`q_1 f = p_1 \quad\text{and}\quad q_2 f = p_2`
This map $`f` is in fact an isomorphism.
:::

See the previous formalisations provided in Exercise 12 of Article IV and on pp. 221 & 239.

# 3. Sum of two objects in a category

:::definition (definitionTerm := "Sum of two objects") (definitionPage := "265–266")
A _sum of two objects_ $`B_1`, $`B_2` is an object $`S` and a pair of maps
$$`B_1 \xrightarrow{j_1} S \xleftarrow{j_2} B_2`
having the following universal mapping property: For any two maps
$$`B_1 \xrightarrow{f_1} X \xleftarrow{f_2} B_2`
among all the maps $`{X \xleftarrow{f} S}` there is exactly one that satisfies both
$$`f_1 = f j_1 \quad\text{and}\quad f_2 = f j_2`
...
:::

See the earlier formalisation of _sum_ on p. 222.

:::question (questionTitle := "Exercise 1") (questionPage := "266")
Formulate and prove the theorem of uniqueness of sums.
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise 24.1 (p. 266)
```

Let $`S` and $`T` be two sums of $`B_1` and $`B_2`, with injection maps $`{B_1 \xrightarrow{j_1} S \xleftarrow{j_2} B_2}` and $`{B_1 \xrightarrow{k_1} T \xleftarrow{k_2} B_2}`.

We first provide a proof of the theorem using the mathlib API for (binary) coproducts. For symmetry with our earlier proof of the uniqueness of products, we include the additional result that the unique map between any two sums of the same two objects in a category is an isomorphism.

From the formalisation in mathlib, we obtain the following mappings between the notation for this exercise given above and the data used in our proof:

`S = coconeS.pt`; `j₁ = coconeS.ι.app ⟨WalkingPair.left⟩`; `j₂ = coconeS.ι.app ⟨WalkingPair.right⟩`

`T = coconeT.pt`; `k₁ = coconeT.ι.app ⟨WalkingPair.left⟩`; `k₂ = coconeT.ι.app ⟨WalkingPair.right⟩`

```savedLean
theorem uniqueness_of_sums
    {𝒞 : Type u} [Category.{v, u} 𝒞] (B₁ B₂ : 𝒞)
    (coconeS coconeT : BinaryCofan B₁ B₂)
    (sumS : IsColimit coconeS) (sumT : IsColimit coconeT)
    : ∃! f : coconeS.pt ⟶ coconeT.pt,
        (coconeT.ι.app ⟨WalkingPair.left⟩ =
            f ⊚ coconeS.ι.app ⟨WalkingPair.left⟩ ∧
         coconeT.ι.app ⟨WalkingPair.right⟩ =
            f ⊚ coconeS.ι.app ⟨WalkingPair.right⟩)
        ∧ IsIso f := by
  use sumS.desc coconeT -- f
  split_ands
  · -- Show that k₁ = f ⊚ j₁
    exact (sumS.fac coconeT ⟨WalkingPair.left⟩).symm
  · -- Show that k₂ = f ⊚ j₂
    exact (sumS.fac coconeT ⟨WalkingPair.right⟩).symm
  · -- Show that f is an isomorphism
    apply IsIso.mk
    use sumT.desc coconeS -- f⁻¹
    constructor
    · -- f⁻¹ ⊚ f = 𝟙 S
      rw [sumS.uniq coconeS (𝟙 coconeS.pt)
                            (fun _ ↦ Category.comp_id _)]
      apply sumS.uniq coconeS
      intro j
      erw [← Category.assoc, sumS.fac, sumT.fac]
    · -- f ⊚ f⁻¹ = 𝟙 T
      rw [sumT.uniq coconeT (𝟙 coconeT.pt)
                            (fun _ ↦ Category.comp_id _)]
      apply sumT.uniq coconeT
      intro j
      erw [← Category.assoc, sumT.fac, sumS.fac]
  · -- Show that f is unique
    intro f ⟨⟨h_left, h_right⟩, _⟩
    apply sumS.uniq coconeT
    intro j
    rcases j with ⟨_ | _⟩
    · exact h_left.symm
    · exact h_right.symm
```

We can use the mathlib lemma `IsColimit.nonempty_isColimit_iff_isIso_desc` to do much of the heavy lifting here. A revised version of the proof using this lemma is given below.

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] (B₁ B₂ : 𝒞)
    (coconeS coconeT : BinaryCofan B₁ B₂)
    (sumS : IsColimit coconeS) (sumT : IsColimit coconeT)
    : ∃! f : coconeS.pt ⟶ coconeT.pt,
        (coconeT.ι.app ⟨WalkingPair.left⟩ =
            f ⊚ coconeS.ι.app ⟨WalkingPair.left⟩ ∧
         coconeT.ι.app ⟨WalkingPair.right⟩ =
            f ⊚ coconeS.ι.app ⟨WalkingPair.right⟩)
        ∧ IsIso f := by
  use sumS.desc coconeT
  split_ands
  · -- Show that k₁ = f ⊚ j₁
    exact (sumS.fac coconeT ⟨WalkingPair.left⟩).symm
  · -- Show that k₂ = f ⊚ j₂
    exact (sumS.fac coconeT ⟨WalkingPair.right⟩).symm
  · -- Show that f is an isomorphism
    exact (IsColimit.nonempty_isColimit_iff_isIso_desc sumS).mp
        ⟨sumT⟩
  · -- Show that f is unique
    intro f ⟨⟨h_left, h_right⟩, _⟩
    apply sumS.uniq coconeT
    intro j
    rcases j with ⟨_ | _⟩
    · exact h_left.symm
    · exact h_right.symm
```

We next provide a proof using only the book definition of sum.

```savedLean
theorem uniqueness_of_sums'
    {𝒞 : Type u} [Category.{v, u} 𝒞] (B₁ B₂ S T : 𝒞)
    (j₁ : B₁ ⟶ S) (j₂ : B₂ ⟶ S)
    (hS : ∀ (X : 𝒞) (f₁ : B₁ ⟶ X) (f₂ : B₂ ⟶ X),
        (∃! f : S ⟶ X, f₁ = f ⊚ j₁ ∧ f₂ = f ⊚ j₂))
    (k₁ : B₁ ⟶ T) (k₂ : B₂ ⟶ T)
    (hT : ∀ (X : 𝒞) (f₁ : B₁ ⟶ X) (f₂ : B₂ ⟶ X),
        (∃! f : T ⟶ X, f₁ = f ⊚ k₁ ∧ f₂ = f ⊚ k₂))
    : Nonempty (S ≅ T) := by
  obtain ⟨f, hf_comm, _⟩ := hS T k₁ k₂
  obtain ⟨g, hg_comm, _⟩ := hT S j₁ j₂
  have hgf : g ⊚ f = 𝟙 S := by
    apply (hS S j₁ j₂).unique
    · constructor
      · symm
        calc (g ⊚ f) ⊚ j₁
          _ = g ⊚ (f ⊚ j₁) := by rw [Category.assoc]
          _ = g ⊚ k₁        := by rw [← hf_comm.1]
          _ = j₁             := by rw [← hg_comm.1]
      · symm
        calc (g ⊚ f) ⊚ j₂
          _ = g ⊚ (f ⊚ j₂) := by rw [Category.assoc]
          _ = g ⊚ k₂        := by rw [← hf_comm.2]
          _ = j₂             := by rw [← hg_comm.2]
    · constructor <;> rw [Category.comp_id]
  have hfg : f ⊚ g = 𝟙 T := by
    apply (hT T k₁ k₂).unique
    · constructor
      · symm
        calc (f ⊚ g) ⊚ k₁
          _ = f ⊚ (g ⊚ k₁) := by rw [Category.assoc]
          _ = f ⊚ j₁        := by rw [← hg_comm.1]
          _ = k₁             := by rw [← hf_comm.1]
      · symm
        calc (f ⊚ g) ⊚ k₂
          _ = f ⊚ (g ⊚ k₂) := by rw [Category.assoc]
          _ = f ⊚ j₂        := by rw [← hg_comm.2]
          _ = k₂             := by rw [← hf_comm.2]
    · constructor <;> rw [Category.comp_id]
  apply Nonempty.intro
  exact {
    hom := f
    inv := g
    hom_inv_id := hgf
    inv_hom_id := hfg
  }
```
:::

:::question (questionTitle := "Exercise 2") (questionPage := "267")
Prove the following formulas:

(a) $`{D + D = 2 \times D}`

(b) $`{D × D = D}`

(c) $`{A × D = D + D}`
:::

:::solution (solutionTo := "Exercise 2")
```savedComment
Exercise 24.2 (p. 267)
```

```savedLean -show
namespace Ex24_2
```

For part (a), we first formalise the graph $`2`.

```savedLean
def IG2 : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 2
  toSrc := fun x ↦ x
  toTgt := fun x ↦ x
}
```

We then show that $`{D + D = 2 \times D}` (up to isomorphism).

```savedLean
open IrreflexiveGraph in
noncomputable
example {sumDD prod2D : IrreflexiveGraph}
    (j₁ : D ⟶ sumDD) (j₂ : D ⟶ sumDD)
    (h_sumDD : ∀ (X : IrreflexiveGraph) (f₁ : D ⟶ X) (f₂ : D ⟶ X),
        (∃! f : sumDD ⟶ X, f₁ = f ⊚ j₁ ∧ f₂ = f ⊚ j₂))
    (p₁ : prod2D ⟶ IG2) (p₂ : prod2D ⟶ D)
    (h_prod2D : ∀ (Y : IrreflexiveGraph) (g₁ : Y ⟶ IG2) (g₂ : Y ⟶ D),
        (∃! g : Y ⟶ prod2D, g₁ = p₁ ⊚ g ∧ g₂ = p₂ ⊚ g))
    : sumDD ≅ prod2D := by
  -- Define graph G isomorphic to both sumDD and prod2D
  let G : IrreflexiveGraph := {
    carrierA := Empty
    carrierD := Fin 2
    toSrc := Empty.elim
    toTgt := Empty.elim
  }
  -- Define injections to G
  let jG₁ : D ⟶ G := {
    val := ⟨Empty.elim, fun _ ↦ 0⟩
    property := by constructor <;> (funext x; cases x)
  }
  let jG₂ : D ⟶ G := {
    val := ⟨Empty.elim, fun _ ↦ 1⟩
    property := by constructor <;> (funext x; cases x)
  }
  -- Define projections from G
  let pG₁ : G ⟶ IG2 := {
    val := ⟨Empty.elim, fun x ↦ x⟩
    property := by constructor <;> (funext x; cases x)
  }
  let pG₂ : G ⟶ D := {
    val := ⟨Empty.elim, fun x ↦ ()⟩
    property := by constructor <;> (funext x; cases x)
  }
  -- Show that G satisfies universal property for sums
  have h_sumG : ∀ (X : IrreflexiveGraph) (f₁ : D ⟶ X) (f₂ : D ⟶ X),
        (∃! f : G ⟶ X, f₁ = f ⊚ jG₁ ∧ f₂ = f ⊚ jG₂) := by
    intros X f₁ f₂
    use {
      val := ⟨Empty.elim, fun | 0 => f₁.val.2 () | 1 => f₂.val.2 ()⟩
      property := by constructor <;> (funext x; cases x)
    }
    constructor
    · constructor
      all_goals
        ext x
        cases x
        rfl
    · intros f hf
      ext x
      · cases x
      · fin_cases x
        · rw [hf.1]; rfl
        · rw [hf.2]; rfl
  -- Hence G is isomorphic to sumDD by uniqueness of sums
  have h_iso_sum : G ≅ sumDD := Classical.choice
      (uniqueness_of_sums' D D G sumDD jG₁ jG₂ h_sumG j₁ j₂ h_sumDD)
  -- Show that G satisfies universal property for products
  have h_prodG :
      ∀ (Y : IrreflexiveGraph) (g₁ : Y ⟶ IG2) (g₂ : Y ⟶ D),
          (∃! g : Y ⟶ G, g₁ = pG₁ ⊚ g ∧ g₂ = pG₂ ⊚ g) := by
    intros Y g₁ g₂
    use {
      val := ⟨g₂.val.1, g₁.val.2⟩
      property := by
        constructor <;> (funext e; nomatch g₂.val.1 e)
    }
    constructor
    · constructor
      · ext e
        · nomatch g₂.val.1 e
        · rfl
      · ext e
        nomatch g₂.val.1 e
    · intros g hg
      ext e
      · nomatch g.val.1 e
      · rw [hg.1]; rfl
  -- Hence G is isomorphic to prod2D by uniqueness of products
  have h_iso_prod : G ≅ prod2D := Classical.choice
      (uniqueness_of_products'
          IG2 D G prod2D pG₁ pG₂ h_prodG p₁ p₂ h_prod2D)
  -- sumDD and prod2D are therefore isomorphic by transitivity
  exact Iso.trans h_iso_sum.symm h_iso_prod
```

For part (b), we show that $`{D × D = D}` (up to isomorphism).

```savedLean
open IrreflexiveGraph in
noncomputable
example {prodDD : IrreflexiveGraph}
    (p₁ : prodDD ⟶ D) (p₂ : prodDD ⟶ D)
    (h_prodDD : ∀ (Y : IrreflexiveGraph) (g₁ : Y ⟶ D) (g₂ : Y ⟶ D),
        (∃! g : Y ⟶ prodDD, g₁ = p₁ ⊚ g ∧ g₂ = p₂ ⊚ g))
    : prodDD ≅ D := {
    hom := {
      val := ⟨p₁.val.1, fun _ ↦ ()⟩
      property := by constructor <;> rfl
    }
    inv := Classical.choose (h_prodDD D (𝟙 D) (𝟙 D)).exists
    hom_inv_id := by
      have h_finv_comm :=
        Classical.choose_spec (h_prodDD D (𝟙 D) (𝟙 D)).exists
      apply (h_prodDD prodDD p₁ p₂).unique
      · constructor
        · rw [Category.assoc, ← h_finv_comm.1, Category.comp_id]
          rfl
        · rw [Category.assoc, ← h_finv_comm.2, Category.comp_id]
          apply IrreflexiveGraph.hom_ext
          · funext x
            nomatch p₂.val.1 x
          · rfl
      · constructor <;> rw [Category.id_comp]
    inv_hom_id := by
      ext x
      nomatch x
  }
```

The proof of $`{A × D = D + D}` in part (c) is very similar to the proof of $`{D + D = 2 \times D}` in part (a).

```savedLean
open IrreflexiveGraph in
noncomputable
example {prodAD sumDD : IrreflexiveGraph}
    (p₁ : prodAD ⟶ A) (p₂ : prodAD ⟶ D)
    (h_prodAD : ∀ (Y : IrreflexiveGraph) (g₁ : Y ⟶ A) (g₂ : Y ⟶ D),
        (∃! g : Y ⟶ prodAD, g₁ = p₁ ⊚ g ∧ g₂ = p₂ ⊚ g))
    (j₁ : D ⟶ sumDD) (j₂ : D ⟶ sumDD)
    (h_sumDD : ∀ (X : IrreflexiveGraph) (f₁ : D ⟶ X) (f₂ : D ⟶ X),
        (∃! f : sumDD ⟶ X, f₁ = f ⊚ j₁ ∧ f₂ = f ⊚ j₂))
    : prodAD ≅ sumDD := by
  -- Define graph G isomorphic to both prodAD and sumDD
  let G : IrreflexiveGraph := {
    carrierA := Empty
    carrierD := Fin 2
    toSrc := Empty.elim
    toTgt := Empty.elim
  }
  -- Define projections from G
  let pG₁ : G ⟶ A := {
    val := ⟨Empty.elim, fun x ↦ x⟩
    property := by constructor <;> (funext x; cases x)
  }
  let pG₂ : G ⟶ D := {
    val := ⟨Empty.elim, fun x ↦ ()⟩
    property := by constructor <;> (funext x; cases x)
  }
  -- Define injections to G
  let jG₁ : D ⟶ G := {
    val := ⟨Empty.elim, fun _ ↦ 0⟩
    property := by constructor <;> (funext x; cases x)
  }
  let jG₂ : D ⟶ G := {
    val := ⟨Empty.elim, fun _ ↦ 1⟩
    property := by constructor <;> (funext x; cases x)
  }
  -- Show that G satisfies universal property for products
  have h_prodG :
      ∀ (Y : IrreflexiveGraph) (g₁ : Y ⟶ A) (g₂ : Y ⟶ D),
          (∃! g : Y ⟶ G, g₁ = pG₁ ⊚ g ∧ g₂ = pG₂ ⊚ g) := by
    intros Y g₁ g₂
    use {
      val := ⟨g₂.val.1, g₁.val.2⟩
      property := by
        constructor <;> (funext e; nomatch g₂.val.1 e)
    }
    constructor
    · constructor
      · rfl
      · ext e
        nomatch g₂.val.1 e
    · intros g hg
      ext e
      · nomatch g.val.1 e
      · rw [hg.1]; rfl
  -- Hence G is isomorphic to prodAD by uniqueness of products
  have h_iso_prod : G ≅ prodAD := Classical.choice
      (uniqueness_of_products'
          A D G prodAD pG₁ pG₂ h_prodG p₁ p₂ h_prodAD)
  -- Show that G satisfies universal property for sums
  have h_sumG : ∀ (X : IrreflexiveGraph) (f₁ : D ⟶ X) (f₂ : D ⟶ X),
        (∃! f : G ⟶ X, f₁ = f ⊚ jG₁ ∧ f₂ = f ⊚ jG₂) := by
    intros X f₁ f₂
    use {
      val := ⟨Empty.elim, fun | 0 => f₁.val.2 () | 1 => f₂.val.2 ()⟩
      property := by constructor <;> (funext x; cases x)
    }
    constructor
    · constructor
      all_goals
        ext x
        cases x
        rfl
    · intros f hf
      ext x
      · cases x
      · fin_cases x
        · rw [hf.1]; rfl
        · rw [hf.2]; rfl
  -- Hence G is isomorphic to sumDD by uniqueness of sums
  have h_iso_sum : G ≅ sumDD := Classical.choice
      (uniqueness_of_sums' D D G sumDD jG₁ jG₂ h_sumG j₁ j₂ h_sumDD)
  -- prodAD and sumDD are therefore isomorphic by transitivity
  exact Iso.trans h_iso_prod.symm h_iso_sum
```

```savedLean -show
end Ex24_2
```
:::

:::question (questionTitle := "Exercise 3") (questionPage := "268")
Reread Section 5 of Session 15 and find a method, starting from presentations of $`X^{↻\alpha}` and $`Y^{↻\beta}`, to construct presentations of

(a) $`{X^{↻\alpha} + Y^{↻\beta}}`

(b) $`{X^{↻\alpha} \times Y^{↻\beta}}`

Part (b) is harder than part (a).
:::

:::solution (solutionTo := "Exercise 3")
(a) Given a presentation of $`X^{↻\alpha}` with a list of generators $`(\mathbf{L}_X)` and a list of relations $`(\mathbf{R}_X)`, and a presentation of $`Y^{↻\beta}` with a list of generators $`(\mathbf{L}_Y)` and a list of relations $`(\mathbf{R}_Y)`, then a presentation of $`{X^{↻\alpha} + Y^{↻\beta}}` can be constructed simply from the disjoint union of generators $`(\mathbf{L}_X)` and $`(\mathbf{L}_Y)`, together with the disjoint union of relations $`(\mathbf{R}_X)` and $`(\mathbf{R}_Y)` (with suitable relabelling of the generators and relations to avoid name clashes between generators injected from $`X^{↻\alpha}` and those injected from $`Y^{↻\beta}`).

{htmlSpan (class := "todo")}[TODO Exercise 24.3 (b)]
:::

```savedLean -show
end CM
```

import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article3
import ConceptualMathematics.Article4
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory
open Limits


#doc (Manual) "Session 27: Examples of universal constructions" =>

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

# 2. Can objects have negatives?

:::question (questionTitle := "Exercise 1") (questionPage := "288")
Prove that if $`A` and $`B` are objects and $`{A \times B = \mathbf{1}}`, then $`{A = B = \mathbf{1}}`. More precisely, if $`\mathbf{1}` is terminal and
$$`A \xleftarrow{p_1} \mathbf{1} \xrightarrow{p_2} B`
is a product, then $`A` and $`B` are terminal objects.
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise 27.1 (p. 288)
```

To prove that $`A` and $`B` are terminal, we construct two binary fans over $`A` and $`B`, one with vertex $`A` and the other with vertex $`B`. The universal property of the product yields a unique map from each vertex to the limit $`\mathbf{1}`. We then use the universal properties of product and terminal object to show that these maps form isomorphisms.

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] [HasTerminal 𝒞]
    (A B : 𝒞) (p₁ : ⊤_ 𝒞 ⟶ A) (p₂ : ⊤_ 𝒞 ⟶ B)
    (P : IsLimit (BinaryFan.mk p₁ p₂)) :
    Nonempty (A ≅ ⊤_ 𝒞) ∧ Nonempty (B ≅ ⊤_ 𝒞) := by
  constructor <;> apply Nonempty.intro
  · let fanA := BinaryFan.mk (𝟙 A) (p₂ ⊚ terminal.from A)
    exact {
      hom := P.lift fanA
      inv := p₁
      hom_inv_id := P.fac fanA ⟨WalkingPair.left⟩
      inv_hom_id := terminal.hom_ext _ _
    }
  · let fanB := BinaryFan.mk (p₁ ⊚ terminal.from B) (𝟙 B)
    exact {
      hom := P.lift fanB
      inv := p₂
      hom_inv_id := P.fac fanB ⟨WalkingPair.right⟩
      inv_hom_id := terminal.hom_ext _ _
    }
```
:::

# 3. Idempotent objects

:::question (questionTitle := "Exercise 2") (questionPage := "290")
(a) Show that if $`C` has the property that for each $`X` there is at most one map $`{X \rightarrow C}`, then
$$`C \xleftarrow{1_C} C \xrightarrow{1_C} C`
is a product.

(b) Show that the property above is also equivalent to the following property: The unique map $`{C \rightarrow \mathbf{1}}` is a monomorphism.
:::

:::solution (solutionTo := "Exercise 2")
```savedComment
Exercise 27.2 (p. 290)
```

Since in mathlib the `Subsingleton` type class represents a type with at most one element, we can use `Subsingleton` in both parts of the exercise to formalise the property that for each $`X` there is at most one map $`{X \rightarrow C}`.

For part (a), we have

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] (C : 𝒞)
    (h : ∀ X : 𝒞, Subsingleton (X ⟶ C)) :
    IsLimit (BinaryFan.mk (𝟙 C) (𝟙 C)) := {
  lift s := BinaryFan.fst s
  fac s := fun ⟨j⟩ ↦ by
    cases j
    all_goals
      dsimp
      exact Subsingleton.elim _ _
  uniq s m _ := by
    dsimp
    exact Subsingleton.elim _ _
}
```

and for part (b), we have

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] [HasTerminal 𝒞] (C : 𝒞) :
    (∀ X : 𝒞, Subsingleton (X ⟶ C)) ↔ Mono (terminal.from C) := by
  constructor
  · intros
    exact { right_cancellation _ _ _ := Subsingleton.elim _ _ }
  · intro h X
    exact
        ⟨fun a b ↦ h.right_cancellation a b (terminal.hom_ext _ _)⟩
```
:::

:::question (questionTitle := "Exercise 3") (questionPage := "291")
Find all objects $`C` in 𝑺, 𝑺↻, and 𝑺⇊ such that this is a product:
$$`C \xleftarrow{1_C} C \xrightarrow{1_C} C`
:::

:::solution (solutionTo := "Exercise 3")
```savedComment
Exercise 27.3 (p. 291)
```

In 𝑺, $`C` must either be empty or have a single element—i.e., $`C` must be a `Subsingleton` type.

```savedLean
example (C : Type) :
    Subsingleton C → IsLimit (BinaryFan.mk (𝟙 C) (𝟙 C)) := by
  intro
  exact {
    lift s := BinaryFan.fst s
    fac s := fun ⟨j⟩ ↦ by
      cases j
      all_goals
        dsimp
        ext x
        exact Subsingleton.elim _ _
    uniq s m _ := by
      ext x
      exact Subsingleton.elim _ (_ : C)
  }
```

In 𝑺↻, $`C` must either be empty or have a single element with the identity map. (We re-use relevant definitions from Article IV.)

```savedLean
-- Empty
example : IsLimit (BinaryFan.mk (𝟙 emptySWE) (𝟙 emptySWE)) := by
  exact {
    lift s := BinaryFan.fst s
    fac s := fun ⟨j⟩ ↦ by
      cases j
      all_goals
        apply ConcreteCategory.hom_ext
        intro x
        exact Empty.elim (BinaryFan.fst s x)
    uniq s m _ := by
      apply ConcreteCategory.hom_ext
      intro x
      exact Empty.elim (m x)
  }

-- Single element with identity map (terminal object in 𝑺↻)
example : IsLimit (BinaryFan.mk (𝟙 termSWE) (𝟙 termSWE)) := by
  exact {
    lift s := BinaryFan.fst s
    fac s := fun ⟨j⟩ ↦ by
      cases j <;> rfl
    uniq s m _ := by
      apply ConcreteCategory.hom_ext
      intro x
      rfl
  }
```

In 𝑺⇊, $`C` must either be the empty graph, a 'naked dot', or a single dot with one looping arrow. (We again re-use relevant definitions from Article IV.)

```savedLean
-- Empty graph
example : IsLimit (BinaryFan.mk (𝟙 emptyIG) (𝟙 emptyIG)) := by
  exact {
    lift s := BinaryFan.fst s
    fac s := fun ⟨j⟩ ↦ by
      cases j
      all_goals
        apply IrreflexiveGraph.hom_ext <;> funext x
        · exact Empty.elim ((BinaryFan.fst s).val.1 x)
        · exact Empty.elim ((BinaryFan.fst s).val.2 x)
    uniq s m _ := by
      apply IrreflexiveGraph.hom_ext <;> funext x
      · exact Empty.elim (m.val.1 x)
      · exact Empty.elim (m.val.2 x)
  }

-- Naked dot
open IrreflexiveGraph in
example : IsLimit (BinaryFan.mk (𝟙 D) (𝟙 D)) := by
  exact {
    lift s := BinaryFan.fst s
    fac s := fun ⟨j⟩ ↦ by
      cases j
      all_goals
        apply IrreflexiveGraph.hom_ext <;> funext x
        · exact Empty.elim ((BinaryFan.fst s).val.1 x)
        · rfl
    uniq s m _ := by
      apply IrreflexiveGraph.hom_ext <;> funext x
      · exact Empty.elim (m.val.1 x)
      · rfl
  }

-- Single dot with one looping arrow (terminal object in 𝑺⇊)
open IrreflexiveGraph in
example : IsLimit (BinaryFan.mk (𝟙 termIG) (𝟙 termIG)) := by
  exact {
    lift s := BinaryFan.fst s
    fac s := fun ⟨j⟩ ↦ by
      cases j
      all_goals
        apply IrreflexiveGraph.hom_ext <;> (funext x; rfl)
    uniq s m _ := by
      apply IrreflexiveGraph.hom_ext <;> (funext x; rfl)
  }
```
:::

:::question (questionTitle := "Exercise 4") (questionPage := "292")
The inverse, call it $`g`, of the isomorphism of sets $`{\mathbb{N} \xrightarrow{f} \mathbb{N} \times \mathbb{N}}` above \[the Cantor pairing function\] is actually given by a quadratic polynomial, of the form
$$`g(x, y) = \tfrac{1}{2}(ax^2 + bxy + cy^2 + dx + ey)`
where $`a`, $`b`, $`c`, $`d`, and $`e` are fixed natural numbers. Can you find them? Can you prove that the map $`g` defined by your formula is an isomorphism of sets? You might expect that $`f` would have a simpler formula than its inverse $`g`, since a map $`{\mathbb{N} \xrightarrow{f} \mathbb{N} \times \mathbb{N}}` amounts to a pair of maps $`{f_1 = p_1 f}` and $`{f_2 = p_2 f}` from $`\mathbb{N}` to $`\mathbb{N}`. But $`f_1` and $`f_2` are not so simple. In fact, no matter _what_ isomorphism $`{\mathbb{N} \xrightarrow{f} \mathbb{N} \times \mathbb{N}}` you choose, $`f_1` cannot be given by a polynomial. Can you see why?
:::

:::solution (solutionTo := "Exercise 4")
```savedComment
Exercise 27.4 (p. 292)
```

```savedLean -show
namespace Ex27_4
```

Let the pair $`{(x, y)}` be an arbitary element of $`{\mathbb{N} \times \mathbb{N}}`, and let $`{n = x + y}`. Then the total number of pairs in all northwest diagonals strictly preceding the $`n`-th diagonal is the $`n`-th triangular number $`{T_n = \frac{1}{2}n(n + 1)}`. To obtain the exact position of the pair $`{(x, y)}` on the $`n`-th diagonal, we add $`y` to $`T_n`. Thus, the formula for $`g` is
$$`g(x, y) = \tfrac{1}{2}(x + y)(x + y + 1) + y = \tfrac{1}{2}(x^2 + 2xy + y^2 + x + 3y).`

To prove that $`g` is an isomorphism of sets, we show that $`g` is a bijective function. (We apply the `grind` tactic liberally in the remaining proofs in this exercise to keep them succinct.)

We begin our proof by defining triangular numbers and the function $`g`.

```savedLean
def tri : ℕ → ℕ
| 0 => 0
| n + 1 => tri n + n + 1

def g : ℕ × ℕ ⟶ ℕ := fun (x, y) ↦ tri (x + y) + y
```

Next we define some helper lemmas.

```savedLean
lemma tri_le_of_le {a b : ℕ} (h : a ≤ b) : tri a ≤ tri b := by
  induction h
  case refl => rfl
  case step m _ ih =>
    exact ih.trans (Nat.le_add_right (tri m) (m + 1))

lemma g_ubound {x y : ℕ} : g (x, y) < tri (x + y + 1) := by
  grind [g, tri]

lemma g_lbound {x y : ℕ} : tri (x + y) ≤ g (x, y) :=
  Nat.le_add_right (tri (x + y)) y

lemma eq_of_g_eq {x y x' y' : ℕ} (h : g (x, y) = g (x', y')) :
    x + y = x' + y' := by
  rcases lt_trichotomy (x + y) (x' + y') with hlt | heq | hgt
  · linarith [tri_le_of_le hlt, @g_ubound x y, @g_lbound x' y']
  · exact heq
  · linarith [tri_le_of_le hgt, @g_ubound x' y', @g_lbound x y]

lemma exists_tri_bound (z : ℕ) :
    ∃ n : ℕ, tri n ≤ z ∧ z < tri (n + 1) := by
  induction z with
  | zero => grind [tri]
  | succ z ih => grind [tri]
```

Finally we prove that $`g` is an isomorphism of sets.

```savedLean
example : IsIso g := by
  apply (isIso_iff_bijective g).mpr
  constructor
  · show Function.Injective g
    intro ⟨x, y⟩ ⟨x', y'⟩ h
    grind [g, eq_of_g_eq]
  · show Function.Surjective g
    intro z
    rcases exists_tri_bound z with ⟨w, _, _⟩
    use (w - (z - tri w), z - tri w)
    grind [g, tri]
```

The final part of the exercise asks us to show that no isomorphism $`{\mathbb{N} \xrightarrow{f} \mathbb{N} \times \mathbb{N}}` can have a polynomial as its first component function $`f_1`.

In the proof below, we assume that such a polynomial $`P` exists and derive a contradiction. Since $`f` is an isomorphism and hence bijective, it maps infinitely many inputs to pairs starting with any given integer $`k`. Therefore $`P` must also evaluate to $`k` infinitely many times. However, a non-constant polynomial can only have a finite number of roots, meaning $`P` must be the constant polynomial $`{P(x) = k}` for any $`k`. Hence $`P` is forced to be simultaneously the constant polynomial $`0` and the constant polynomial $`1`, yielding the impossible result that $`{0 = 1}`.

```savedLean
open Polynomial in
example (f : ℕ ⟶ ℕ × ℕ) [IsIso f] :
    ¬∃ P : ℤ[X], ∀ n : ℕ, P.eval (n : ℤ) = (f n).1 := by
  -- Convert isomorphism f to equivalence f'
  let f' : ℕ ≃ ℕ × ℕ := Iso.toEquiv (asIso f)
  -- Provide translation for grind
  have : ∀ n : ℕ, f n = f' n := fun _ ↦ rfl
  intro ⟨P, hP⟩
  -- Show polynomial P must equal constant polynomial C k for any k
  have h_P_eq_C (k : ℕ) : P = C (k : ℤ) := by
    -- Equate preimage of set {k} × ℕ to roots of P = k
    have h_eq : f' ⁻¹' {p : ℕ × ℕ | (p.1 : ℤ) = k} =
        {n : ℕ | P.eval (n : ℤ) = k} := by
      grind
    -- Register type class 'Infinite' for set {k} × ℕ
    have : Infinite {p : ℕ × ℕ | (p.1 : ℤ) = k} := by
      apply Infinite.of_injective (fun n : ℕ ↦ ⟨(k, n), rfl⟩)
      grind [Function.Injective]
    -- Prove there are infinitely many inputs where P evaluates to k
    have h_infinite : Infinite {n : ℕ | P.eval (n : ℤ) = k} := by
      rw [← h_eq]
      apply Infinite.of_injective
          (fun s : {p : ℕ × ℕ | (p.1 : ℤ) = k} ↦
              ⟨f'.symm s.val, by grind⟩)
      grind [Function.Injective]
    -- Assume towards a contradiction that P does not equal C k
    by_contra hc
    -- Map infinite inputs injectively to finite roots of P = k
    let toRoots : {n : ℕ | P.eval (n : ℤ) = k} →
        (P - C (k : ℤ)).roots.toFinset := fun z ↦
            ⟨z.val, by grind [mem_roots, IsRoot, eval_sub, eval_C]⟩
    -- Set up contradiction by showing our set is finite
    have h_fin : Finite {n : ℕ | P.eval (n : ℤ) = k} :=
      Finite.of_injective toRoots (by grind [Function.Injective])
    -- and also not finite
    have h_not_fin : ¬Finite {n : ℕ | P.eval (n : ℤ) = k} :=
      not_finite_iff_infinite.mpr h_infinite
    contradiction
  -- Conclude P must equal both 0 and 1, forcing 0 = 1
  have hC : (C 0 : ℤ[X]) = C 1 :=
    (h_P_eq_C 0).symm.trans (h_P_eq_C 1)
  exact zero_ne_one (C_inj.mp hC)
```

```savedLean -show
end Ex27_4
```
:::

# 4. Solving equations and picturing maps

:::definition (definitionTerm := "Equalizer") (definitionPage := "292")
$`{E \xrightarrow{p} X}` is an _equalizer_ of $`{f, g}` if $`{fp = gp}` and for each $`{T \xrightarrow{x} X}` for which $`{fx = gx}`, there is exactly one $`{T \xrightarrow{e} E}` for which $`{x = pe}`.
:::

In mathlib, two parallel morphisms $`f` and $`g` are given by the diagram `parallelPair f g`. A cone over `parallelPair f g` is aliased as `Fork f g`. If that fork is a limit cone, then we have an equalizer of $`{f, g}`. We print the definitions of `HasEqualizer`, `parallelPair`, and `Fork` below for reference.

```lean (name := out_HasEqualizer)
#print HasEqualizer
```

```leanOutput out_HasEqualizer
@[reducible] def CategoryTheory.Limits.HasEqualizer.{v, u} : {C : Type u} →
  [inst : Category.{v, u} C] → {X Y : C} → (X ⟶ Y) → (X ⟶ Y) → Prop :=
fun {C} [Category.{v, u} C] {X Y} f g ↦ HasLimit (parallelPair f g)
```

```lean (name := out_parallelPair)
#check parallelPair
```

```leanOutput out_parallelPair
CategoryTheory.Limits.parallelPair.{v, u} {C : Type u} [Category.{v, u} C] {X Y : C} (f g : X ⟶ Y) :
  WalkingParallelPair ⥤ C
```

```lean (name := out_Fork)
#print Fork
```

```leanOutput out_Fork
@[reducible] def CategoryTheory.Limits.Fork.{v, u} : {C : Type u} →
  [inst : Category.{v, u} C] → {X Y : C} → (X ⟶ Y) → (X ⟶ Y) → Type (max (max 0 u) v) :=
fun {C} [Category.{v, u} C] {X Y} f g ↦ Cone (parallelPair f g)
```

:::question (questionTitle := "Exercise 5") (questionPage := "293")
If both $`{E, p}` and $`{F, q}` are equalizers for the same pair $`{f, g}`, then the unique map $`{F \xrightarrow{e} E}` for which $`{pe = q}` is an isomorphism.
:::

:::solution (solutionTo := "Exercise 5")
```savedComment
Exercise 27.5 (p. 293)
```

Using Mathlib's canonical `equalizer f g` function would make both $`{E, p}` and $`{F, q}` into the exact same chosen object, reducing the exercise to a triviality about the identity morphism. To preserve the purpose of the exercise, which is to compare two independent equalizers, our proof uses the book definition directly.

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (X Y : 𝒞) (f g : X ⟶ Y) (E F : 𝒞)
    (p : E ⟶ X) (hp₁ : f ⊚ p = g ⊚ p)
    (hp₂ : ∀ (T : 𝒞) (x : T ⟶ X), f ⊚ x = g ⊚ x →
        ∃! e : T ⟶ E, x = p ⊚ e)
    (q : F ⟶ X) (hq₁ : f ⊚ q = g ⊚ q)
    (hq₂ : ∀ (T : 𝒞) (x : T ⟶ X), f ⊚ x = g ⊚ x →
        ∃! e : T ⟶ F, x = q ⊚ e) :
    ∃ e : F ≅ E, p ⊚ e.hom = q := by
  obtain ⟨e, he_comm, _⟩ := hp₂ F q hq₁
  obtain ⟨e_inv, he_inv_comm, _⟩ := hq₂ E p hp₁
  obtain ⟨_, _, hE_uniq⟩ := hp₂ E p hp₁
  have hE₁ := hE_uniq (𝟙 E) (Category.id_comp p).symm
  have hE₂ := hE_uniq (e ⊚ e_inv)
      (by dsimp; rw [Category.assoc, ← he_comm, ← he_inv_comm])
  obtain ⟨_, _, hF_uniq⟩ := hq₂ F q hq₁
  have hF₁ := hF_uniq (𝟙 F) (Category.id_comp q).symm
  have hF₂ := hF_uniq (e_inv ⊚ e)
      (by dsimp; rw [Category.assoc, ← he_inv_comm, ← he_comm])
  use {
    hom := e
    inv := e_inv
    hom_inv_id := by rw [hF₂, ← hF₁]
    inv_hom_id := by rw [hE₂, ← hE₁]
  }
  exact he_comm.symm
```
:::

:::question (questionTitle := "Exercise 6") (questionPage := "293")
Any map $`p` which is an equalizer of some pair of maps is itself a monomorphism (i.e. injective).
:::

:::solution (solutionTo := "Exercise 6")
```savedComment
Exercise 27.6 (p. 293)
```

Using the book definition of equalizer, we have

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (X Y : 𝒞) (f g : X ⟶ Y) (E : 𝒞)
    (p : E ⟶ X) (hp₁ : f ⊚ p = g ⊚ p)
    (hp₂ : ∀ (T : 𝒞) (x : T ⟶ X), f ⊚ x = g ⊚ x →
        ∃! e : T ⟶ E, x = p ⊚ e) :
    Mono p := by
  constructor
  intro T e₁ e₂ h_eq₁
  have h_eq₂ : f ⊚ p ⊚ e₁ = g ⊚ p ⊚ e₁ := by
    rw [Category.assoc, hp₁, ← Category.assoc]
  obtain ⟨_, _, h_uniq⟩ := hp₂ T (p ⊚ e₁) h_eq₂
  exact (h_uniq e₁ rfl).trans (h_uniq e₂ h_eq₁).symm
```

Alternatively, using mathlib's `HasEqualizer` type class and the `equalizer.hom_ext` theorem yields a more concise proof.

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (X Y : 𝒞) (f g : X ⟶ Y) [HasEqualizer f g] :
    Mono (equalizer.ι f g) := by
  let p : equalizer f g ⟶ X := equalizer.ι f g
  constructor
  intro T e₁ e₂ h_eq
  exact equalizer.hom_ext h_eq
```
:::

:::question (questionTitle := "Exercise 7") (questionPage := "293")
If $`{B \xrightarrow{\alpha} A \xrightarrow{\beta} B}` compose to the identity $`{1_B = \beta\alpha}` and if $`f` is the idempotent $`\alpha\beta`, then $`\alpha` is an equalizer for the pair $`{f, 1_A}`.
:::

:::solution (solutionTo := "Exercise 7")
```savedComment
Exercise 27.7 (p. 293)
```

Using the book definition of equalizer, we have

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (A B : 𝒞) (α : B ⟶ A) (β : A ⟶ B)
    (h_idB : 𝟙 B = β ⊚ α) (f : A ⟶ A) (hf : f = α ⊚ β) :
    f ⊚ α = 𝟙 A ⊚ α ∧
    ∀ (T : 𝒞) (x : T ⟶ A), f ⊚ x = 𝟙 A ⊚ x →
        ∃! e : T ⟶ B, x = α ⊚ e := by
  constructor
  · rw [hf, ← Category.assoc, ← h_idB, Category.id_comp,
        Category.comp_id]
  · intro T x hx
    use β ⊚ x
    constructor
    · dsimp
      rw [Category.assoc, ← hf, hx, Category.comp_id]
    · intro y hy
      rw [hy, Category.assoc, ← h_idB, Category.comp_id]
```

Using the mathlib API, we have

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (A B : 𝒞) (α : B ⟶ A) (β : A ⟶ B)
    (h_idB : 𝟙 B = β ⊚ α) (f : A ⟶ A) (hf : f = α ⊚ β) :
    ∃ (w : f ⊚ α = 𝟙 A ⊚ α),
        Nonempty (IsLimit (Fork.ofι α w)) := by
  have w : f ⊚ α = 𝟙 A ⊚ α := by
    rw [hf, ← Category.assoc, ← h_idB, Category.id_comp,
        Category.comp_id]
  use w
  constructor
  refine Fork.IsLimit.mk (Fork.ofι α w) (fun s ↦ β ⊚ s.ι) ?_ ?_
  · -- fac
    intro s
    dsimp
    rw [Category.assoc, ← hf, s.condition, Category.comp_id]
  · -- uniq
    intro s m hm
    dsimp
    erw [← hm, Category.assoc, ← h_idB, Category.comp_id]
```
:::

:::question (questionTitle := "Exercise 8") (questionPage := "293")
Any parallel pair $`{X \xrightarrow{f} Y}`, $`{X \xrightarrow{g} Y}` of maps in sets, no matter how or why it occurred to us in the first place, can always be imagined as the source and target structure of a graph. In a graph, which are the arrows that are named by the equalizer of the source and target maps?
:::

:::solution (solutionTo := "Exercise 8")
```savedComment
Exercise 27.8 (p. 293)
```

In this analogy, the set $`X` represents the arrows of the graph, and the set $`Y` represents the dots. The functions $`f` and $`g` represent the source and target maps. The equalizer of $`{f, g}` is then the subset of elements $`{x \in X}` such that $`{f(x) = g(x)}`, which corresponds to the arrows whose source and target are the same dot. Therefore the arrows named by the equalizer are exactly the self-loops of the graph.

We formalise the proof of this statement below. Instead of using a subset, however, we represent the equalizer as a type $`E` and a morphism $`p` from $`E` to the arrows of the graph, and we assume that $`p` equalizes the source and target maps and satisfies the universal property of a limit.

```savedLean
example (G : IrreflexiveGraph) (E : Type) (p : E ⟶ G.carrierA)
    (w : G.toSrc ⊚ p = G.toTgt ⊚ p)
    (t : IsLimit (Fork.ofι p w)) :
    ∀ a : G.carrierA, (∃ x : E, p x = a) ↔
        G.toSrc a = G.toTgt a := by
  intro a
  constructor
  · rintro ⟨x, rfl⟩
    exact congr_fun w x
  · intro ha
    -- Convert a : G.carrierA into a morphism from the terminal object
    let test : Unit ⟶ G.carrierA := fun _ ↦ a
    -- and show that the morphism equalizes the source and target maps
    have h_test : G.toSrc ⊚ test = G.toTgt ⊚ test := by
      funext _
      exact ha
    -- Bundle the morphism into a cone over the parallel pair of maps
    let s := Fork.ofι test h_test
    -- Use the universal property of the limit to get a witness x : E
    use t.lift s ()
    -- Appeal to the factorisation property of the limit
    have h_fac : p ⊚ t.lift s = s.ι :=
      t.fac s WalkingParallelPair.zero
    -- Close the goal by applying Unit.unit to both sides
    exact congr_fun h_fac ()
```
:::

:::question (questionTitle := "Exercise 9") (questionPage := "293")
For any map $`{X \xrightarrow{f} Y}` there is a unique section $`\Gamma` of $`p_X` for which $`{f = p_Y \Gamma}`, namely $`{\Gamma = \langle ?, f \rangle}`.
:::

:::solution (solutionTo := "Exercise 9")
```savedComment
Exercise 27.9 (p. 293)
```

The unique section is $`{\Gamma = \langle 1_X, f \rangle}`.

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (X Y : 𝒞) [HasBinaryProduct X Y] :
    ∀ f : X ⟶ Y,
        ∃! Γ : SplitEpi prod.fst, f = prod.snd ⊚ Γ.section_ := by
  intro f
  use ⟨prod.lift (𝟙 X) f, prod.lift_fst (𝟙 X) f⟩
  constructor
  · exact (prod.lift_snd (𝟙 X) f).symm
  · intro Γ' hf
    ext
    · rw [Γ'.id, prod.lift_fst]
    · rw [prod.lift_snd, hf]
```
:::

:::question (questionTitle := "Exercise 10") (questionPage := "294")
Given two parallel maps $`{X \xrightarrow{f} Y}`, $`{X \xrightarrow{g} Y}` in a category with products (such as 𝑺), consider their graphs $`\Gamma_f` and $`\Gamma_g`. Explain pictorially why the equalizer of $`{f, g}` is isomorphic to the intersection in $`{X \times Y}` of their graphs.
:::

:::solution (solutionTo := "Exercise 10")
```savedComment
Exercise 27.10 (p. 294)
```

We provide two formalisations of the proof that the equalizer of $`{f, g}` is isomorphic to the intersection in $`{X \times Y}` of their graphs. The first proof uses the book definition of equalizer and a manual definition of intersection (since the book has not yet introduced the concept of an intersection). The second uses mathlib's API for equalizers and pullbacks, the latter being how intersections are implemented in mathlib. We have kept the structure of the two proofs essentially the same to aid in undertanding the translation between manual terms and API terms.

The 'manual' proof is as follows:

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (X Y : 𝒞) (f g : X ⟶ Y) [HasBinaryProduct X Y]
    -- Equalizer of f, g
    (E₁ : 𝒞) (p : E₁ ⟶ X) (hp : f ⊚ p = g ⊚ p)
    (lift₁ : ∀ {T : 𝒞} (x : T ⟶ X), f ⊚ x = g ⊚ x → (T ⟶ E₁))
    (fac₁ : ∀ {T : 𝒞} (x : T ⟶ X) (h : f ⊚ x = g ⊚ x),
        p ⊚ lift₁ x h = x)
    (uniq₁ : ∀ {T : 𝒞} (x : T ⟶ X) (h : f ⊚ x = g ⊚ x)
        (m : T ⟶ E₁), p ⊚ m = x → m = lift₁ x h)
    -- Graphs of f and g
    (Γf Γg : SplitEpi prod.fst)
    (hΓf : f = prod.snd ⊚ Γf.section_)
    (hΓg : g = prod.snd ⊚ Γg.section_)
    -- Intersection in X × Y of graphs of f and g
    (E₂ : 𝒞) (u : E₂ ⟶ X) (v : E₂ ⟶ X)
    (h_intersect : Γf.section_ ⊚ u = Γg.section_ ⊚ v)
    (lift₂ : ∀ {T : 𝒞} (u' v' : T ⟶ X),
        Γf.section_ ⊚ u' = Γg.section_ ⊚ v' → (T ⟶ E₂))
    (fac_u₂ : ∀ {T : 𝒞} (u' v' : T ⟶ X)
        (h : Γf.section_ ⊚ u' = Γg.section_ ⊚ v'),
        u ⊚ lift₂ u' v' h = u')
    (_ : ∀ {T : 𝒞} (u' v' : T ⟶ X)
        (h : Γf.section_ ⊚ u' = Γg.section_ ⊚ v'),
        v ⊚ lift₂ u' v' h = v')
    (uniq₂ : ∀ {T : 𝒞} (u' v' : T ⟶ X)
        (h : Γf.section_ ⊚ u' = Γg.section_ ⊚ v') (m : T ⟶ E₂),
        u ⊚ m = u' → v ⊚ m = v' → m = lift₂ u' v' h) :
    E₁ ≅ E₂ := by
  have huv : u = v := by
    calc
      u = 𝟙 X ⊚ u                       := by rw [Category.comp_id]
      _ = (prod.fst ⊚ Γf.section_) ⊚ u := by rw [Γf.id]
      _ = prod.fst ⊚ (Γf.section_ ⊚ u) := by rw [Category.assoc]
      _ = prod.fst ⊚ (Γg.section_ ⊚ v) := by rw [h_intersect]
      _ = (prod.fst ⊚ Γg.section_) ⊚ v := by rw [Category.assoc]
      _ = 𝟙 X ⊚ v                       := by rw [Γg.id]
      _ = v                              := by rw [Category.comp_id]
  have hu_eq : f ⊚ u = g ⊚ u := by
    calc f ⊚ u
      _ = (prod.snd ⊚ Γf.section_) ⊚ u := by rw [hΓf]
      _ = prod.snd ⊚ (Γf.section_ ⊚ u) := by rw [Category.assoc]
      _ = prod.snd ⊚ (Γg.section_ ⊚ v) := by rw [h_intersect]
      _ = (prod.snd ⊚ Γg.section_) ⊚ v := by rw [Category.assoc]
      _ = g ⊚ v                         := by rw [hΓg]
      _ = g ⊚ u                         := by rw [huv]
  let e₂₁_lift := lift₁ u hu_eq
  have he₂₁_fac := fac₁ u hu_eq
  have hp_eq : Γf.section_ ⊚ p = Γg.section_ ⊚ p := by
    apply prod.hom_ext
    · rw [Category.assoc, Γf.id, Category.comp_id]
      rw [Category.assoc, Γg.id, Category.comp_id]
    · rw [Category.assoc, ← hΓf, Category.assoc, ← hΓg, hp]
  let e₁₂_lift := lift₂ p p hp_eq
  have e₁₂_fac_u := fac_u₂ p p hp_eq
  exact {
    hom := e₁₂_lift
    inv := e₂₁_lift
    hom_inv_id := by
      have h : p ⊚ e₂₁_lift ⊚ e₁₂_lift = p := by
        rw [Category.assoc, he₂₁_fac, ← e₁₂_fac_u]
      have h₁ := uniq₁ p hp (𝟙 E₁) (Category.id_comp p)
      have h₂ := uniq₁ p hp (e₂₁_lift ⊚ e₁₂_lift) h
      exact h₂.trans h₁.symm
    inv_hom_id := by
      have hu : u ⊚ e₁₂_lift ⊚ e₂₁_lift = u := by
        rw [Category.assoc, e₁₂_fac_u, ← he₂₁_fac]
      have hv : v ⊚ e₁₂_lift ⊚ e₂₁_lift = v := by
        rw [← huv, hu]
      have h₁ := uniq₂ u v h_intersect (𝟙 E₂) (Category.id_comp u)
          (Category.id_comp v)
      have h₂ := uniq₂ u v h_intersect (e₁₂_lift ⊚ e₂₁_lift) hu hv
      exact h₂.trans h₁.symm
  }
```

The API proof is as follows:

```savedLean
noncomputable example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (X Y : 𝒞) (f g : X ⟶ Y) [HasBinaryProduct X Y]
    -- Equalizer of f, g
    [HasEqualizer f g]
    -- Graphs of f and g
    (Γf Γg : SplitEpi prod.fst)
    (hΓf : f = prod.snd ⊚ Γf.section_)
    (hΓg : g = prod.snd ⊚ Γg.section_)
    -- Intersection in X × Y of graphs of f and g
    [HasPullback Γf.section_ Γg.section_] :
    equalizer f g ≅ pullback Γf.section_ Γg.section_ := by
  let p := equalizer.ι f g
  let u := pullback.fst Γf.section_ Γg.section_
  let v := pullback.snd Γf.section_ Γg.section_
  have huv : u = v := by
   calc
    u = 𝟙 X ⊚ u                       := by rw [Category.comp_id]
    _ = (prod.fst ⊚ Γf.section_) ⊚ u := by rw [Γf.id]
    _ = prod.fst ⊚ (Γf.section_ ⊚ u) := by rw [Category.assoc]
    _ = prod.fst ⊚ (Γg.section_ ⊚ v) := by rw [pullback.condition]
    _ = (prod.fst ⊚ Γg.section_) ⊚ v := by rw [Category.assoc]
    _ = 𝟙 X ⊚ v                       := by rw [Γg.id]
    _ = v                              := by rw [Category.comp_id]
  have hu_eq : f ⊚ u = g ⊚ u := by
   calc f ⊚ u
    _ = (prod.snd ⊚ Γf.section_) ⊚ u := by rw [hΓf]
    _ = prod.snd ⊚ (Γf.section_ ⊚ u) := by rw [Category.assoc]
    _ = prod.snd ⊚ (Γg.section_ ⊚ v) := by rw [pullback.condition]
    _ = (prod.snd ⊚ Γg.section_) ⊚ v := by rw [Category.assoc]
    _ = g ⊚ v                         := by rw [hΓg]
    _ = g ⊚ u                         := by rw [huv]
  have hp_eq : Γf.section_ ⊚ p = Γg.section_ ⊚ p := by
    apply prod.hom_ext
    · rw [Category.assoc, Γf.id, Category.comp_id]
      rw [Category.assoc, Γg.id, Category.comp_id]
    · rw [Category.assoc, ← hΓf, Category.assoc, ← hΓg,
          equalizer.condition]
  exact {
    hom := pullback.lift p p hp_eq
    inv := equalizer.lift u hu_eq
    hom_inv_id := by
      ext
      rw [Category.assoc, equalizer.lift_ι, pullback.lift_fst,
          Category.id_comp]
    inv_hom_id := by
      ext
      · rw [Category.assoc, pullback.lift_fst, equalizer.lift_ι,
            Category.id_comp]
      · rw [Category.assoc, pullback.lift_snd, equalizer.lift_ι,
            huv, Category.id_comp]
  }
```
:::

Between Exercises 10 and 11, the book discusses _cographs_ and _coequalizers_.

To emphasize the duality between graphs and cographs, we first provide a formalisation of graph of $`f` (cf. Exercise 9).

```savedComment
graphOf (pp. 293–294)
```

```savedLean
noncomputable def graphOf {𝒞 : Type u} [Category.{v, u} 𝒞]
    {X Y : 𝒞} [HasBinaryProduct X Y] (f : X ⟶ Y) : X ⟶ X ⨯ Y :=
  prod.lift (𝟙 X) f

lemma graphOf_is_section {𝒞 : Type u} [Category.{v, u} 𝒞]
    {X Y : 𝒞} [HasBinaryProduct X Y] (f : X ⟶ Y) :
    prod.fst ⊚ graphOf f = 𝟙 X :=
  prod.lift_fst (𝟙 X) f

lemma graphOf_commutes {𝒞 : Type u} [Category.{v, u} 𝒞]
    {X Y : 𝒞} [HasBinaryProduct X Y] (f : X ⟶ Y) :
    prod.snd ⊚ graphOf f = f :=
  prod.lift_snd (𝟙 X) f
```

Dualizing the definition of graph of $`f` then gives the following formalisation of cograph of $`g`.

```savedComment
cographOf (p. 294)
```

```savedLean
noncomputable def cographOf {𝒞 : Type u} [Category.{v, u} 𝒞]
    {X Y : 𝒞} [HasBinaryCoproduct X Y] (g : Y ⟶ X) : X ⨿ Y ⟶ X :=
  coprod.desc (𝟙 X) g

lemma cographOf_is_retraction {𝒞 : Type u} [Category.{v, u} 𝒞]
    {X Y : 𝒞} [HasBinaryCoproduct X Y] (g : Y ⟶ X) :
    cographOf g ⊚ coprod.inl = 𝟙 X :=
  coprod.inl_desc (𝟙 X) g

lemma cographOf_commutes {𝒞 : Type u} [Category.{v, u} 𝒞]
    {X Y : 𝒞} [HasBinaryCoproduct X Y] (g : Y ⟶ X) :
    cographOf g ⊚ coprod.inr = g :=
  coprod.inr_desc (𝟙 X) g
```

Similarly, the definition of coequalizer is dual to that of equalizer. That is, $`{X \xrightarrow{q} C}` is a _coequalizer_ of $`{u, v}` if $`{qu = qv}` and for each $`{X \xrightarrow{t} T}` for which $`{tu = tv}`, there is exactly one $`{C \xrightarrow{c} T}` for which $`{t = cq}` (cf. the definition of equalizer above).

In mathlib, two parallel morphisms have a coequalizer if their parallel pair diagram has a colimit. We print the definition of `HasCoequalizer` below for reference.

```lean (name := out_HasCoequalizer)
#print HasCoequalizer
```

```leanOutput out_HasCoequalizer
@[reducible] def CategoryTheory.Limits.HasCoequalizer.{v, u} : {C : Type u} →
  [inst : Category.{v, u} C] → {X Y : C} → (X ⟶ Y) → (X ⟶ Y) → Prop :=
fun {C} [Category.{v, u} C] {X Y} f g ↦ HasColimit (parallelPair f g)
```

:::question (questionTitle := "Exercise 11") (questionPage := "294")
Say that $`{Y \xrightarrow{h} Z}` is a _cosolution_ of the co-equation represented by a given source/target structure $`{X \xrightarrow{f} Y}`, $`{X \xrightarrow{g} Y}` if $`{hf = hg}`. Show that if such a cosolution $`h` is universal, in the sense that any other cosolution $`{Y \xrightarrow{h'} Z'}` can be uniquely expressed as $`{h' = qh}`, then $`h` is an epimorphism. (A universal cosolution is called a _coequalizer_ of the pair $`{f, g}`; in many categories every epimorphism is a coequalizer of some pair.)
:::

:::solution (solutionTo := "Exercise 11")
```savedComment
Exercise 27.11 (p. 294)
```

This exercise is the dual of Exercise 6, so our proof here is essentially the same but with all arrows reversed. Following the approach taken in Exercise 6, we provide formalisations using both the book definition of coequalizer and mathlib's `HasCoequalizer` type class.

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (X Y : 𝒞) (f g : X ⟶ Y) (Z : 𝒞)
    (h : Y ⟶ Z) (hh₁ : h ⊚ f = h ⊚ g)
    (hh₂ : ∀ (Z' : 𝒞) (h' : Y ⟶ Z'), h' ⊚ f = h' ⊚ g →
        ∃! q : Z ⟶ Z', h' = q ⊚ h) :
    Epi h := by
  constructor
  intro Z' q₁ q₂ h_eq₁
  have h_eq₂ : (q₁ ⊚ h) ⊚ f = (q₁ ⊚ h) ⊚ g := by
    rw [← Category.assoc, hh₁, Category.assoc]
  obtain ⟨_, _, h_uniq⟩ := hh₂ Z' (q₁ ⊚ h) h_eq₂
  exact (h_uniq q₁ rfl).trans (h_uniq q₂ h_eq₁).symm

example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (X Y : 𝒞) (f g : X ⟶ Y) [HasCoequalizer f g] :
    Epi (coequalizer.π f g) := by
  let h : Y ⟶ coequalizer f g := coequalizer.π f g
  constructor
  intro Z' q₁ q₂ h_eq
  exact coequalizer.hom_ext h_eq
```
:::

:::question (questionTitle := "Exercise 12") (questionPage := "294")
For a given map $`{Y \xrightarrow{h} Z}`, consider all parallel pairs $`{X \xrightarrow{f} Y}`, $`{X \xrightarrow{g} Y}` (for various $`X`) such that $`{hf = hg}`. Formulate the notion of a universal such; call it $`X_h`. Show that $`{X_h \rightrightarrows Y}` is reflexive, symmetric, transitive, and jointly monomorphic. Here 'reflexive' you know from our discussion of directed graphs, 'symmetric' means there is an involution $`\sigma` of $`X_h` whose right action interchanges the universal $`f` and $`g`. 'Jointly monomorphic' means the map $`{X \rightarrow Y \times Y}` with label $`{\langle f, g \rangle}` is injective. 'Transitivity' involves a trio of test maps $`{T \xrightarrow Y}`. (An STM  reflexive graph is called an _equivalence relation_ on $`Y`; in many categories every equivalence relation arises as the universal $`X_h`, for some $`h`.)
:::

:::solution (solutionTo := "Exercise 12")
```savedComment
Exercise 27.12 (p. 294)
```

We take each of the four properties in turn.

$`{X_h \rightrightarrows Y}` is reflexive:

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (Y Z : 𝒞) (h : Y ⟶ Z)
    (Xh : 𝒞) (f g : Xh ⟶ Y) (_ : h ⊚ f = h ⊚ g)
    (h_univ : ∀ {X : 𝒞} (f' g' : X ⟶ Y), h ⊚ f' = h ⊚ g' →
        ∃! u : X ⟶ Xh, f ⊚ u = f' ∧ g ⊚ u = g') :
    ∃ r : Y ⟶ Xh, f ⊚ r = 𝟙 Y ∧ g ⊚ r = 𝟙 Y := by
  obtain ⟨r, hr_comm, _⟩ := h_univ (𝟙 Y) (𝟙 Y) rfl
  exact ⟨r, hr_comm⟩
```

$`{X_h \rightrightarrows Y}` is symmetric:

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (Y Z : 𝒞) (h : Y ⟶ Z)
    (Xh : 𝒞) (f g : Xh ⟶ Y) (hh : h ⊚ f = h ⊚ g)
    (h_univ : ∀ {X : 𝒞} (f' g' : X ⟶ Y), h ⊚ f' = h ⊚ g' →
        ∃! u : X ⟶ Xh, f ⊚ u = f' ∧ g ⊚ u = g') :
    ∃ σ : Xh ⟶ Xh,
        σ ⊚ σ = 𝟙 Xh ∧ f ⊚ σ = g ∧ g ⊚ σ = f := by
  obtain ⟨σ, hσ_comm, _⟩ := h_univ g f hh.symm
  refine ⟨σ, ?_, hσ_comm⟩
  obtain ⟨_, _, h_uniq⟩ := h_univ f g hh
  have h1Xh : 𝟙 Xh = _ :=
    h_uniq (𝟙 Xh) ⟨Category.id_comp f, Category.id_comp g⟩
  have hσσ : σ ⊚ σ = _ :=
    h_uniq (σ ⊚ σ) (by
      constructor
      · rw [Category.assoc, hσ_comm.1, hσ_comm.2]
      · rw [Category.assoc, hσ_comm.2, hσ_comm.1])
  exact hσσ.trans h1Xh.symm
```

$`{X_h \rightrightarrows Y}` is transitive:

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (Y Z : 𝒞) (h : Y ⟶ Z)
    (Xh : 𝒞) (f g : Xh ⟶ Y) (hh : h ⊚ f = h ⊚ g)
    (h_univ : ∀ {X : 𝒞} (f' g' : X ⟶ Y), h ⊚ f' = h ⊚ g' →
        ∃! u : X ⟶ Xh, f ⊚ u = f' ∧ g ⊚ u = g') :
    ∀ {T : 𝒞} (y₁ y₂ y₃ : T ⟶ Y) (v₁ v₂ : T ⟶ Xh),
        f ⊚ v₁ = y₁ → g ⊚ v₁ = y₂ → f ⊚ v₂ = y₂ → g ⊚ v₂ = y₃ →
        ∃ v₃ : T ⟶ Xh, f ⊚ v₃ = y₁ ∧ g ⊚ v₃ = y₃ := by
  intro T y₁ y₂ y₃ v₁ v₂ hf₁ hg₁ hf₂ hg₂
  have hy : h ⊚ y₁ = h ⊚ y₃ := calc h ⊚ y₁
    _ = h ⊚ (f ⊚ v₁) := by rw [← hf₁]
    _ = (h ⊚ f) ⊚ v₁ := by rw [Category.assoc]
    _ = (h ⊚ g) ⊚ v₁ := by rw [hh]
    _ = h ⊚ (g ⊚ v₁) := by rw [← Category.assoc]
    _ = h ⊚ y₂        := by rw [hg₁]
    _ = h ⊚ (f ⊚ v₂) := by rw [← hf₂]
    _ = (h ⊚ f) ⊚ v₂ := by rw [Category.assoc]
    _ = (h ⊚ g) ⊚ v₂ := by rw [hh]
    _ = h ⊚ (g ⊚ v₂) := by rw [← Category.assoc]
    _ = h ⊚ y₃        := by rw [hg₂]
  obtain ⟨v₃, _, _⟩ := h_univ (y₁) (y₃) hy
  use v₃
```

$`{X_h \rightrightarrows Y}` is jointly monomorphic:

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (Y Z : 𝒞) [HasBinaryProduct Y Y] (h : Y ⟶ Z)
    (Xh : 𝒞) (f g : Xh ⟶ Y) (hh : h ⊚ f = h ⊚ g)
    (h_univ : ∀ {X : 𝒞} (f' g' : X ⟶ Y), h ⊚ f' = h ⊚ g' →
        ∃! u : X ⟶ Xh, f ⊚ u = f' ∧ g ⊚ u = g') :
    ∀ {T : 𝒞} (a b : T ⟶ Xh),
        prod.lift f g ⊚ a = prod.lift f g ⊚ b → a = b := by
  intro T a b hp_comm
  have hf : f ⊚ a = f ⊚ b := by
    rw [← prod.lift_fst f g, ← Category.assoc, hp_comm,
        Category.assoc]
  have hg : g ⊚ a = g ⊚ b := by
    rw [← prod.lift_snd f g, ← Category.assoc, hp_comm,
        Category.assoc]
  obtain ⟨_, _, h_uniq⟩ := h_univ (f ⊚ a) (g ⊚ a) (by
    rw [Category.assoc, hh, ← Category.assoc])
  have ha := h_uniq a ⟨rfl, rfl⟩
  have hb := h_uniq b ⟨hf.symm, hg.symm⟩
  exact ha.trans hb.symm
```
:::

```savedLean -show
end CM
```

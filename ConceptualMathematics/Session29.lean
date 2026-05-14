import VersoManual
import ConceptualMathematics.Meta.Lean
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory
open Limits


#doc (Manual) "Session 29: Binary operations and diagonal arguments" =>

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

# 2. Cantor's diagonal argument

:::theoremDirective (theoremTitle := "Diagonal Theorem") (theoremPage := "304")
(In any category with products) If $`Y` is an object such that there exists an object $`T` with enough points to parameterize all the maps $`{T \rightarrow Y}` by means of some single map $`{T \times T \xrightarrow{f} Y}`, then $`Y` has the 'fixed point property': every endomap $`{Y \xrightarrow{\alpha} Y}` of $`Y` has at least one point $`{\mathbf{1} \xrightarrow{y} Y}` for which $`{\alpha y = y}`.
:::

:::proof (proofPage := "304–305")
Assume $`Y`, $`T`, $`f`, and $`\alpha` given. Then there is the diagonal map $`{T \rightarrow T \times T}` as always (which maps every element $`t` to $`{\langle t,t \rangle}`), so we can form the three-fold composite $`{g: T \rightarrow Y}`. This new map by its construction satisfies
$$`g(t) = \alpha(f(t,t))`
for every point $`t` of $`T`. We have assumed that _every_ map $`{T \rightarrow Y}` is named as $`{f(-,x)}` for some point $`{\mathbf{1} \xrightarrow{x} T}`, and $`g` is such a map $`{T \rightarrow Y}`. So let $`{x = t_0}` be a parameter value corresponding to our $`g`, i.e. $`{g = f(-,t_0)}`, so that
$$`g(t) = f(t,t_0)`
for all $`t`. Taking the special case $`t = t_0`, we have
$$`g(t_0) = f(t_0,t_0)`
which by the definition of $`g` says
$$`\alpha(f(t_0,t_0)) = f(t_0,t_0)`
or, in other words, that $`{y_0 = f(t_0,t_0)}` defines a point of $`Y` which is fixed by $`\alpha`:
$$`\alpha(y_0) = y_0`
:::

Our implementation in Lean faithfully follows the argument of the book proof given above.

```savedComment
Diagonal Theorem (pp. 304–305)
```

```savedLean
theorem diagonal_theorem {𝒞 : Type u} [Category.{v, u} 𝒞] {T Y : 𝒞}
    [HasBinaryProduct T T] [HasTerminal 𝒞]
    (h : ∃ f : T ⨯ T ⟶ Y, ∀ e : T ⟶ Y, ∃ x : ⊤_ 𝒞 ⟶ T,
        e = f ⊚ prod.lift (𝟙 T) (x ⊚ terminal.from T)) :
    ∀ α : Y ⟶ Y, ∃ y : ⊤_ 𝒞 ⟶ Y, α ⊚ y = y := by
  obtain ⟨f, h'⟩ := h
  intro α
  let g : T ⟶ Y := α ⊚ f ⊚ prod.lift (𝟙 T) (𝟙 T)
  obtain ⟨t₀, hg⟩ := h' g
  have hgt₀ : g ⊚ t₀ = f ⊚ prod.lift t₀ t₀ := by
    have : prod.lift (𝟙 T) (t₀ ⊚ terminal.from T) ⊚ t₀ =
        prod.lift t₀ t₀ := by
      apply prod.hom_ext
      · rw [prod.lift_fst, Category.assoc,
            prod.lift_fst, Category.comp_id]
      · rw [prod.lift_snd, Category.assoc,
            prod.lift_snd, ← Category.assoc]
        nth_rw 3 [← Category.id_comp t₀]
        rw [terminal.hom_ext (terminal.from T ⊚ t₀) (𝟙 (⊤_ 𝒞))]
    rw [hg, ← Category.assoc, this]
  have hα : α ⊚ f ⊚ prod.lift t₀ t₀ = f ⊚ prod.lift t₀ t₀ := by
    have : prod.lift (𝟙 T) (𝟙 T) ⊚ t₀ = prod.lift t₀ t₀ := by
      apply prod.hom_ext
      · rw [prod.lift_fst, Category.assoc,
            prod.lift_fst, Category.comp_id]
      · rw [prod.lift_snd, Category.assoc,
            prod.lift_snd, Category.comp_id]
    nth_rw 2 [← hgt₀]
    dsimp [g]
    rw [← Category.assoc, ← Category.assoc, this]
  set y₀ : ⊤_ 𝒞 ⟶ Y := f ⊚ prod.lift t₀ t₀
  use y₀
```

:::theoremDirective (theoremTitle := "Cantor's Contrapositive Corollary") (theoremPage := "305")
If $`Y` is an object known to have at least one endomap $`\alpha` which has no fixed points, then for every object $`T` and for every attempt $`{f: T \times T \rightarrow Y}` to parameterize maps $`{T \rightarrow Y}` by points of $`T`, there must be at least one map $`{T \rightarrow Y}` which is left out of the family, i.e. does not occur as $`{f(-,x)}` for any point $`x` in $`T`.
:::

:::proof (proofPage := "305")
Use $`\alpha` and the diagonal as above to make $`f` itself produce an example $`g` which $`f` leaves out.
:::

Our implementation in Lean follows the structure of the Diagonal Theorem proof.

```savedComment
Cantor's Contrapositive Corollary (p. 305)
```

```savedLean
theorem cantor's_contrapositive_corollary
    {𝒞 : Type u} [Category.{v, u} 𝒞] {T Y : 𝒞}
    [HasBinaryProduct T T] [HasTerminal 𝒞]
    (h : ∃ α : Y ⟶ Y, ∀ y : ⊤_ 𝒞 ⟶ Y, α ⊚ y ≠ y) :
    ∀ f : T ⨯ T ⟶ Y, ∃ g : T ⟶ Y, ∀ x : ⊤_ 𝒞 ⟶ T,
        g ≠ f ⊚ prod.lift (𝟙 T) (x ⊚ terminal.from T) := by
  obtain ⟨α, h'⟩ := h
  intro f
  let g : T ⟶ Y := α ⊚ f ⊚ prod.lift (𝟙 T) (𝟙 T)
  use g
  intro x hg
  have hgx : g ⊚ x = f ⊚ prod.lift x x := by
    have : prod.lift (𝟙 T) (x ⊚ terminal.from T) ⊚ x =
        prod.lift x x := by
      apply prod.hom_ext
      · rw [prod.lift_fst, Category.assoc,
            prod.lift_fst, Category.comp_id]
      · rw [prod.lift_snd, Category.assoc,
            prod.lift_snd, ← Category.assoc]
        nth_rw 3 [← Category.id_comp x]
        rw [terminal.hom_ext (terminal.from T ⊚ x) (𝟙 (⊤_ 𝒞))]
    rw [hg, ← Category.assoc, this]
  have hα : α ⊚ f ⊚ prod.lift x x = f ⊚ prod.lift x x := by
    have : prod.lift (𝟙 T) (𝟙 T) ⊚ x = prod.lift x x := by
      apply prod.hom_ext
      · rw [prod.lift_fst, Category.assoc,
            prod.lift_fst, Category.comp_id]
      · rw [prod.lift_snd, Category.assoc,
            prod.lift_snd, Category.comp_id]
    nth_rw 2 [← hgx]
    dsimp [g]
    rw [← Category.assoc, ← Category.assoc, this]
  set y₀ : ⊤_ 𝒞 ⟶ Y := f ⊚ prod.lift x x
  apply h' y₀
  exact hα
```

:::question (questionTitle := "Exercise 1") (questionPage := "306")
Cantor's proof, if you read it carefully, really tells us a bit more. Rewrite the proof to show that if $`{T \times T \xrightarrow{f} Y}` _weakly_ parameterizes all maps $`{T \rightarrow Y}`, then $`Y` has the fixed point property. To say that $`{T \times T \xrightarrow{f} Y}` 'weakly' parameterizes all maps $`{T \rightarrow Y}` means that for each $`{T \xrightarrow{g} Y}` there is a point $`{\mathbf{1} \xrightarrow{x} X}` such that (letting $`\xi` stand for the map whose components are the identity and the constant map with value $`x`) the composite map $`{h = f \circ \xi}`
$$`T \xrightarrow{\xi} T \times T \xrightarrow{f} Y`
agrees with $`{T \xrightarrow{g} Y}` on points; i.e. for each point $`{\mathbf{1} \xrightarrow{t} T}`, $`{g \circ t = h \circ t}`. (In the category of sets that says $`{g = h}`; but as we have seen, in other categories it says much less.)
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise 29.1 (p. 306)
```

cf. Our formalisation of the Diagonal Theorem above.

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] {T Y : 𝒞}
    [HasBinaryProduct T T] [HasTerminal 𝒞]
    (h : ∃ f : T ⨯ T ⟶ Y, ∀ e : T ⟶ Y, ∃ x : ⊤_ 𝒞 ⟶ T,
        ∀ t : ⊤_ 𝒞 ⟶ T,
        e ⊚ t = f ⊚ prod.lift (𝟙 T) (x ⊚ terminal.from T) ⊚ t) :
    ∀ α : Y ⟶ Y, ∃ y : ⊤_ 𝒞 ⟶ Y, α ⊚ y = y := by
  obtain ⟨f, h'⟩ := h
  intro α
  let g : T ⟶ Y := α ⊚ f ⊚ prod.lift (𝟙 T) (𝟙 T)
  obtain ⟨t₀, hg⟩ := h' g
  have hgt₀ : g ⊚ t₀ = f ⊚ prod.lift t₀ t₀ := by
    have : prod.lift (𝟙 T) (t₀ ⊚ terminal.from T) ⊚ t₀ =
        prod.lift t₀ t₀ := by
      apply prod.hom_ext
      · rw [prod.lift_fst, Category.assoc,
            prod.lift_fst, Category.comp_id]
      · rw [prod.lift_snd, Category.assoc,
            prod.lift_snd, ← Category.assoc]
        nth_rw 3 [← Category.id_comp t₀]
        rw [terminal.hom_ext (terminal.from T ⊚ t₀) (𝟙 (⊤_ 𝒞))]
    rw [hg t₀, this]
  have hα : α ⊚ f ⊚ prod.lift t₀ t₀ = f ⊚ prod.lift t₀ t₀ := by
    have : prod.lift (𝟙 T) (𝟙 T) ⊚ t₀ = prod.lift t₀ t₀ := by
      apply prod.hom_ext
      · rw [prod.lift_fst, Category.assoc,
            prod.lift_fst, Category.comp_id]
      · rw [prod.lift_snd, Category.assoc,
            prod.lift_snd, Category.comp_id]
    nth_rw 2 [← hgt₀]
    dsimp [g]
    rw [← Category.assoc, ← Category.assoc, this]
  set y₀ : ⊤_ 𝒞 ⟶ Y := f ⊚ prod.lift t₀ t₀
  use y₀
```
:::

```savedLean -show
end CM
```

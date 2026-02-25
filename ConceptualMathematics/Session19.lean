import VersoManual
import ConceptualMathematics.Meta.Lean
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory
open Limits


#doc (Manual) "Session 19: Terminal objects" =>

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

:::definition (definitionTerm := "Terminal object") (definitionPage := "226")
In any category 𝒞, an object $`T` is a _terminal object_ if and only if it has the property: for each object $`X` in 𝒞 there is exactly one map from $`X` to $`T`.
:::

See the earlier definition of _terminal object_ on p. 213.

:::theoremDirective (theoremTitle := "Theorem") (theoremPage := "229")
Suppose that 𝒞 is any category and that both $`T_1` and $`T_2` are terminal objects in 𝒞. Then $`T_1` and $`T_2` are isomorphic; i.e. there are maps $`{f : T_1 \rightarrow T_2}`, $`{g : T_2 \rightarrow T_1}` such that $`{g \circ f}` is the identity of $`T_1` and $`{f \circ g}` is the identity of $`T_2`.
:::

:::proof (proofPage := "229")
To show that $`T_1` and $`T_2` are isomorphic we need first of all a map $`{T_1 \rightarrow T_2}`. Because $`T_2` is terminal there is a map $`{f : T_1 \rightarrow T_2}`. We need a map $`{g : T_2 \rightarrow T_1}`. Again there is one because $`T_1` is terminal. But this does not prove yet that $`T_1` is isomorphic to $`T_2`. These two maps have to be proved to be inverse to each other. Because $`T_1` is terminal, there is only one map from $`T_1` to $`T_1`. Therefore, $`{g \circ f = 1_{T_1}}`. \[Because $`T_2` is terminal, there is only one map from $`T_2` to $`T_2`. Therefore, $`{f \circ g = 1_{T_2}}`.\]
:::

We provided a proof of this theorem in Article IV using the mathlib API for terminal objects. We repeat that proof here, but this time using only the book definition.

```savedComment
Theorem (p. 229)
```

```savedLean
theorem uniqueness_of_terminal_objects'
    {𝒞 : Type u} [Category.{v, u} 𝒞] {T₁ T₂ : 𝒞}
    (hT₁ : ∀ X : 𝒞, (∃ f : X ⟶ T₁, (∀ f' : X ⟶ T₁, f = f')))
    (hT₂ : ∀ X : 𝒞, (∃ f : X ⟶ T₂, (∀ f' : X ⟶ T₂, f = f')))
    : Nonempty (T₁ ≅ T₂) := by
  let f : T₁ ⟶ T₂ := hT₂ T₁ |> Classical.choose
  let g : T₂ ⟶ T₁ := hT₁ T₂ |> Classical.choose
  have hgf : g ⊚ f = 𝟙 T₁ := by
    obtain ⟨t₁, ht₁⟩ := hT₁ T₁
    rw [← ht₁ (g ⊚ f), ← ht₁ (𝟙 T₁)]
  have hfg : f ⊚ g = 𝟙 T₂ := by
    obtain ⟨t₂, ht₂⟩ := hT₂ T₂
    rw [← ht₂ (f ⊚ g), ← ht₂ (𝟙 T₂)]
  apply Nonempty.intro
  exact {
    hom := f
    inv := g
    hom_inv_id := hgf
    inv_hom_id := hfg
  }
```

```savedLean -show
end CM
```

import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article2
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory

set_option linter.unusedFintypeInType false


#doc (Manual) "Summary: On the equation p ∘ j = 1A" =>

%%%
htmlSplit := .never
number := false
%%%

```savedImport
import ConceptualMathematics.Article2
import Mathlib
open CategoryTheory
set_option linter.unusedFintypeInType false
```

```savedLean -show
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

:::excerpt (excerptPage := "117")
If maps $`{A \xrightarrow{j} X \xrightarrow{p} A}` satisfy $`{p \circ j = 1_A}`, several _consequences_ follow:
:::

:::excerpt (excerptPage := "117")
In _any_ category
:::

```savedLean -show
namespace AnyCategory
```

```lean -show
set_option linter.unusedVariables false
```

```savedLean
variable {𝒞 : Type u} [Category.{v, u} 𝒞] {A X : 𝒞}
         {j : A ⟶ X} {p : X ⟶ A}
```

:::excerpt (excerptPage := "117")
The endomap $`{X \xrightarrow{j \circ p} X}` (call it '$`\alpha`' for short) satisfies $`{\alpha \circ \alpha = \alpha}`; we say $`\alpha` is _idempotent_. Written out in full, this is $`{(j \circ p) \circ (j \circ p) = (j \circ p)}`.
:::

```savedComment
idempotent
```

```savedLean
example (hpj : p ⊚ j = 𝟙 A) : (j ⊚ p) ⊚ (j ⊚ p) = (j ⊚ p) := by
  set α := j ⊚ p
  show α ⊚ α = α
  rw [Category.assoc, ← Category.assoc j, hpj, Category.id_comp]
```

```savedLean -show
end AnyCategory
```

:::excerpt (excerptPage := "117")
In the category of _finite sets_
:::

```savedLean -show
namespace CM_Fintype
```

We use `Fintype`s instead of finite sets.

```lean -show
set_option linter.unusedVariables false
```

```savedLean
variable {A X : Type u} [Fintype A] [Fintype X] {j : A ⟶ X} {p : X ⟶ A}
```

:::excerpt (excerptPage := "117")
(1) $`p` satisfies: for each member $`a` of $`A`, there is at least one member $`x` of $`X` for which $`{p(x) = a}`; (We say $`p` is _surjective_.)
:::

```savedComment
Function.Surjective
```

```savedLean
example (hpj : p ⊚ j = 𝟙 A) : ∀ a : A, ∃ x : X, p x = a := by
  intro a
  use j a
  rw [← types_comp_apply j p, hpj]
  rfl
```

A morphism with this property in the category `Type` (and also in the category of sets) is a surjective function, defined in mathlib as `Function.Surjective`, which we print below for reference.

```lean (name := out_Function_Surjective)
#print Function.Surjective
```

```leanOutput out_Function_Surjective
def Function.Surjective.{u_1, u_2} : {α : Sort u_1} → {β : Sort u_2} → (α → β) → Prop :=
fun {α} {β} f ↦ ∀ (b : β), ∃ a, f a = b
```

Hence we can restate our proof of (1) above as

```savedLean
example (hpj : p ⊚ j = 𝟙 A) : Function.Surjective p := by
  intro a
  use j a
  rw [← types_comp_apply j p, hpj]
  rfl
```

The mathlib theorem `epi_iff_surjective` is also relevant here.

```savedComment
epi_iff_surjective
```

```savedLean
example {X Y : Type u} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f :=
  epi_iff_surjective f
```

:::excerpt (excerptPage := "117")
(2) $`j` satisfies: if $`{j(a_1) = j(a_2)}`, then $`{a_1 = a_2}`; (We say j is _injective_.)
:::

```savedComment
Function.Injective
```

```savedLean
example (hpj : p ⊚ j = 𝟙 A) : ∀ a₁ a₂ : A, j a₁ = j a₂ → a₁ = a₂ := by
  intro a₁ a₂ h
  calc a₁
    _ = 𝟙 A a₁ := rfl
    _ = (p ⊚ j) a₁ := by rw [← hpj]
    _ = p (j a₁) := rfl
    _ = p (j a₂) := by rw [h]
    _ = (p ⊚ j) a₂ := rfl
    _ = 𝟙 A a₂ := by rw [hpj]
    _ = a₂ := rfl
```

A morphism with this property in the category `Type` (and also in the category of sets) is an injective function, defined in mathlib as `Function.Injective`, which we print below for reference.

```lean (name := out_Function_Injective)
#print Function.Injective
```

```leanOutput out_Function_Injective
def Function.Injective.{u_1, u_2} : {α : Sort u_1} → {β : Sort u_2} → (α → β) → Prop :=
fun {α} {β} f ↦ ∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂
```

Hence we can restate our proof of (2) above as

```savedLean
example (hpj : p ⊚ j = 𝟙 A) : Function.Injective j := by
  intro a₁ a₂ h
  calc a₁
    _ = 𝟙 A a₁ := rfl
    _ = (p ⊚ j) a₁ := by rw [← hpj]
    _ = p (j a₁) := rfl
    _ = p (j a₂) := by rw [h]
    _ = (p ⊚ j) a₂ := rfl
    _ = 𝟙 A a₂ := by rw [hpj]
    _ = a₂ := rfl
```

The mathlib theorem `mono_iff_injective` is also relevant here.

```savedComment
mono_iff_injective
```

```savedLean
example {X Y : Type u} (f : X ⟶ Y) : Mono f ↔ Function.Injective f :=
  mono_iff_injective f
```

:::excerpt (excerptPage := "117")
(3) $`{\#A \le \#X}`, and if $`{\#A = 0}`, then $`{\#X = 0}` too!
:::

The key step in our proof below that $`{\#A \le \#X}` is provided by the mathlib theorem `Cardinal.mk_le_of_surjective`, which states that the number of elements of the codomain of a surjective function is less than or equal to the number of elements of its domain, as follows:

```savedComment
Cardinal.mk_le_of_surjective, Cardinal.mk_le_of_injective
```

```savedLean
example {α β : Type u} {f : α → β} (hf_surj : Function.Surjective f)
    : Cardinal.mk β ≤ Cardinal.mk α :=
  Cardinal.mk_le_of_surjective hf_surj
```

Hence our proof is

```savedLean
open Cardinal in
example (hpj : p ⊚ j = 𝟙 A) : #A ≤ #X := by
  have hp₁ : Section p := { section_ := j }
  have hp₂ : Epi p := hp₁.epi
  have hp₃ : Function.Surjective p := (epi_iff_surjective p).mp hp₂
  exact mk_le_of_surjective hp₃
```

or, alternatively, using the counterpart mathlib theorem `Cardinal.mk_le_of_injective`,

```savedLean
open Cardinal in
example (hpj : p ⊚ j = 𝟙 A) : #A ≤ #X := by
  have hj₁ : Retraction j := { retraction := p }
  have hj₂ : Mono j := hj₁.mono
  have hj₃ : Function.Injective j := (mono_iff_injective j).mp hj₂
  exact mk_le_of_injective hj₃
```

For the second part of (3) — that is, if $`{\#A = 0}`, then $`{\#X = 0}` — we first define the following lemma:

```savedComment
h_cardinal_zero_eq_zero_iff
```

```savedLean
open Cardinal in
theorem h_cardinal_zero_eq_zero_iff {α : Type u} [Fintype α]
    : #α = 0 ↔ IsEmpty α := by
  rw [mk_fintype]
  norm_cast
  exact Fintype.card_eq_zero_iff
```

We can then proceed as below. (Note that the primary assumption $`{p \circ j = 1_A}` is not required here, since any $`p` that maps to an empty codomain must have an empty domain.)

```savedLean
open Cardinal in
example (_ : p ⊚ j = 𝟙 A) : #A = 0 → #X = 0 := by
  repeat rw [h_cardinal_zero_eq_zero_iff]
  intro hA
  apply IsEmpty.mk
  intro x
  exact hA.false (p x)
```

```savedLean -show
end CM_Fintype
```

```savedLean -show
end CM
```

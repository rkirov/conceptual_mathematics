import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article3
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "Test 2" =>

%%%
htmlSplit := .never
number := false
%%%

```savedImport
import ConceptualMathematics.Article3
import Mathlib
open CategoryTheory
```

```savedLean -show
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

:::question (questionTitle := "Problem 1") (questionPage := "204")
Suppose
$$`X^{↻\alpha} \xrightarrow{f} Y^{↻\beta}`
is a map in 𝑺↻. Show that if $`\alpha` has a fixed point, then $`\beta` must also have a fixed point.
:::

:::solution (solutionTo := "Problem 1")
```savedComment
Problem Test 2.1 (p. 204)
```

The sequence of rewrites in the example below mirrors Danilo's solution on p. 205.

```savedLean
example (X Y : SetWithEndomap) (f : X ⟶ Y) :
    (∃ x : X.carrier, X.toEnd x = x) →
    (∃ y : Y.carrier, Y.toEnd y = y) := by
  obtain ⟨f, hf_comm⟩ := f
  intro ⟨x, hα⟩
  use f x
  rw [← types_comp_apply _ Y.toEnd, ← hf_comm, types_comp_apply, hα]
```
:::

:::question (questionTitle := "Problem 2") (questionPage := "204")
```savedComment
Problem Test 2.2 (p. 204)
```

```savedLean -show
namespace Test2_2
```

Find all maps of (irreflexive) graphs from

```savedLean
inductive A₁
  | a | b

inductive D₁
  | p | q | r

def G₁ : IrreflexiveGraph := {
  carrierA := A₁
  carrierD := D₁
  toSrc := fun
    | A₁.a => D₁.p
    | A₁.b => D₁.q
  toTgt := fun
    | A₁.a => D₁.r
    | A₁.b => D₁.r
}
```

to

```savedLean
inductive A₂
  | c | d

inductive D₂
  | v | w

def G₂ : IrreflexiveGraph := {
  carrierA := A₂
  carrierD := D₂
  toSrc := fun
    | A₂.c => D₂.w
    | A₂.d => D₂.v
  toTgt := fun
    | A₂.c => D₂.w
    | A₂.d => D₂.w
}
```

(There are not more than a half-dozen of them.)
:::

:::solution (solutionTo := "Problem 2")
There are four maps, as given below (cf. the discussion of Omer's solution on pp. 207–210):

```savedLean
def f₁ : G₁ ⟶ G₂ := {
  val := (
    fun -- maps arrows
      | A₁.a => A₂.d
      | A₁.b => A₂.d,
    fun -- maps dots
      | D₁.p => D₂.v
      | D₁.q => D₂.v
      | D₁.r => D₂.w
  )
  property := by
    constructor
    all_goals
      funext x
      cases x <;> rfl
}

def f₂ : G₁ ⟶ G₂ := {
  val := (
    fun -- maps arrows
      | A₁.a => A₂.c
      | A₁.b => A₂.c,
    fun -- maps dots
      | D₁.p => D₂.w
      | D₁.q => D₂.w
      | D₁.r => D₂.w
  )
  property := by
    constructor
    all_goals
      funext x
      cases x <;> rfl
}

def f₃ : G₁ ⟶ G₂ := {
  val := (
    fun -- maps arrows
      | A₁.a => A₂.c
      | A₁.b => A₂.d,
    fun -- maps dots
      | D₁.p => D₂.w
      | D₁.q => D₂.v
      | D₁.r => D₂.w
  )
  property := by
    constructor
    all_goals
      funext x
      cases x <;> rfl
}

def f₄ : G₁ ⟶ G₂ := {
  val := (
    fun -- maps arrows
      | A₁.a => A₂.d
      | A₁.b => A₂.c,
    fun -- maps dots
      | D₁.p => D₂.v
      | D₁.q => D₂.w
      | D₁.r => D₂.w
  )
  property := by
    constructor
    all_goals
      funext x
      cases x <;> rfl
}
```

```savedLean -show
end Test2_2
```
:::

:::question (questionTitle := "Problem 3") (questionPage := "204")
Find an example of a set $`X` and an endomap $`{X \xrightarrow{\alpha} X}` with $`{\alpha^2 = \alpha^3}` but $`{\alpha \neq \alpha^2}`.
:::

:::solution (solutionTo := "Problem 3")
```savedComment
Problem Test 2.3 (p. 204)
```

```savedLean -show
namespace Test2_3
```

cf. the discussion of Katie's attempted solution on pp. 205–207.

```savedLean
inductive X
  | x₁ | x₂ | x₃

def α : End X
  | X.x₁ => X.x₂
  | X.x₂ => X.x₃
  | X.x₃ => X.x₃

example : α ^ 2 = α ^ 3 ∧ α ≠ α ^ 2 := by
  constructor
  · funext x
    cases x <;> rfl
  · by_contra h
    have h_false : α X.x₁ = (α ^ 2) X.x₁ := congrFun h X.x₁
    have hα : α X.x₁ = X.x₂ := rfl
    have hαα : (α ^ 2) X.x₁ = X.x₃ := rfl
    rw [hα, hαα] at h_false
    contradiction
```

In fact, since `hα` and `hαα` just establish definitional equalities, the `contradiction` tactic can take care of the last few steps automatically.

```savedLean
example : α ^ 2 = α ^ 3 ∧ α ≠ α ^ 2 := by
  constructor
  · funext x
    cases x <;> rfl
  · by_contra h
    have h_false : α X.x₁ = (α ^ 2) X.x₁ := congrFun h X.x₁
    -- have hα : α X.x₁ = X.x₂ := rfl
    -- have hαα : (α ^ 2) X.x₁ = X.x₃ := rfl
    -- rw [hα, hαα] at h_false
    contradiction
```

```savedLean -show
end Test2_3
```
:::

```savedLean -show
end CM
```

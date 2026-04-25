import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article4
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory
open Limits


#doc (Manual) "Test 5" =>

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

:::question (questionTitle := "Problem 1") (questionPage := "301")
Find as many graphs with exactly 4 dots and 2 arrows as you can, with no two of your graphs isomorphic. (Draw an internal diagram of each of your graphs.)

```lean
def Example : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 2
  toTgt := fun
    | 0 => 1
    | 1 => 1
}
```

Hint: The number of such graphs is between 10 and 15.
:::

:::solution (solutionTo := "Problem 1")
```savedComment
Problem Test 5.1 (p. 301)
```

```savedLean -show
namespace Test5_1
```

There are 11 such graphs—2 graphs with exactly 2 loops, 3 graphs with exactly one loop, and 6 graphs with no loops. We provide definitions below.

Graphs with exactly 2 loops:

```savedLean
def G₁ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 0
  toTgt := fun
    | 0 => 0
    | 1 => 0
}

def G₂ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 1
  toTgt := fun
    | 0 => 0
    | 1 => 1
}
```

Graphs with exactly 1 loop:

```savedLean
def G₃ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 0
  toTgt := fun
    | 0 => 0
    | 1 => 1
}

def G₄ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 1
  toTgt := fun
    | 0 => 0
    | 1 => 0
}

def G₅ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 1
  toTgt := fun
    | 0 => 0
    | 1 => 2
}
```

Graphs with no loops:

```savedLean
def G₆ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 0
  toTgt := fun
    | 0 => 1
    | 1 => 1
}

def G₇ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 1
  toTgt := fun
    | 0 => 1
    | 1 => 2
}

def G₈ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 2
  toTgt := fun
    | 0 => 1
    | 1 => 3
}

def G₉ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 1
  toTgt := fun
    | 0 => 1
    | 1 => 0
}

def G₁₀ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 0
    | 1 => 2
  toTgt := fun
    | 0 => 1
    | 1 => 1
}

def G₁₁ : IrreflexiveGraph := {
  carrierA := Fin 2
  carrierD := Fin 4
  toSrc := fun
    | 0 => 1
    | 1 => 1
  toTgt := fun
    | 0 => 0
    | 1 => 2
}
```

```savedLean -show
end Test5_1
```
:::

:::question (questionTitle := "Problem 2") (questionPage := "301")
```savedComment
Problem Test 5.2 (p. 301)
```

```lean -show
namespace Test5_2'
```

```lean
abbrev IrreflexiveGraph.D : IrreflexiveGraph := {
  carrierA := Empty
  carrierD := Unit
  toSrc := Empty.elim
  toTgt := Empty.elim
}

abbrev IrreflexiveGraph.A : IrreflexiveGraph := {
  carrierA := Unit
  carrierD := Fin 2
  toSrc := fun _ ↦ 0
  toTgt := fun _ ↦ 1
}
```

```lean -show
end Test5_2'
```

```savedLean -show
namespace Test5_2
```

```savedLean
abbrev I : IrreflexiveGraph := {
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

Find numbers $`a`, $`b`, $`c` such that
$$`I \times I = aD + bA + cI`
Hint: First try to draw $`{I \times I}`

To _check_ your picture, be sure that the two projection maps are _maps of graphs_!
:::

:::solution (solutionTo := "Problem 2")
We can formalise $`{I \times I}` as follows:

```savedLean
abbrev IxI : IrreflexiveGraph := {
  carrierA := Fin 4
  carrierD := Fin 3 × Fin 3
  toSrc := fun
    | 0 => (0, 0)
    | 1 => (0, 1)
    | 2 => (1, 0)
    | 3 => (1, 1)
  toTgt := fun
    | 0 => (1, 1)
    | 1 => (1, 2)
    | 2 => (2, 1)
    | 3 => (2, 2)
}
```

We then find that $`{I \times I}` is isomorphic to the graph $`{2D + 2A + I}`, which we can formalise using Lean's Sigma type (dependent pairs) as follows:

```savedLean
open IrreflexiveGraph

abbrev Fam2D2AI : Fin 5 → IrreflexiveGraph
  | 0 => D
  | 1 => D
  | 2 => A
  | 3 => A
  | 4 => I

def G : IrreflexiveGraph := {
  carrierA := Σ i, (Fam2D2AI i).carrierA
  carrierD := Σ i, (Fam2D2AI i).carrierD
  toSrc := fun ⟨i, a⟩ ↦ ⟨i, (Fam2D2AI i).toSrc a⟩
  toTgt := fun ⟨i, a⟩ ↦ ⟨i, (Fam2D2AI i).toTgt a⟩
}
```

We prove the isomorphism $`{I \times I \cong 2D + 2A + I}` below.

```savedLean
example : IxI ≅ G := {
  hom := ⟨
    (fun
      | 0 => ⟨4, 0⟩
      | 1 => ⟨2, ()⟩
      | 2 => ⟨3, ()⟩
      | 3 => ⟨4, 1⟩,
    fun
      | (0, 0) => ⟨4, 0⟩
      | (0, 1) => ⟨2, 0⟩
      | (0, 2) => ⟨0, ()⟩
      | (1, 0) => ⟨3, 0⟩
      | (1, 1) => ⟨4, 1⟩
      | (1, 2) => ⟨2, 1⟩
      | (2, 0) => ⟨1, ()⟩
      | (2, 1) => ⟨3, 1⟩
      | (2, 2) => ⟨4, 2⟩),
    by
      constructor
      all_goals
        funext a; fin_cases a <;> rfl
  ⟩
  inv := ⟨
    (fun
      | ⟨0, a⟩ => nomatch a
      | ⟨1, a⟩ => nomatch a
      | ⟨2, ()⟩ => 1
      | ⟨3, ()⟩ => 2
      | ⟨4, 0⟩ => 0
      | ⟨4, 1⟩ => 3,
    fun
      | ⟨0, ()⟩ => (0, 2)
      | ⟨1, ()⟩ => (2, 0)
      | ⟨2, 0⟩ => (0, 1)
      | ⟨2, 1⟩ => (1, 2)
      | ⟨3, 0⟩ => (1, 0)
      | ⟨3, 1⟩ => (2, 1)
      | ⟨4, 0⟩ => (0, 0)
      | ⟨4, 1⟩ => (1, 1)
      | ⟨4, 2⟩ => (2, 2)),
    by
      constructor
      all_goals
        funext ⟨i, a⟩
        fin_cases i
        · nomatch a
        · nomatch a
        · rfl
        · rfl
        · fin_cases a <;> rfl
  ⟩
  hom_inv_id := by
    apply hom_ext
    all_goals
      funext x; fin_cases x <;> rfl
  inv_hom_id := by
    apply hom_ext
    · funext ⟨i, a⟩
      fin_cases i
      · nomatch a
      · nomatch a
      · rfl
      · rfl
      · fin_cases a <;> rfl
    · funext ⟨i, d⟩
      fin_cases i
      · rfl
      · rfl
      · fin_cases d <;> rfl
      · fin_cases d <;> rfl
      · fin_cases d <;> rfl
}
```

```savedLean -show
end Test5_2
```
:::

```savedLean -show
end CM
```

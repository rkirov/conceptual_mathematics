import VersoManual
import ConceptualMathematics.Meta.Lean
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory
open Limits


#doc (Manual) "Session 20: Points of an object" =>

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

:::definition (definitionTerm := "Point") (definitionPage := "232")
A _point_ of $`X` is a map $`{T \rightarrow X}` where $`T` is terminal.
:::

See the earlier definition of _point_ on p. 214 (and also cf. the definition of points in sets on p. 19).

```savedLean -show
end CM
```

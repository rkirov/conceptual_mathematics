import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article1
import ConceptualMathematics.Article3
import ConceptualMathematics.Session15
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory
open Limits


#doc (Manual) "Article IV: Universal mapping properties" =>

%%%
htmlSplit := .never
number := false
%%%

```savedImport
import ConceptualMathematics.Article1
import ConceptualMathematics.Article3
import ConceptualMathematics.Session15
import Mathlib
open CategoryTheory
open Limits
```

```savedLean -show
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

# 1. Terminal objects

:::definition (definitionTerm := "Terminal object") (definitionPage := "213")
An object $`S` in a category 𝒞 is said to be a _terminal object_ of 𝒞 if for each object $`X` of 𝒞 there is exactly one 𝒞-map $`{X \rightarrow S}`.
:::

The relevant mathlib definitions here are `HasTerminal` and `IsTerminal`, which we print below for reference.

```lean (name := out_HasTerminal)
#print HasTerminal
```

```leanOutput out_HasTerminal
@[reducible] def CategoryTheory.Limits.HasTerminal.{v₁, u₁} : (C : Type u₁) → [Category.{v₁, u₁} C] → Prop :=
fun C [Category.{v₁, u₁} C] ↦ HasLimitsOfShape (Discrete PEmpty.{1}) C
```

```lean (name := out_IsTerminal)
#print IsTerminal
```

```leanOutput out_IsTerminal
@[reducible] def CategoryTheory.Limits.IsTerminal.{v₁, u₁} : {C : Type u₁} →
  [Category.{v₁, u₁} C] → C → Type (max (max 0 u₁) v₁) :=
fun {C} [Category.{v₁, u₁} C] X ↦ IsLimit (asEmptyCone X)
```

:::theoremDirective (theoremTitle := "Proposition (uniqueness of terminal objects)") (theoremPage := "213")
If $`S_1`, $`S_2` are both terminal objects in the category 𝒞, then there is exactly one 𝒞-map $`{S_1 \rightarrow S_2}`, and that map is a 𝒞-isomorphism.
:::

:::proof (proofPage := "213–214")
Since $`S_2` is terminal, there is for each object $`X` in 𝒞 exactly one 𝒞-map $`{X \rightarrow S_2}`. In particular, for $`{X = S_1}`, there is exactly one $`{S_1 \rightarrow S_2}`. Since $`S_1` is also terminal in 𝒞, there is for each $`Y` in 𝒞 exactly one 𝒞-map $`{Y \rightarrow S_1}`; for example, taking $`{Y = S_2}` we have exactly one 𝒞-map $`{S_2 \rightarrow S_1}`. To complete the proof we show that the latter map $`{S_2 \rightarrow S_1}` is a two-sided inverse for the former map $`{S_1 \rightarrow S_2}`, i.e. that the composites
$$`S_1 \rightarrow S_2 \rightarrow S_1`
$$`S_2 \rightarrow S_1 \rightarrow S_2`
are respectively $`1_{S_1}` and $`1_{S_2}`, the identity maps of these objects. Observe that any terminal object $`S` has the property that the only map $`{S \rightarrow S}` is $`1_S`; for applying the definition a third time with $`{X = S}` itself, we get that there is exactly one map $`{S \rightarrow S}`. Since both $`S_1` and $`S_2` are terminal in 𝒞, we can apply this observation to the case $`{S = S_1}` and then to $`{S = S_2}` to conclude that the composite $`S_1 \rightarrow S_2 \rightarrow S_1` is $`1_{S_1}` and that $`S_2 \rightarrow S_1 \rightarrow S_2` is $`1_{S_2}`. Thus the map $`S_1 \rightarrow S_2` has as inverse the map $`S_2 \rightarrow S_1`, and hence is an isomorphism as claimed.
:::

Our implementation in Lean follows the general outline of the book proof given above.

```savedComment
Proposition (uniqueness of terminal objects) (pp. 213–214)
```

```savedLean
theorem uniqueness_of_terminal_objects
    {𝒞 : Type u} [Category.{v, u} 𝒞] {S₁ S₂ : 𝒞}
    (hS₁ : IsTerminal S₁) (hS₂ : IsTerminal S₂)
    : ∃! s : S₁ ⟶ S₂, IsIso s := by
  let f : S₁ ⟶ S₂ := hS₂.from S₁
  let g : S₂ ⟶ S₁ := hS₁.from S₂
  have h_id₁ : g ⊚ f = 𝟙 S₁ := hS₁.hom_ext _ _
  have h_id₂ : f ⊚ g = 𝟙 S₂ := hS₂.hom_ext _ _
  use f
  constructor
  · exact { out := ⟨g, h_id₁, h_id₂⟩ }
  · intros
    exact hS₂.hom_ext _ _
```

:::definition (definitionTerm := "Point") (definitionPage := "214")
If $`\mathbf{1}` is a terminal object of a category 𝒞 and if $`X` is any object of 𝒞, then a 𝒞-map $`{\mathbf{1} \rightarrow X}` is called a _point_ of $`X`.
:::

cf. the earlier definition of _points_ in sets on p. 19.

:::question (questionTitle := "Exercise 1") (questionPage := "214")
$`\mathbf{1}` has one point. If $`{X \xrightarrow{f} Y}` and $`x` is a point of $`X` then $`fx` is a point of $`Y`.
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise IV.1 (p. 214)
```

The statement is tautological in a formalised category theory context, so the proof here is immediate.

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] {One X Y : 𝒞}
    {_ : IsTerminal One} (_ : Unique (One ⟶ One))
    (f : X ⟶ Y) (x : One ⟶ X)
    : ∃ y : One ⟶ Y, y = f ⊚ x := by
  use f ⊚ x
```
:::

:::question (questionTitle := "Exercise 2") (questionPage := "214")
In the category 𝑺 of abstract sets, each point of $`X` 'points to' exactly one element of $`X` and every element of $`X` is the value of exactly one point of $`X`. (Here $`X` is any given abstract set.)
:::

:::solution (solutionTo := "Exercise 2")
```savedComment
Exercise IV.2 (p. 214)
```

We use types instead of sets here, and we also make use of our earlier implementation of `Point` in Article I (p. 19).

```savedLean
example (X : Type) : (∀ x : Point X, (∃! x' : X, x' = x ())) ∧
                     (∀ x' : X, (∃! x : Point X, x () = x')) := by
  constructor
  · intro x
    use x ()
    dsimp
    constructor
    · rfl
    · intros
      assumption
  · intro x'
    use (fun _ : Unit ↦ x')
    dsimp
    constructor
    · rfl
    · intro x hx
      funext (_ : Unit)
      exact hx
```
:::

:::question (questionTitle := "Exercise 3") (questionPage := "214")
In the category 𝑺↻ of discrete dynamical systems, a point of an object 'is' just a fixed point of the endomap (i.e. an 'equilibrium state' of the dynamical system); thus most states do not correspond to any 𝑺↻-map from the terminal object.
:::

:::solution (solutionTo := "Exercise 3")
```savedComment
Exercise IV.3 (p. 214)
```

We define `termSWE` as a candidate for the terminal object in the category 𝑺↻.

```savedLean
def termSWE : SetWithEndomap := {
  carrier := Unit
  toEnd := id
}
```

We prove that `termSWE` is indeed terminal in 𝑺↻.

```savedLean
example : Nonempty (IsTerminal termSWE) := by
  apply Nonempty.intro
  refine @IsTerminal.ofUnique _ _ termSWE (fun Y ↦ ?_)
  exact {
    default := {
      val := fun _ ↦ ()
      property := rfl
    }
    uniq := by
      intro f
      rfl
  }
```

We show that a point of $`X` is just a fixed point of the endomap.

```savedLean
example : ∀ (X : SetWithEndomap) (x : termSWE ⟶ X),
    X.toEnd (x.val ()) = x.val () := by
  intro X x
  have : X.toEnd ⊚ x.val = x.val ⊚ termSWE.toEnd :=
      x.property.symm
  exact congr_fun this ()
```
:::

:::question (questionTitle := "Exercise 4") (questionPage := "214")
In the category 𝑺⇊ of (irreflexive) graphs, a 'point' of graph $`X` 'is' just any loop in $`X`. Hint: Determine what a terminal object looks like, using the definition of 'map in 𝑺⇊'.
:::

:::solution (solutionTo := "Exercise 4")
```savedComment
Exercise IV.4 (p. 214)
```

We define `termIG` as a candidate for the terminal object in the category 𝑺⇊.

```savedLean
def termIG : IrreflexiveGraph := {
  carrierA := Unit
  carrierD := Unit
  toSrc := fun _ ↦ ()
  toTgt := fun _ ↦ ()
}
```

We prove that `termIG` is indeed terminal in 𝑺⇊.

```savedLean
example : Nonempty (IsTerminal termIG) := by
  apply Nonempty.intro
  refine @IsTerminal.ofUnique _ _ termIG (fun Y ↦ ?_)
  exact {
    default := {
      val := (fun _ ↦ (), fun _ ↦ ())
      property := by
        constructor <;> trivial
    }
    uniq := by
      intro f
      rfl
  }
```

We show that a point of $`X` is just any loop in $`X`.

```savedLean
example : ∀ (X : IrreflexiveGraph) (x : termIG ⟶ X),
    X.toSrc (x.val.1 ()) = X.toTgt (x.val.1 ()) := by
  intro X x
  obtain ⟨hxSrc_comm, hxTgt_comm⟩ := x.property
  have h₁ := congr_fun hxSrc_comm ()
  have h₂ := congr_fun hxTgt_comm ()
  dsimp [termIG] at h₁ h₂
  rw [← h₁, h₂]
```
:::

:::question (questionTitle := "Exercise 5") (questionPage := "214")
The terminal object $`\mathbf{1}` in 𝑺 has the further property of 'separating arbitrary maps'. If $`{X \xrightarrow{f} Y}`, $`{X \xrightarrow{g} Y}` and if for each point $`x` of $`X` we have $`{fx = gx}`, then $`{f = g}`. This further property is NOT true of the terminal object in either 𝑺↻ or 𝑺⇊. Give a counterexample in each.
:::

:::solution (solutionTo := "Exercise 5")
```savedComment
Exercise IV.5 (p. 214)
```

We give a counterexample in 𝑺↻ that is not vacuously true.

```savedLean -show
namespace ExIV_5a
```

```savedLean
inductive X
  | x₁ | x₂

def α : X ⟶ X
  | X.x₁ => X.x₁
  | X.x₂ => X.x₁

def Xα : SetWithEndomap := {
  carrier := X
  toEnd := α
}

inductive Y
  | y₁ | y₂

def β : Y ⟶ Y
  | Y.y₁ => Y.y₁
  | Y.y₂ => Y.y₁

def Yβ : SetWithEndomap := {
  carrier := Y
  toEnd := β
}

def f : Xα ⟶ Yβ := ⟨
  fun
    | X.x₁ => Y.y₁
    | X.x₂ => Y.y₁,
  by
    funext x
    cases x <;> rfl
⟩

def g : Xα ⟶ Yβ := ⟨
  fun
    | X.x₁ => Y.y₁
    | X.x₂ => Y.y₂,
  by
    funext x
    cases x <;> rfl
⟩
```

We have already shown (in Exercise 3) that `termSWE` is terminal in 𝑺↻, so we can now use our counterexample to prove that the property of 'separating arbitrary maps' is not true of the terminal object `termSWE` in 𝑺↻.

```savedLean
example : ¬(∀ x : termSWE ⟶ Xα, f ⊚ x = g ⊚ x → f = g) := by
  push Not
  let x : termSWE ⟶ Xα := ⟨fun _ ↦ X.x₁, rfl⟩
  use x
  constructor
  · rfl
  · by_contra h_eq
    have hf : f.val X.x₂ = Y.y₁ := rfl
    have hg : g.val X.x₂ = Y.y₂ := rfl
    rw [h_eq] at hf
    contradiction
```

```savedLean -show
end ExIV_5a
```

Our counterexample in 𝑺⇊ is a direct translation of our counterexample in 𝑺↻ into the category of graphs.

```savedLean -show
namespace ExIV_5b
```

```savedLean
inductive XA
  | a₁ | a₂

inductive XD
  | d₁ | d₂

def X : IrreflexiveGraph := {
  carrierA := XA
  carrierD := XD
  toSrc := fun
    | XA.a₁ => XD.d₁
    | XA.a₂ => XD.d₂
  toTgt := fun
    | XA.a₁ => XD.d₁
    | XA.a₂ => XD.d₁
}

inductive YA
  | a₁ | a₂

inductive YD
  | d₁ | d₂

def Y : IrreflexiveGraph := {
  carrierA := YA
  carrierD := YD
  toSrc := fun
    | YA.a₁ => YD.d₁
    | YA.a₂ => YD.d₂
  toTgt := fun
    | YA.a₁ => YD.d₁
    | YA.a₂ => YD.d₁
}

def f : X ⟶ Y := ⟨
  (fun _ ↦ YA.a₁, fun _ ↦ YD.d₁),
  by
    constructor
    all_goals
      funext a
      cases a <;> rfl
⟩

def g : X ⟶ Y := ⟨
  (fun
    | XA.a₁ => YA.a₁
    | XA.a₂ => YA.a₂,
   fun
    | XD.d₁ => YD.d₁
    | XD.d₂ => YD.d₂),
  by
    constructor
    all_goals
      funext a
      cases a <;> rfl
⟩
```

We have already shown (in Exercise 4) that `termIG` is terminal in 𝑺⇊, so we can now use our counterexample to prove that the property of 'separating arbitrary maps' is not true of the terminal object `termIG` in 𝑺⇊.

```savedLean
example : ¬(∀ x : termIG ⟶ X, f ⊚ x = g ⊚ x → f = g) := by
  push Not
  let x : termIG ⟶ X := ⟨
    (fun _ ↦ XA.a₁, fun _ ↦ XD.d₁),
    ⟨rfl, rfl⟩
  ⟩
  use x
  constructor
  · rfl
  · by_contra h_eq
    have hf : (f.val.1 XA.a₂) = YA.a₁ := rfl
    have hg : (g.val.1 XA.a₂) = YA.a₂ := rfl
    rw [h_eq] at hf
    contradiction
```

```savedLean -show
end ExIV_5b
```
:::

# 2. Separating

:::excerpt (excerptPage := "215")
```savedComment
Excerpt (p. 215)
```

Consider the two graphs \[$`A`, the generic arrow, and $`D`, the naked dot,\] whose internal pictures are as indicated

```savedLean
def IrreflexiveGraph.A : IrreflexiveGraph := {
  carrierA := Unit
  carrierD := Fin 2
  toSrc := fun _ ↦ 0
  toTgt := fun _ ↦ 1
}

def IrreflexiveGraph.D : IrreflexiveGraph := {
  carrierA := Empty
  carrierD := Unit
  toSrc := Empty.elim
  toTgt := Empty.elim
}
```

Then for any graph $`X`, each arrow in $`X` is indicated by exactly one 𝑺⇊-map $`{A \rightarrow X}` and each dot in $`X` is indicated by exactly one 𝑺⇊-map $`{D \rightarrow X}`. It follows that:

Let $`X`, $`Y` be any two graphs and $`{X \xrightarrow{f} Y}`, $`{X \xrightarrow{g} Y}` any two graph maps. If $`{fx = gx}` for all $`{A \xrightarrow{x} X}` with domain $`A` and also $`{fx = gx}` for all $`{D \xrightarrow{x} X}` with domain $`D`, then $`{f = g}`.
:::

Since morphisms in our implementation of 𝑺⇊ are subtypes of the product of functions ArrowMap × DotMap, two morphisms are equal if their underlying functions are equal. Hence our proof strategy involves constructing a morphism $`{A \xrightarrow{x} X}` that maps the single arrow of $`A` to $`a` and a morphism $`{D \xrightarrow{x} X}` that maps the single dot of $`D` to $`d`, and then using these morphisms to prove equality on ArrowMap and DotMap, respectively.

```savedLean
open IrreflexiveGraph in
example
    (X Y : IrreflexiveGraph)
    (f g : X ⟶ Y)
    (ha : ∀ x : A ⟶ X, f ⊚ x = g ⊚ x)
    (hd : ∀ x : D ⟶ X, f ⊚ x = g ⊚ x)
    : f = g := by
  apply Subtype.ext
  apply Prod.ext
  -- Prove equality on ArrowMap
  · funext a
    let x : A ⟶ X := {
      val := (
        fun _ ↦ a,
        fun (i : Fin 2) ↦ if i = 0 then X.toSrc a else X.toTgt a
      )
      property := by
        constructor <;> rfl
    }
    have h := ha x
    apply_fun (fun k ↦ k.val.1 ()) at h
    exact h
  -- Prove equality on DotMap
  · funext d
    let x : D ⟶ X := {
      val := (Empty.elim, fun _ ↦ d)
      property := by
        constructor <;> (funext e; exact Empty.elim e)
    }
    have h := hd x
    apply_fun (fun k ↦ k.val.2 ()) at h
    exact h
```

:::question (questionTitle := "Exercise 6") (questionPage := "215")
Show that in the category 𝑺↻ of discrete dynamical systems, there is a single object $`N` such that the 𝑺↻-maps from $`N` are sufficient to separate the maps $`{X \rightrightarrows Y}` of arbitrary objects. Hint: The object $`N` must have an infinite number of states and may be taken to be the basic object of 'arithmetic'.
:::

:::solution (solutionTo := "Exercise 6")
```savedComment
Exercise IV.6 (p. 215)
```

The appropriate object $`N` is the discrete dynamical system whose states are the natural numbers and whose endomap is the successor function $`\sigma`. We previously implemented this object as `ℕσ` in Session 15, and we reuse that implementation here. Otherwise, the proof strategy is similar to that used in the excerpt above.

```savedLean
example
    (X Y : SetWithEndomap)
    (f g : X ⟶ Y)
    : ∃ N : SetWithEndomap,
        (∀ x : N ⟶ X, f ⊚ x = g ⊚ x) → f = g := by
  use ℕσ
  intro hx
  apply Subtype.ext
  funext x'
  let x : ℕσ ⟶ X := {
    -- n ↦ X.toEnd^[n] x' for n = 0,1,2,...
    val := fun n ↦ Nat.recOn n x' (fun _ prev ↦ X.toEnd prev)
    property := rfl
  }
  have h := hx x
  apply_fun (fun k ↦ k.val (0 : ℕ)) at h
  exact h
```
:::

# 3. Initial object

:::definition (definitionTerm := "Initial object") (definitionPage := "215")
$`S` is an _initial object_ of 𝒞 if for every object $`X` of 𝒞 there is exactly one 𝒞-map $`{S \rightarrow X}`.
:::

The relevant mathlib definitions here are `HasInitial` and `IsInitial`, which we print below for reference (cf. `HasTerminal` and `IsTerminal` above).

```lean (name := out_HasInitial)
#print HasInitial
```

```leanOutput out_HasInitial
@[reducible] def CategoryTheory.Limits.HasInitial.{v₁, u₁} : (C : Type u₁) → [Category.{v₁, u₁} C] → Prop :=
fun C [Category.{v₁, u₁} C] ↦ HasColimitsOfShape (Discrete PEmpty.{1}) C
```

```lean (name := out_IsInitial)
#print IsInitial
```

```leanOutput out_IsInitial
@[reducible] def CategoryTheory.Limits.IsInitial.{v₁, u₁} : {C : Type u₁} →
  [Category.{v₁, u₁} C] → C → Type (max (max 0 u₁) v₁) :=
fun {C} [Category.{v₁, u₁} C] X ↦ IsColimit (asEmptyCocone X)
```

:::question (questionTitle := "Exercise 7") (questionPage := "215")
If $`S_1`, $`S_2` are both initial in 𝒞 then the (unique) map $`{S_1 \rightarrow S_2}` is an isomorphism.
:::

:::solution (solutionTo := "Exercise 7")
```savedComment
Exercise IV.7 (p. 215)
```

cf. the proof of the earlier proposition on uniqueness of terminal objects (pp. 213–214).

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] {S₁ S₂ : 𝒞}
    (hS₁ : IsInitial S₁) (hS₂ : IsInitial S₂)
    : ∃! s : S₁ ⟶ S₂, IsIso s := by
  let f : S₁ ⟶ S₂ := hS₁.to S₂
  let g : S₂ ⟶ S₁ := hS₂.to S₁
  have h_id₁ : g ⊚ f = 𝟙 S₁ := hS₁.hom_ext _ _
  have h_id₂ : f ⊚ g = 𝟙 S₂ := hS₂.hom_ext _ _
  use f
  constructor
  · exact { out := ⟨g, h_id₁, h_id₂⟩ }
  · intros
    exact hS₁.hom_ext _ _
```
:::

:::question (questionTitle := "Exercise 8") (questionPage := "216")
In each of 𝑺, 𝑺⇊, and 𝑺↻, if $`\mathbf{0}` is an initial object and $`{X \xrightarrow{f} \mathbf{0}}` is a map, then both

(a) for any $`{X \xrightarrow{g} \mathbf{0}}`, $`{g = f}`; and

(b) $`X` itself is initial.
:::

:::solution (solutionTo := "Exercise 8")
```savedComment
Exercise IV.8 (p. 216)
```

For each of 𝑺, 𝑺⇊, and 𝑺↻, we follow the same strategy. To prove part (a) we show that $`f` and $`g` are both 'empty' maps and therefore trivially equal; to prove part (b) we show that for every object $`Y` of the respective category there is exactly one morphism $`{X \rightarrow Y}`, namely the empty map.

In the case of 𝑺 we have

```savedLean
example
    {Zero X : Type}
    (hZero : IsInitial Zero) (f : X ⟶ Zero)
    : (∀ g : X ⟶ Zero, g = f) ∧ Nonempty (IsInitial X) := by
  have e : Zero ⟶ Empty := hZero.to Empty
  constructor
  · intro g
    exact IsInitial.strict_hom_ext hZero g f
  · constructor
    apply IsInitial.ofUnique (
      h := fun Y ↦ {
        default := hZero.to Y ⊚ f
        uniq := by
          intros
          funext x
          exact (e (f x)).elim
      }
    )
```

In the case of 𝑺⇊ we first define an empty object in 𝑺⇊.

```savedLean
def emptyIG : IrreflexiveGraph := {
  carrierA := Empty
  carrierD := Empty
  toSrc := Empty.elim
  toTgt := Empty.elim
}
```

Then we have

```savedLean
example
    {Zero X : IrreflexiveGraph}
    (hZero : IsInitial Zero) (f : X ⟶ Zero)
    : (∀ g : X ⟶ Zero, g = f) ∧ Nonempty (IsInitial X) := by
  have e : Zero ⟶ emptyIG := hZero.to emptyIG
  constructor
  · intros
    ext x
    · exact (e.val.1 (f.val.1 x)).elim
    · exact (e.val.2 (f.val.2 x)).elim
  · constructor
    apply IsInitial.ofUnique (
      h := fun Y ↦ {
        default := hZero.to Y ⊚ f
        uniq := by
          intros
          ext x
          · exact (e.val.1 (f.val.1 x)).elim
          · exact (e.val.2 (f.val.2 x)).elim
      }
    )
```

In the case of 𝑺↻ we first define an empty object in 𝑺↻.

```savedLean
def emptySWE : SetWithEndomap := {
  carrier := Empty
  toEnd := Empty.elim
}
```

Then we have

```savedLean
example
    {Zero X : SetWithEndomap}
    (hZero : IsInitial Zero) (f : X ⟶ Zero)
    : (∀ g : X ⟶ Zero, g = f) ∧ Nonempty (IsInitial X) := by
  have e : Zero ⟶ emptySWE := hZero.to emptySWE
  constructor
  · intros
    apply Subtype.ext
    funext x
    exact (e.val (f.val x)).elim
  · constructor
    apply IsInitial.ofUnique (
      h := fun Y ↦ {
        default := hZero.to Y ⊚ f
        uniq := by
          intros
          apply Subtype.ext
          funext x
          exact (e.val (f.val x)).elim
      }
    )
```
:::

:::question (questionTitle := "Exercise 9") (questionPage := "216")
```savedComment
Exercise IV.9 (p. 216)
```

Define the category $`\mathbf{1}`/𝑺 of _pointed sets_: an _object_ is a map $`{\mathbf{1} \xrightarrow{x_0} X}` in 𝑺, and a _map_ from $`{\mathbf{1} \xrightarrow{x_0} X}` to $`{\mathbf{1} \xrightarrow{y_0} Y}` is a map $`{X \xrightarrow{f} Y}` in 𝑺 for which

```savedLean
structure PointedSet where
  carrier : Type
  point : One ⟶ carrier

instance : Category PointedSet where
  Hom X Y := {
    f : X.carrier ⟶ Y.carrier //
        f ⊚ X.point = Y.point -- commutes
  }
  id X := ⟨𝟙 X.carrier, rfl⟩
  comp f g := ⟨
    g.val ⊚ f.val,
    by
      obtain hf_comm := f.property
      obtain hg_comm := g.property
      rw [← Category.assoc, hf_comm, hg_comm]
  ⟩
```

Show that in $`\mathbf{1}`/𝑺 any terminal object is also initial and that part (b) of the previous exercise is false.
:::

:::solution (solutionTo := "Exercise 9")
The terminal object in $`\mathbf{1}`/𝑺 is the identity map on $`\mathbf{1}`.

```savedLean
example
    {T : PointedSet}
    (hT : IsTerminal T)
    : Nonempty (IsInitial T)
    ∧ ¬(∀ X : PointedSet, Nonempty (IsInitial X)) := by
  constructor
  · -- Define the object PSOne,
    let PSOne : PointedSet := {
      carrier := One
      point := 𝟙 One
    }
    -- and show that PSOne is terminal
    have hT' : IsTerminal PSOne := by
      apply IsTerminal.ofUnique (
        h := fun X ↦ {
          default := by
            exact ⟨fun _ ↦ (), rfl⟩
          uniq := by
            intros
            rfl
        }
      )
    -- PSOne is isomorphic to T,
    have h_iso : PSOne ≅ T := IsTerminal.uniqueUpToIso hT' hT
    -- so it suffices to show that PSOne is initial
    constructor
    apply IsInitial.ofIso _ h_iso
    exact IsInitial.ofUnique (
      h := fun Y ↦ {
        default := by
          exact ⟨Y.point, rfl⟩
        uniq := by
          intro a
          exact Subtype.ext a.property
      }
    )
  · -- Consider the pointed set X with two elements
    let X : PointedSet := {
      carrier := Fin 2
      point := fun _ ↦ 0
    }
    -- and two distinct endomorphisms
    let f₁ : X ⟶ X := {
      val := fun
        | 0 => 0
        | 1 => 0
      property := rfl
    }
    let f₂ : X ⟶ X := {
      val := fun
        | 0 => 0
        | 1 => 1
      property := rfl
    }
    intro h
    -- If X is intial,
    obtain ⟨hI⟩ := h X
    -- then there is a unique morphism from X to itself, so f₁ = f₂
    have h_eq : f₁ = f₂ := hI.hom_ext f₁ f₂
    -- But f₁ and f₂ are distinct, so X is not initial
    have : f₁.val = f₂.val := congr_arg Subtype.val h_eq
    exact zero_ne_one (congr_fun this 1)
```

We can faithfully implement the same proof using mathlib's `Under` category, as demonstrated below.

```savedLean -show
namespace ExIV_9
```

```savedLean
abbrev PointedSet := Under Unit

example
    {T : PointedSet}
    (hT : IsTerminal T)
    : Nonempty (IsInitial T)
    ∧ ¬(∀ X : PointedSet, Nonempty (IsInitial X)) := by
  constructor
  · -- Define the object PSOne,
    let PSOne : PointedSet := Under.mk (𝟙 Unit)
    -- and show that PSOne is terminal
    have hT' : IsTerminal PSOne := by
      apply IsTerminal.ofUnique (
        h := fun X ↦ {
          default := Under.homMk (fun _ ↦ ())
          uniq := by
            intros
            rfl
        }
      )
    -- PSOne is isomorphic to T,
    have h_iso : PSOne ≅ T := IsTerminal.uniqueUpToIso hT' hT
    -- so it suffices to show that PSOne is initial
    constructor
    apply IsInitial.ofIso _ h_iso
    exact IsInitial.ofUnique (
      h := fun Y ↦ {
        default := Under.homMk Y.hom
        uniq := by
          intro a
          exact Under.UnderMorphism.ext (Under.w a)
      }
    )
  · -- Consider the pointed set X with two elements
    let X : PointedSet := Under.mk (fun _ ↦ (0 : Fin 2))
    -- and two distinct endomorphisms
    let f₁ : X ⟶ X := Under.homMk (fun
      | 0 => 0
      | 1 => 0
      : Fin 2 ⟶ Fin 2)
    let f₂ : X ⟶ X := Under.homMk (fun
      | 0 => 0
      | 1 => 1
      : Fin 2 ⟶ Fin 2)
    intro h
    -- If X is intial,
    obtain ⟨hI⟩ := h X
    -- then there is a unique morphism from X to itself, so f₁ = f₂
    have h_eq : f₁ = f₂ := hI.hom_ext f₁ f₂
    -- But f₁ and f₂ are distinct, so X is not initial
    have : f₁.right = f₂.right := Under.UnderMorphism.ext_iff.mp h_eq
    exact Fin.zero_ne_one (congr_fun this (1 : Fin 2))
```

```savedLean -show
end ExIV_9
```

A more idiomatic Lean proof would likely use mathlib's `Pointed` category, but at the cost of moving away from the book's morphism-based definition of a point. A version of the same proof using `Pointed` is given below.

```savedLean
example
    {T : Pointed.{0}}
    (hT : IsTerminal T)
    : Nonempty (IsInitial T)
    ∧ ¬(∀ X : Pointed.{0}, Nonempty (IsInitial X)) := by
  constructor
  · -- Define the object PSOne,
    let PSOne : Pointed := {
      X := One
      point := ()
    }
    -- and show that PSOne is terminal
    have hT' : IsTerminal PSOne := by
      apply IsTerminal.ofUnique (
        h := fun X ↦ {
          default := by
            exact ⟨fun _ ↦ (), rfl⟩
          uniq := by
            intros
            rfl
        }
      )
    -- PSOne is isomorphic to T,
    have h_iso : PSOne ≅ T := IsTerminal.uniqueUpToIso hT' hT
    -- so it suffices to show that PSOne is initial
    constructor
    apply IsInitial.ofIso _ h_iso
    exact IsInitial.ofUnique (
      h := fun Y ↦ {
        default := by
          exact ⟨fun _ ↦ Y.point, rfl⟩
        uniq := by
          intro a
          apply Pointed.Hom.ext
          funext x
          exact a.map_point
      }
    )
  · -- Consider the pointed set X with two elements
    let X : Pointed := {
      X := Fin 2
      point := 0
    }
    -- and two distinct endomorphisms
    let f₁ : X ⟶ X := {
      toFun := fun
        | 0 => 0
        | 1 => 0
      map_point := rfl
    }
    let f₂ : X ⟶ X := {
      toFun := fun
        | 0 => 0
        | 1 => 1
      map_point := rfl
    }
    intro h
    -- If X is intial,
    have := h X
    obtain ⟨hI⟩ := h X
    -- then there is a unique morphism from X to itself, so f₁ = f₂
    have h_eq : f₁ = f₂ := hI.hom_ext f₁ f₂
    -- But f₁ and f₂ are distinct, so X is not initial
    have : f₁.toFun = f₂.toFun := Pointed.Hom.ext_iff.mp h_eq
    exact zero_ne_one (congr_fun this 1)
```
:::

:::question (questionTitle := "Exercise 10") (questionPage := "216")
```savedComment
Exercise IV.10 (p. 216)
```

Let $`\mathbf{2}` be a fixed 2-point set.

```savedLean
abbrev Two := Fin 2
```

Define the category $`\mathbf{2}`/𝑺 of _bipointed sets_ to have as objects the 𝑺-maps $`{\mathbf{2} \xrightarrow{\bar{x}} X}` and as maps the 𝑺-maps satisfying $`{f\bar{x} = \bar{y}}`

```savedLean
structure BipointedSet where
  carrier : Type
  point : Two ⟶ carrier

instance : Category BipointedSet where
  Hom X Y := {
    f : X.carrier ⟶ Y.carrier //
        f ⊚ X.point = Y.point -- commutes
  }
  id X := ⟨𝟙 X.carrier, rfl⟩
  comp f g := ⟨
    g.val ⊚ f.val,
    by
      obtain hf_comm := f.property
      obtain hg_comm := g.property
      rw [← Category.assoc, hf_comm, hg_comm]
  ⟩
```

Show that in $`\mathbf{2}`/𝑺 'the' initial object is the identity map $`{\mathbf{2} \rightarrow \mathbf{2}}` and that part (a) of Exercise 8 is false, i.e. an object can have more than one map to the initial object.
:::

:::solution (solutionTo := "Exercise 10")
In a similar fashion to Exercise 9, we provide three different implementations of the same proof.

The first version of the proof uses our custom `BipointedSet` category.

```savedLean -show
namespace ExIV_10a
```

```savedLean
def BSTwo : BipointedSet := {
  carrier := Two
  point := 𝟙 Two
}

example : Nonempty (IsInitial BSTwo)
          ∧ ¬(∀ (X : BipointedSet) (f g : X ⟶ BSTwo), f = g) := by
  constructor
  · -- Show that BSTwo is initial
    constructor
    apply IsInitial.ofUnique (
      h := fun Y ↦ {
        default := by
          exact ⟨Y.point, rfl⟩
        uniq := by
          intro a
          exact Subtype.ext a.property
      }
    )
  · -- Consider the bipointed set X with three elements
    let X : BipointedSet := {
      carrier := Fin 3
      point := fun
        | 0 => 0
        | 1 => 1
    }
    -- and two distinct morphisms to the initial object
    let f : X ⟶ BSTwo := {
      val := (fun
      | 0 => 0
      | 1 => 1
      | 2 => 0
      : X.carrier ⟶ Two)
      property := by
        funext x
        fin_cases x <;> rfl
    }
    let g : X ⟶ BSTwo := {
      val := (fun
      | 0 => 0
      | 1 => 1
      | 2 => 1
      : X.carrier ⟶ Two)
      property := by
        funext x
        fin_cases x <;> rfl
    }
    intro h
    have : f.val = g.val := congr_arg Subtype.val (h X f g)
    exact Fin.zero_ne_one (congr_fun this 2)
```

```savedLean -show
end ExIV_10a
```

The second version of the proof uses mathlib's `Under` category.

```savedLean -show
namespace ExIV_10b
```

```savedLean
abbrev BipointedSet := Under (Fin 2)

def BSTwo : BipointedSet := Under.mk (𝟙 (Fin 2))

example : Nonempty (IsInitial BSTwo)
          ∧ ¬(∀ (X : BipointedSet) (f g : X ⟶ BSTwo), f = g) := by
  constructor
  · -- Show that BSTwo is initial
    constructor
    apply IsInitial.ofUnique (
      h := fun Y ↦ {
        default := Under.homMk Y.hom
        uniq := by
          intro a
          exact Under.UnderMorphism.ext (Under.w a)
      }
    )
  · -- Consider the bipointed set X with three elements
    let X : BipointedSet := Under.mk (fun
      | 0 => 0
      | 1 => 1
      : Fin 2 ⟶ Fin 3)
    -- and two distinct morphisms to the initial object
    let f : X ⟶ BSTwo := Under.homMk (fun
      | 0 => 0
      | 1 => 1
      | 2 => 0
      : Fin 3 ⟶ Fin 2)
      (by
        funext (x : Fin 2)
        fin_cases x <;> rfl)
    let g : X ⟶ BSTwo := Under.homMk (fun
      | 0 => 0
      | 1 => 1
      | 2 => 1
      : Fin 3 ⟶ Fin 2)
      (by
        funext (x : Fin 2)
        fin_cases x <;> rfl)
    intro h
    have : f.right = g.right :=
        Under.UnderMorphism.ext_iff.mp (h X f g)
    exact Fin.zero_ne_one (congr_fun this (2 : Fin 3))
```

```savedLean -show
end ExIV_10b
```

The third version of the proof uses mathlib's `Bipointed` category.

```savedLean -show
namespace ExIV_10c
```

```savedLean
abbrev BSTwo : Bipointed := ⟨Fin 2, (0, 1)⟩

example : Nonempty (IsInitial BSTwo)
          ∧ ¬(∀ (X : Bipointed) (f g : X ⟶ BSTwo), f = g) := by
  constructor
  · -- Show that BSTwo is initial
    constructor
    apply IsInitial.ofUnique (
      h := fun Y ↦ {
        default := Bipointed.Hom.mk (fun
          | 0 => Y.toProd.1
          | 1 => Y.toProd.2
          : Fin 2 ⟶ Y.X)
          rfl
          rfl
        uniq := by
          intro a
          apply Bipointed.Hom.ext
          funext x
          fin_cases x
          · exact a.map_fst
          · exact a.map_snd
      }
    )
  · -- Consider the bipointed set X with three elements
    let X : Bipointed := ⟨Fin 3, (0, 1)⟩
    -- and two distinct morphisms to the initial object
    let f : X ⟶ BSTwo := Bipointed.Hom.mk (fun
      | 0 => 0
      | 1 => 1
      | 2 => 0
      : Fin 3 ⟶ Fin 2)
      rfl
      rfl
    let g : X ⟶ BSTwo := Bipointed.Hom.mk (fun
      | 0 => 0
      | 1 => 1
      | 2 => 1
      : Fin 3 ⟶ Fin 2)
      rfl
      rfl
    intro h
    have : f.toFun = g.toFun := Bipointed.Hom.ext_iff.mp (h X f g)
    exact Fin.zero_ne_one (congr_fun this (2 : Fin 3))
```

```savedLean -show
end ExIV_10c
```
:::

:::question (questionTitle := "Exercise 11") (questionPage := "216")
Show that in the category 𝑺, if an object $`X` is not an initial object, then $`X` has at least one point (map from a terminal object). Show that the same statement is false in both the categories 𝑺↻ and 𝑺⇊.
:::

:::solution (solutionTo := "Exercise 11")
```savedComment
Exercise IV.11 (p. 216)
```

In our answer below to the first part of the exercise, we use the category `Type` instead of the category 𝑺.

```savedLean
example : ∀ X, IsEmpty (IsInitial X) → Nonempty (⊤_ Type ⟶ X) := by
  intro X hX
  have h_nonempty : Nonempty X := by
    by_contra h_empty
    apply hX.false
    exact IsInitial.ofUnique (
      h := fun Y ↦ {
        default := fun x ↦ False.elim (h_empty (Nonempty.intro x))
        uniq := by
          intros
          funext x
          exact False.elim (h_empty (Nonempty.intro x))
      }
    )
  exact Nonempty.map (fun x _ ↦ x) h_nonempty
```

To work with the same statement in 𝑺↻, we first need a `HasTerminal` instance for the category `SetWithEndomap`, since the statement includes the terminal object `⊤_`.

```savedLean
instance : HasTerminal SetWithEndomap where
  has_limit _ := HasLimit.mk' (
    exists_limit := Nonempty.intro {
      cone := {
        pt := {
          carrier := Unit
          toEnd := id
        }
        π := { app := fun j ↦ j.as.elim }
      }
      isLimit := {
        lift := fun _ ↦ {
          val := fun _ ↦ ()
          property := rfl
        }
        fac := fun _ j ↦ j.as.elim
        uniq _ _ _ := rfl
      }
    }
  )
```

We can now use the `emptySWE` object defined in Exercise 8 above to show that the statement is false in the category 𝑺↻.

```savedLean
example : ¬(∀ X : SetWithEndomap, IsEmpty (IsInitial X) →
    Nonempty (⊤_ SetWithEndomap ⟶ X)) := by
  push Not
  -- Define an object X which is not initial
  -- and has no morphism from the terminal object
  let X : SetWithEndomap := {
    carrier := Fin 2
    toEnd := fun
      | 0 => 1
      | 1 => 0
  }
  use X
  constructor
  · -- Assume towards a contradiction that X is initial
    refine ⟨fun hX : IsInitial X ↦ ?_⟩
    -- Since, by assumption, X is initial, there exists X ⟶ emptySWE
    let f : X ⟶ emptySWE := hX.to emptySWE
    -- But the assumption is false, since the carrier of emptySWE is ∅
    exact (f.val 0).elim
  · -- Assume towards a contradiction that there exists ⊤_ ⟶ X
    refine ⟨fun hX : ⊤_ SetWithEndomap ⟶ X ↦ ?_⟩
    -- Define a probe object U
    let U : SetWithEndomap := {
      carrier := Unit
      toEnd := id
    }
    let f : U ⟶ X := hX ⊚ terminal.from U
    -- Perform case analysis to show that the assumption is false
    have h_comm : (f.val ⊚ U.toEnd) () = (X.toEnd ⊚ f.val) () :=
        congr_fun f.property ()
    dsimp [U, X] at h_comm
    generalize f.val () = x at h_comm
    fin_cases x <;> trivial
```

Our proof that the same statement is false in 𝑺⇊ is essentially identical to our proof for 𝑺↻, just with the endomaps of sets translated into irreflexive graphs.

```savedLean
instance : HasTerminal IrreflexiveGraph where
  has_limit _ := HasLimit.mk' (
    exists_limit := Nonempty.intro {
      cone := {
        pt := {
          carrierA := Unit
          carrierD := Unit
          toSrc := fun _ ↦ ()
          toTgt := fun _ ↦ ()
        }
        π := { app := fun j ↦ j.as.elim }
      }
      isLimit := {
        lift := fun _ ↦ {
          val := (fun _ ↦ (), fun _ ↦ ())
          property := by
            constructor <;> rfl
        }
        fac := fun _ j ↦ j.as.elim
        uniq _ _ _ := rfl
      }
    }
  )

example : ¬(∀ X : IrreflexiveGraph, IsEmpty (IsInitial X) →
    Nonempty (⊤_ IrreflexiveGraph ⟶ X)) := by
  push Not
  -- Define an object X which is not initial
  -- and has no morphism from the terminal object
  let X : IrreflexiveGraph := {
    carrierA := Fin 2
    carrierD := Fin 2
    toSrc := fun
      | 0 => 0
      | 1 => 1
    toTgt := fun
      | 0 => 1
      | 1 => 0
  }
  use X
  constructor
  · -- Assume towards a contradiction that X is initial
    refine ⟨fun hX : IsInitial X ↦ ?_⟩
    -- Since, by assumption, X is initial, there exists X ⟶ emptyIG
    let f : X ⟶ emptyIG := hX.to emptyIG
    -- But the assumption is false, since carrierA of emptyIG is ∅
    exact (f.val.1 0).elim
  · -- Assume towards a contradiction that there exists ⊤_ ⟶ X
    refine ⟨fun hX : ⊤_ IrreflexiveGraph ⟶ X ↦ ?_⟩
    -- Define a probe object U
    let U : IrreflexiveGraph := {
      carrierA := Unit
      carrierD := Unit
      toSrc := fun _ ↦ ()
      toTgt := fun _ ↦ ()
    }
    let f : U ⟶ X := hX ⊚ terminal.from U
    -- Perform case analysis to show that the assumption is false
    have h_src_comm := congr_fun f.property.1 ()
    have h_tgt_comm := congr_fun f.property.2 ()
    dsimp [U, X] at h_src_comm h_tgt_comm
    generalize f.val.1 () = x₁ at h_src_comm h_tgt_comm
    generalize f.val.2 () = x₂ at h_src_comm h_tgt_comm
    fin_cases x₁ <;> fin_cases x₂ <;> trivial
```
:::

# 4. Products

:::definition (definitionTerm := "Product") (definitionPage := "217")
An object $`P` together with a pair of maps $`{P \xrightarrow{p_1} B_1}`, $`{P \xrightarrow{p_2} B_2}` is called a _product_ of $`B_1` and $`B_2` if for each object $`X` and each pair of maps $`{X \xrightarrow{f_1} B_1}`, $`{X \xrightarrow{f_2} B_2}`, there is exactly one map $`{X \xrightarrow{f} P}` for which both $`{f_1 = p_1 f}` and $`{f_2 = p_2 f}`.
:::

In mathlib, the categorical (binary) product is formalised as the limit of a discrete diagram containing a pair of objects. The data (the product object $`P` and its _projections_ $`p_1` and $`p_2`) are bundled into the `BinaryFan` type, which is a cone on a diagram indexed by the discrete category on the inductive type `WalkingPair`. The universal property is asserted by the `IsLimit` structure applied to that cone. We print these three definitions below for reference.

```lean (name := out_BinaryFan)
#print BinaryFan
```

```leanOutput out_BinaryFan
@[reducible] def CategoryTheory.Limits.BinaryFan.{v, u} : {C : Type u} →
  [Category.{v, u} C] → C → C → Type (max (max 0 u) v) :=
fun {C} [Category.{v, u} C] X Y ↦ Cone (pair X Y)
```

```lean (name := out_WalkingPair)
#print WalkingPair
```

```leanOutput out_WalkingPair
inductive CategoryTheory.Limits.WalkingPair : Type
number of parameters: 0
constructors:
CategoryTheory.Limits.WalkingPair.left : WalkingPair
CategoryTheory.Limits.WalkingPair.right : WalkingPair
```

```lean (name := out_IsLimit)
#print IsLimit
```

```leanOutput out_IsLimit
structure CategoryTheory.Limits.IsLimit.{v₁, v₃, u₁, u₃} {J : Type u₁} [Category.{v₁, u₁} J] {C : Type u₃}
  [Category.{v₃, u₃} C] {F : J ⥤ C} (t : Cone F) : Type (max (max u₁ u₃) v₃)
number of parameters: 6
fields:
  CategoryTheory.Limits.IsLimit.lift : (s : Cone F) → s.pt ⟶ t.pt
  CategoryTheory.Limits.IsLimit.fac : ∀ (s : Cone F) (j : J), t.π.app j ⊚ self.lift s = s.π.app j := by
    cat_disch
  CategoryTheory.Limits.IsLimit.uniq : ∀ (s : Cone F) (m : s.pt ⟶ t.pt),
      (∀ (j : J), t.π.app j ⊚ m = s.π.app j) → m = self.lift s := by
    cat_disch
constructor:
  CategoryTheory.Limits.IsLimit.mk.{v₁, v₃, u₁, u₃} {J : Type u₁} [Category.{v₁, u₁} J] {C : Type u₃}
    [Category.{v₃, u₃} C] {F : J ⥤ C} {t : Cone F} (lift : (s : Cone F) → s.pt ⟶ t.pt)
    (fac : ∀ (s : Cone F) (j : J), t.π.app j ⊚ lift s = s.π.app j := by cat_disch)
    (uniq : ∀ (s : Cone F) (m : s.pt ⟶ t.pt), (∀ (j : J), t.π.app j ⊚ m = s.π.app j) → m = lift s := by cat_disch) :
    IsLimit t
```

We show that the formalisation in mathlib of the categorical (binary) product is equivalent to the definition given in the book.

```savedComment
Product (binary) (p. 217)
```

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (P B₁ B₂ : 𝒞) (p₁ : P ⟶ B₁) (p₂ : P ⟶ B₂)
    : Nonempty (IsLimit (BinaryFan.mk p₁ p₂)) ↔
      ∀ (X : 𝒞) (f₁ : X ⟶ B₁) (f₂ : X ⟶ B₂),
          ∃! f : X ⟶ P, p₁ ⊚ f = f₁ ∧ p₂ ⊚ f = f₂ := by
  constructor
  · rintro ⟨h⟩ X f₁ f₂
    let s := BinaryFan.mk f₁ f₂
    use h.lift s
    and_intros
    · exact (h.fac s ⟨WalkingPair.left⟩)
    · exact (h.fac s ⟨WalkingPair.right⟩)
    · intro m ⟨h₁, h₂⟩
      apply h.uniq s
      rintro ⟨_ | _⟩
      all_goals
        dsimp
        first | erw [h₁] | erw [h₂]
        rfl
  · intro h
    constructor
    let hs (s : BinaryFan B₁ B₂) :=
      let f₁ : s.pt ⟶ B₁ := s.π.app ⟨WalkingPair.left⟩
      let f₂ : s.pt ⟶ B₂ := s.π.app ⟨WalkingPair.right⟩
      h s.pt f₁ f₂
    refine IsLimit.mk ?_ ?_ ?_
    · -- lift
      intro s
      exact (hs s).choose
    · -- fac
      intro s j
      rcases j with ⟨_ | _⟩
      · exact (hs s).choose_spec.1.1
      · exact (hs s).choose_spec.1.2
    · -- uniq
      intro s m w
      apply (hs s).choose_spec.2
      constructor
      · exact (w ⟨WalkingPair.left⟩)
      · exact (w ⟨WalkingPair.right⟩)
```

:::question (questionTitle := "Exercise 12") (questionPage := "217")
If $`P`, $`p_1`, $`p_2` and also $`Q`, $`q_1`, $`q_2` are both products of the same pair of objects $`B_1`, $`B_2` in a given category, then the unique map
$$`P \xrightarrow{f} Q`
for which $`p_1 = q_1 f` and $`p_2 = q_2 f` is an _isomorphism_.
:::

:::solution (solutionTo := "Exercise 12")
```savedComment
Exercise IV.12 (p. 217)
```

From the formalisation in mathlib described above, we obtain the following mappings between the notation for this exercise in the book and the data used in our proof:

`P = coneP.pt`; `p₁ = coneP.fst`; `p₂ = coneP.snd`

`Q = coneQ.pt`; `q₁ = coneQ.fst`; `q₂ = coneQ.snd`

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] (B₁ B₂ : 𝒞)
    (coneP coneQ : BinaryFan B₁ B₂)
    (prodP : IsLimit coneP) (prodQ : IsLimit coneQ)
    : ∃! f : coneP.pt ⟶ coneQ.pt,
        (coneQ.fst ⊚ f = coneP.fst ∧ coneQ.snd ⊚ f = coneP.snd)
        ∧ IsIso f := by
  use prodQ.lift coneP -- f
  and_intros
  · -- Show that q₁ ⊚ f = p₁
    exact prodQ.fac coneP ⟨WalkingPair.left⟩
  · -- Show that q₂ ⊚ f = p₂
    exact prodQ.fac coneP ⟨WalkingPair.right⟩
  · -- Show that f is an isomorphism
    apply IsIso.mk
    use prodP.lift coneQ -- f⁻¹
    constructor
    · -- f⁻¹ ⊚ f = 𝟙 P
      rw [prodP.uniq coneP (𝟙 coneP.pt)
                           (fun _ ↦ Category.id_comp _)]
      apply prodP.uniq coneP
      intro j
      rw [Category.assoc, prodP.fac, prodQ.fac]
    · -- f ⊚ f⁻¹ = 𝟙 Q
      rw [prodQ.uniq coneQ (𝟙 coneQ.pt)
                           (fun _ ↦ Category.id_comp _)]
      apply prodQ.uniq coneQ
      intro j
      rw [Category.assoc, prodQ.fac, prodP.fac]
  · -- Show that f is unique
    intro f ⟨⟨h_left, h_right⟩, _⟩
    apply prodQ.uniq coneP
    intro j
    rcases j with ⟨_ | _⟩
    · exact h_left
    · exact h_right
```

We can use the mathlib lemma `IsLimit.nonempty_isLimit_iff_isIso_lift` to do much of the heavy lifting here. A revised version of the proof using this lemma is given below.

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] (B₁ B₂ : 𝒞)
    (coneP coneQ : BinaryFan B₁ B₂)
    (prodP : IsLimit coneP) (prodQ : IsLimit coneQ)
    : ∃! f : coneP.pt ⟶ coneQ.pt,
        (coneQ.fst ⊚ f = coneP.fst ∧ coneQ.snd ⊚ f = coneP.snd)
        ∧ IsIso f := by
  use prodQ.lift coneP
  and_intros
  · -- Show that q₁ ⊚ f = p₁
    exact prodQ.fac coneP ⟨WalkingPair.left⟩
  · -- Show that q₂ ⊚ f = p₂
    exact prodQ.fac coneP ⟨WalkingPair.right⟩
  · -- Show that f is an isomorphism
    exact (IsLimit.nonempty_isLimit_iff_isIso_lift prodQ).mp ⟨prodP⟩
  · -- Show that f is unique
    intro f ⟨⟨h_left, h_right⟩, _⟩
    apply prodQ.uniq coneP
    intro j
    rcases j with ⟨_ | _⟩
    · exact h_left
    · exact h_right
```
:::

:::question (questionTitle := "Exercise 13") (questionPage := "217")
In a category 𝒞 with products and a terminal object, each point of $`{B_1 \times B_2}` is uniquely of the form $`{\langle b_1,b_2 \rangle}`, where $`b_i` is a point of $`{B_i(i = 1,2)}`; and any pair of points of $`B_1`, $`B_2` are the projections of exactly one point of $`{B_1 \times B_2}`.
:::

:::solution (solutionTo := "Exercise 13")
```savedComment
Exercise IV.13 (p. 217)
```

To formalise the statement for this exercise, we first need to define what it means for a category to have (binary) products. In mathlib, a category with products is an instance of the typeclass `HasBinaryProducts`, which is the typeclass `HasLimitsOfShape` applied to the discrete category on two objects. We print this definition below for reference.

```lean (name := out_HasBinaryProducts)
#print HasBinaryProducts
```

```leanOutput out_HasBinaryProducts
@[reducible] def CategoryTheory.Limits.HasBinaryProducts.{v, u} : (C : Type u) → [Category.{v, u} C] → Prop :=
fun C [Category.{v, u} C] ↦ HasLimitsOfShape (Discrete WalkingPair) C
```

Our proof of the statement then makes extensive use of the mathlib API for products, which is described in the documentation under Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.

```savedLean -show
namespace ExIV_13
```

```savedLean
variable {𝒞 : Type u} [Category.{v, u} 𝒞]
         [HasBinaryProducts 𝒞] [HasTerminal 𝒞]

abbrev Point' (X : 𝒞) := ⊤_ 𝒞 ⟶ X

example (B₁ B₂ : 𝒞)
    : (∀ p : Point' (B₁ ⨯ B₂),
        ∃! b : Point' B₁ × Point' B₂, p = prod.lift b.1 b.2)
    ∧ (∀ (b₁ : Point' B₁) (b₂ : Point' B₂),
        ∃! p : Point' (B₁ ⨯ B₂),
        b₁ = prod.fst ⊚ p ∧ b₂ = prod.snd ⊚ p) := by
  constructor
  · intro p
    use (prod.fst ⊚ p, prod.snd ⊚ p)
    constructor
    · dsimp
      apply prod.hom_ext
      · rw [prod.lift_fst]
      · rw [prod.lift_snd]
    · intro b h
      rw [h, prod.lift_fst, prod.lift_snd, Prod.mk.eta]
  · intro b₁ b₂
    use prod.lift b₁ b₂
    and_intros
    · rw [prod.lift_fst]
    · rw [prod.lift_snd]
    · rintro p ⟨h₁, h₂⟩
      apply prod.hom_ext
      · rw [prod.lift_fst, h₁]
      · rw [prod.lift_snd, h₂]
```

```savedLean -show
end ExIV_13
```
:::

:::definition (definitionTerm := "Binary operation") (definitionPage := "218")
A _binary operation_ on an object $`A` is a map
$$`A \times A \rightarrow A`
:::

:::definition (definitionTerm := "Action") (definitionPage := "218")
An _action_ of an object $`A` on an object $`X` is a map
$$`A \times X \rightarrow X`
:::

:::question (questionTitle := "Exercise 14") (questionPage := "219")
Define composition of maps in 𝑺ᴬ and show that it is a category.
:::

:::solution (solutionTo := "Exercise 14")
```savedComment
Exercise IV.14 (p. 219)
```

We define composition of maps $`{X,\xi \xrightarrow{f} Y,\eta}` and $`{Y,\eta \xrightarrow{g} Z,\theta}` in 𝑺ᴬ in the obvious way such that
$$`g \circ f \circ \xi = \theta \circ (\mathbf{1}_A \times g) \circ (\mathbf{1}_A \times f)`

We create a `Category` instance for 𝑺ᴬ using this definition of composition (and using types instead of sets) and thus show that the category axioms hold.

```savedLean
structure SetA (carrierA : Type) where
  carrier : Type
  action : carrierA × carrier ⟶ carrier

instance {carrierA : Type} : Category (SetA carrierA) where
  Hom X Y := {
    f : X.carrier ⟶ Y.carrier //
    f ⊚ X.action = Y.action ⊚ (Prod.map (𝟙 carrierA) f) -- commutes
  }
  id X := ⟨𝟙 X.carrier, rfl⟩
  comp f g := ⟨
    g.val ⊚ f.val,
    by
      obtain hf_comm := f.property
      obtain hg_comm := g.property
      rw [← Category.assoc, hf_comm, Category.assoc, hg_comm,
          ← Category.assoc]
      rfl
  ⟩
```
:::

:::question (questionTitle := "Exercise 15") (questionPage := "219")
Express these equations as equations between maps
$$`A \times A \times X \rightrightarrows X, \qquad X \rightrightarrows X`
constructed by using $`\xi` and the universal mapping property of products.
:::

:::solution (solutionTo := "Exercise 15")
For the first equation (associativity)
$$`\xi(\alpha(a,b),x) = \xi(a,\xi(b,x)), \enspace\forall\; a,b,x`
we can express the left-hand side as the composition of maps
$$`A \times A \times X \xrightarrow{\alpha \times \mathbf{1}_X} A \times X \xrightarrow{\xi} X`
and the right-hand side as the composition of maps
$$`A \times A \times X \xrightarrow{\mathbf{1}_A \times \xi} A \times X \xrightarrow{\xi} X`
from which we obtain the following equation between maps
$$`\xi \circ (\alpha \times \mathbf{1}_X) = \xi \circ (\mathbf{1}_A \times \xi)`

For the second equation (identity)
$$`\xi(a_0,x) = x, \enspace\forall\; x`
we can express the left-hand side as the composition of maps
$$`X \xrightarrow{\langle a_0, \mathbf{1}_X \rangle} A \times X \xrightarrow{\xi} X`
and the right-hand side as simply the identity map on $`X`
$$`X \xrightarrow{\mathbf{1}_X} X`
from which we obtain the following equation between maps
$$`\xi \circ \langle a_0, \mathbf{1}_X \rangle = \mathbf{1}_X`
:::

# 5. Commutative, associative, and identity laws for multiplication of objects

:::definition (definitionTerm := "Product") (definitionPage := "220")
A _product_ of \[a family of objects indexed by a set $`I`\] is an object $`P` together with maps $`{P \xrightarrow{p_i} C_i}` (one for each $`i`), having the universal property:

Given any object $`X` and any maps $`{X \xrightarrow{f_i} C_i}` (one for each $`i`), there is exactly one map $`{X \xrightarrow{f} P}` such that all the triangles ... commute, i.e. such that $`{p_i f = f_i}` for each $`i` in $`I`.
:::

In mathlib, the categorical product of an indexed family of objects is formalised as the limit of a discrete diagram representing that family. The data (the product object $`P` and its projections $`p_i`) are bundled into the `Fan` type, which is a cone on a diagram defined by the functor `Discrete.functor f`. The universal property is asserted by the `IsLimit` structure applied to that cone, and the product object itself is denoted by `∏ᶜ f` (`piObj f`), which is defined as an abbreviation for `limit (Discrete.functor f)`. We print the relevant definitions below for reference.

```lean (name := out_Fan)
#print Fan
```

```leanOutput out_Fan
@[reducible] def CategoryTheory.Limits.Fan.{w, v, u} : {β : Type w} →
  {C : Type u} → [Category.{v, u} C] → (β → C) → Type (max (max w u) v) :=
fun {β} {C} [Category.{v, u} C] f ↦ Cone (Discrete.functor f)
```

```lean (name := out_piObj)
#print piObj
```

```leanOutput out_piObj
@[reducible] def CategoryTheory.Limits.piObj.{w, v, u} : {β : Type w} →
  {C : Type u} → [inst : Category.{v, u} C] → (f : β → C) → [HasProduct f] → C :=
fun {β} {C} [Category.{v, u} C] f [HasProduct f] ↦ limit (Discrete.functor f)
```

We show that the formalisation in mathlib of the categorical product is equivalent to the definition given in the book (cf. our earlier proof of equivalency for the binary product).

```savedComment
Product (p. 220)
```

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] {I : Type}
    (P : 𝒞) (Cᵢ : I → 𝒞) (pᵢ : (i : I) → (P ⟶ Cᵢ i))
    : Nonempty (IsLimit (Fan.mk P pᵢ)) ↔
      ∀ (X : 𝒞) (fᵢ : (i : I) → (X ⟶ Cᵢ i)),
          ∃! f : X ⟶ P, (∀ i : I, pᵢ i ⊚ f = fᵢ i) := by
  constructor
  · rintro ⟨h⟩ X fᵢ
    let s := Fan.mk X fᵢ
    use h.lift s
    constructor
    · intro i
      exact h.fac s ⟨i⟩
    · intro m hᵢ
      apply h.uniq s
      intro i
      exact hᵢ i.as
  · intro h
    constructor
    let hs (s : Fan Cᵢ) :=
      let fᵢ : (i : I) → (s.pt ⟶ Cᵢ i) := fun i ↦ s.π.app ⟨i⟩
      h s.pt fᵢ
    refine IsLimit.mk ?_ ?_ ?_
    · -- lift
      intro s
      exact (hs s).choose
    · -- fac
      intro s i
      exact (hs s).choose_spec.1 i.as
    · -- uniq
      intro s m w
      apply (hs s).choose_spec.2
      intro i
      exact w ⟨i⟩
```

:::theoremDirective (theoremTitle := "Theorem (uniqueness of products)") (theoremPage := "221")
If the maps $`{P \xrightarrow{p_i} C_i}` and $`{Q \xrightarrow{q_i} C_i}` make both $`P` and $`Q` products of this family, then (because $`Q` is a product) there is exactly one map $`{P \xrightarrow{f} Q}` for which $`q_i f = p_i` for each $`i` in $`I`. Moreover, the map $`f` is an isomorphism.
:::

Our formalisation of the proof of this theorem is essentially identical to our proof of the uniqueness of binary products given in Exercise 12 above, just with the data and universal property of products generalised to an indexed family.

```savedComment
Theorem (uniqueness of products) (p. 221)
```

```savedLean
theorem uniqueness_of_products
    {𝒞 : Type u} [Category.{v, u} 𝒞] {I : Type} (Cᵢ : I → 𝒞)
    (coneP coneQ : Fan Cᵢ)
    (prodP : IsLimit coneP) (prodQ : IsLimit coneQ)
    : ∃! f : coneP.pt ⟶ coneQ.pt,
        (∀ i : I, coneQ.proj i ⊚ f = coneP.proj i)
        ∧ IsIso f := by
  use prodQ.lift coneP -- f
  and_intros
  · -- Show that qᵢ ⊚ f = pᵢ
    intro i
    exact prodQ.fac coneP ⟨i⟩
  · -- Show that f is an isomorphism
    apply IsIso.mk
    use prodP.lift coneQ -- f⁻¹
    constructor
    · -- f⁻¹ ⊚ f = 𝟙 P
      rw [prodP.uniq coneP (𝟙 coneP.pt) (fun _ ↦ Category.id_comp _)]
      apply prodP.uniq coneP
      intro i
      rw [Category.assoc, prodP.fac, prodQ.fac]
    · -- f ⊚ f⁻¹ = 𝟙 Q
      rw [prodQ.uniq coneQ (𝟙 coneQ.pt) (fun _ ↦ Category.id_comp _)]
      apply prodQ.uniq coneQ
      intro i
      rw [Category.assoc, prodQ.fac, prodP.fac]
  · -- Show that f is unique
    intro f ⟨hᵢ, _⟩
    apply prodQ.uniq coneP
    intro i
    exact hᵢ i.as
```

:::question (questionTitle := "Exercise 16") (questionPage := "221")
Show that if $`{P \xrightarrow{p_a} C_a}`, $`{P \xrightarrow{p_b} C_b}` is a product, and $`{Q \xrightarrow{q} P}`, $`{Q \xrightarrow{q_c} C_c}` is a product, then $`{Q \xrightarrow{p_a q} C_a}`, $`{Q \xrightarrow{p_b q} C_b}`, $`{Q \xrightarrow{q_c} C_c}` is a triple product, i.e. has the appropriate universal mapping property comparing it with all $`{X \xrightarrow{f_a} C_a}`, $`{X \xrightarrow{f_b} C_b}`, $`{X \xrightarrow{f_c} C_c}`
:::

:::solution (solutionTo := "Exercise 16")
```savedComment
Exercise IV.16 (p. 221)
```

We first prove the statement for this exercise using the notation in the book.

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] (C_a C_b C_c : 𝒞)
    (P : 𝒞) (p_a : P ⟶ C_a) (p_b : P ⟶ C_b)
    (h_prodP : ∀ (X : 𝒞) (f₁ : X ⟶ C_a) (f₂ : X ⟶ C_b),
        ∃! f : X ⟶ P, p_a ⊚ f = f₁ ∧ p_b ⊚ f = f₂)
    (Q : 𝒞) (q : Q ⟶ P) (q_c : Q ⟶ C_c)
    (h_prodQ : ∀ (X : 𝒞) (f₁ : X ⟶ P) (f₂ : X ⟶ C_c),
        ∃! f : X ⟶ Q, q ⊚ f = f₁ ∧ q_c ⊚ f = f₂)
    : ∀ (X : 𝒞) (f_a : X ⟶ C_a) (f_b : X ⟶ C_b) (f_c : X ⟶ C_c),
        ∃! f : X ⟶ Q, p_a ⊚ q ⊚ f = f_a ∧
                       p_b ⊚ q ⊚ f = f_b ∧
                       q_c ⊚ f = f_c := by
  intro X f_a f_b f_c
  obtain ⟨f_p, ⟨hf_a, hf_b⟩, h_uniqP⟩ := by exact h_prodP X f_a f_b
  obtain ⟨f, ⟨hf_p, hf_c⟩, h_uniqQ⟩ := by exact h_prodQ X f_p f_c
  use f
  and_intros
  · -- Show that p_a q f = f_a
    rw [hf_p, hf_a]
  · -- Show that p_b q f = f_b
    rw [hf_p, hf_b]
  · -- Show that q_c f = f_c
    rw [hf_c]
  · -- Show uniqueness
    intro m ⟨hm_a, hm_b, hm_c⟩
    apply h_uniqQ
    constructor
    · apply h_uniqP
      constructor
      · exact hm_a
      · exact hm_b
    · exact hm_c
```

We then give the same proof using the mathlib API for products.

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞] (C_a C_b C_c : 𝒞)
    (coneP : Fan (fun | 0 => C_a | 1 => C_b : Fin 2 → 𝒞))
    (prodP : IsLimit coneP)
    (coneQ : Fan (fun | 0 => coneP.pt | 1 => C_c : Fin 2 → 𝒞))
    (prodQ : IsLimit coneQ)
    : IsLimit (
        Fan.mk coneQ.pt (fun i : Fin 3 ↦ match i with
          | 0 => coneP.π.app ⟨0⟩ ⊚ coneQ.π.app ⟨0⟩
          | 1 => coneP.π.app ⟨1⟩ ⊚ coneQ.π.app ⟨0⟩
          | 2 => coneQ.π.app ⟨1⟩)
          : Fan (fun | 0 => C_a | 1 => C_b | 2 => C_c)
      ) := by
  refine IsLimit.mk ?_ ?_ ?_
  · -- lift
    intro coneX
    exact prodQ.lift (Fan.mk coneX.pt (fun
      | 0 => prodP.lift (Fan.mk coneX.pt (fun
        | 0 => coneX.π.app ⟨0⟩
        | 1 => coneX.π.app ⟨1⟩))
      | 1 => coneX.π.app ⟨2⟩))
  · -- fac
    intro coneX i
    fin_cases i
    · -- Show that p_a q f = f_a
      dsimp
      erw [← Category.assoc, prodQ.fac]
      exact prodP.fac _ ⟨0⟩
    · -- Show that p_b q f = f_b
      dsimp
      erw [← Category.assoc, prodQ.fac]
      exact prodP.fac _ ⟨1⟩
    · -- Show that q_c f = f_c
      exact prodQ.fac _ ⟨1⟩
  · -- uniq
    intro coneX m hm
    refine prodQ.uniq (Fan.mk coneX.pt (fun
      | 0 => prodP.lift (Fan.mk coneX.pt (fun
              | 0 => coneX.π.app ⟨0⟩
              | 1 => coneX.π.app ⟨1⟩))
      | 1 => coneX.π.app ⟨2⟩)) m ?_
    intro i
    fin_cases i
    · refine prodP.uniq (Fan.mk coneX.pt (fun
        | 0 => coneX.π.app ⟨0⟩
        | 1 => coneX.π.app ⟨1⟩)) _ ?_
      intro i
      fin_cases i
      · erw [Category.assoc]
        exact hm ⟨0⟩
      · erw [Category.assoc]
        exact hm ⟨1⟩
    · exact hm ⟨2⟩
```
:::

# 6. Sums

:::definition (definitionTerm := "Sum") (definitionPage := "222")
A pair $`{B_1 \xrightarrow{j_1} S}`, $`{B_2 \xrightarrow{j_2} S}`, of maps in a category makes $`S` a _sum_ of $`B_1` and $`B_2` if for each object $`Y` and each pair $`{B_1 \xrightarrow{g_1} Y}`, $`{B_2 \xrightarrow{g_2} Y}`, there is exactly one map $`{S \xrightarrow{g} Y}` for which both $`{g_1 = g j_1}` and $`{g_2 = g j_2}`.
:::

In mathlib, the categorical sum (binary coproduct) is formalised as the colimit of a discrete diagram containing a pair of objects. The data (the sum object $`S` and its _injections_ $`j_1` and $`j_2`) are bundled into the `BinaryCofan` type, which is a cocone on a diagram indexed by the discrete category on the inductive type `WalkingPair`. The universal property is asserted by the `IsColimit` structure applied to that cocone. We print the `BinaryCofan` and `IsColimit` definitions below for reference.

```lean (name := out_BinaryCofan)
#print BinaryCofan
```

```leanOutput out_BinaryCofan
@[reducible] def CategoryTheory.Limits.BinaryCofan.{v, u} : {C : Type u} →
  [Category.{v, u} C] → C → C → Type (max (max 0 u) v) :=
fun {C} [Category.{v, u} C] X Y ↦ Cocone (pair X Y)
```

```lean (name := out_IsColimit)
#print IsColimit
```

```leanOutput out_IsColimit
structure CategoryTheory.Limits.IsColimit.{v₁, v₃, u₁, u₃} {J : Type u₁} [Category.{v₁, u₁} J] {C : Type u₃}
  [Category.{v₃, u₃} C] {F : J ⥤ C} (t : Cocone F) : Type (max (max u₁ u₃) v₃)
number of parameters: 6
fields:
  CategoryTheory.Limits.IsColimit.desc : (s : Cocone F) → t.pt ⟶ s.pt
  CategoryTheory.Limits.IsColimit.fac : ∀ (s : Cocone F) (j : J), self.desc s ⊚ t.ι.app j = s.ι.app j := by
    cat_disch
  CategoryTheory.Limits.IsColimit.uniq : ∀ (s : Cocone F) (m : t.pt ⟶ s.pt),
      (∀ (j : J), m ⊚ t.ι.app j = s.ι.app j) → m = self.desc s := by
    cat_disch
constructor:
  CategoryTheory.Limits.IsColimit.mk.{v₁, v₃, u₁, u₃} {J : Type u₁} [Category.{v₁, u₁} J] {C : Type u₃}
    [Category.{v₃, u₃} C] {F : J ⥤ C} {t : Cocone F} (desc : (s : Cocone F) → t.pt ⟶ s.pt)
    (fac : ∀ (s : Cocone F) (j : J), desc s ⊚ t.ι.app j = s.ι.app j := by cat_disch)
    (uniq : ∀ (s : Cocone F) (m : t.pt ⟶ s.pt), (∀ (j : J), m ⊚ t.ι.app j = s.ι.app j) → m = desc s := by cat_disch) :
    IsColimit t
```

We show that the formalisation in mathlib of the binary coproduct is equivalent to the definition of sum given in the book (cf. binary product above).

```savedComment
Sum (p. 222)
```

```savedLean
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (S B₁ B₂ : 𝒞) (j₁ : B₁ ⟶ S) (j₂ : B₂ ⟶ S)
    : Nonempty (IsColimit (BinaryCofan.mk j₁ j₂)) ↔
      ∀ (Y : 𝒞) (g₁ : B₁ ⟶ Y) (g₂ : B₂ ⟶ Y),
          ∃! g : S ⟶ Y, g ⊚ j₁ = g₁ ∧ g ⊚ j₂ = g₂ := by
  constructor
  · rintro ⟨h⟩ Y g₁ g₂
    let s := BinaryCofan.mk g₁ g₂
    use h.desc s
    and_intros
    · exact (h.fac s ⟨WalkingPair.left⟩)
    · exact (h.fac s ⟨WalkingPair.right⟩)
    · intro m ⟨h₁, h₂⟩
      apply h.uniq s
      rintro ⟨_ | _⟩
      all_goals
        dsimp
        first | erw [h₁] | erw [h₂]
        rfl
  · intro h
    constructor
    let hs (s : BinaryCofan B₁ B₂) :=
      let g₁ : B₁ ⟶ s.pt := s.ι.app ⟨WalkingPair.left⟩
      let g₂ : B₂ ⟶ s.pt := s.ι.app ⟨WalkingPair.right⟩
      h s.pt g₁ g₂
    refine IsColimit.mk ?_ ?_ ?_
    · -- desc
      intro s
      exact (hs s).choose
    · -- fac
      intro s j
      rcases j with ⟨_ | _⟩
      · exact (hs s).choose_spec.1.1
      · exact (hs s).choose_spec.1.2
    · -- uniq
      intro s m w
      apply (hs s).choose_spec.2
      constructor
      · exact (w ⟨WalkingPair.left⟩)
      · exact (w ⟨WalkingPair.right⟩)
```

:::question (questionTitle := "Exercise 17") (questionPage := "222")
In 𝑺, 𝑺⇊, and 𝑺↻, sums have the property that any point of $`{B_1 + B_2}` comes via injection from a point of exactly one of $`B_1`, $`B_2`.
:::

:::solution (solutionTo := "Exercise 17")
```savedComment
Exercise IV.17 (p. 222)
```

Our proof for 𝑺 is given below, with inline comments explaining the various steps.

```savedLean
example (S B₁ B₂ : Type) (j₁ : B₁ ⟶ S) (j₂ : B₂ ⟶ S)
    (h_sum : ∀ (Y : Type) (g₁ : B₁ ⟶ Y) (g₂ : B₂ ⟶ Y),
        ∃! g : S ⟶ Y, (g ⊚ j₁ = g₁ ∧ g ⊚ j₂ = g₂))
    : ∀ s : Unit ⟶ S,
        Xor' (∃ b₁ : Unit ⟶ B₁, j₁ ⊚ b₁ = s)
             (∃ b₂ : Unit ⟶ B₂, j₂ ⊚ b₂ = s) := by
  intro s
  -- Construct a concrete disjoint union Y
  -- such that the left component tagged as true implies
  -- the right component contains an element of B₁
  -- and the left component tagged as false implies
  -- the right component contains an element of B₂
  let Y := (b : Bool) × (fun | true => B₁ | false => B₂) b
  -- Create the injections from B₁ and B₂ into Y
  let g₁ : B₁ ⟶ Y := fun x ↦ ⟨true, x⟩
  let g₂ : B₂ ⟶ Y := fun x ↦ ⟨false, x⟩
  -- Use the universal property to get a unique g : S ⟶ Y
  -- such that g ⊚ j₁ = g₁ and g ⊚ j₂ = g₂
  obtain ⟨g, ⟨hg₁, hg₂⟩, _⟩ := h_sum Y g₁ g₂
  -- Create a morphism f that sends the right component of Y to S
  -- via the injection j₁ (when tagged true) or j₂ (when tagged false)
  let f : Y ⟶ S := fun
    | ⟨true, val⟩ => j₁ val
    | ⟨false, val⟩ => j₂ val
  -- Show that f ⊚ g = 𝟙 S
  obtain ⟨e, _, h_uniq⟩ := h_sum S j₁ j₂
  have h_fg_e : f ⊚ g = e := by
    apply h_uniq
    and_intros
    · rw [← Category.assoc, hg₁]
      rfl
    · rw [← Category.assoc, hg₂]
      rfl
  have h_id_e : 𝟙 S = e := by
    apply h_uniq
    exact ⟨rfl, rfl⟩
  have h_fg_id : f ⊚ g = 𝟙 S := by
    rw [h_fg_e, h_id_e]
  have hfgs : f ⊚ g ⊚ s = s := by
    rw [Category.assoc, h_fg_id]
    rfl
  -- Perform case analysis on (g ⊚ s) ()
  match hgs : (g ⊚ s) () with
  | ⟨true, x₁⟩ =>
      left
      refine ⟨⟨fun _ => x₁, ?_⟩, ?_⟩
      · -- Prove existence
        funext ()
        calc j₁ x₁
         _ = f ⟨true, x₁⟩     := rfl
         _ = f ((g ⊚ s) ())  := by rw [hgs]
         _ = (f ⊚ g ⊚ s) () := by rw [types_comp_apply (g ⊚ s) f]
         _ = s ()             := by rw [hfgs]
      · -- Prove exclusivity
        rintro ⟨b₂, hb₂⟩
        have h_contra : ⟨false, b₂ ()⟩ = (⟨true, x₁⟩ : Y) :=
          calc ⟨false, b₂ ()⟩
            _ = (g₂ ⊚ b₂) ()        := rfl
            _ = ((g ⊚ j₂) ⊚ b₂) () := by rw [hg₂]
            _ = (g ⊚ j₂ ⊚ b₂) ()   := by rw [Category.assoc]
            _ = (g ⊚ s) ()          := by rw [hb₂]
            _ = ⟨true, x₁⟩           := hgs
        have : false = true := congr_arg Sigma.fst h_contra
        contradiction
  | ⟨false, x₂⟩ =>
      right
      refine ⟨⟨fun _ => x₂, ?_⟩, ?_⟩
      · -- Prove existence
        funext ()
        calc j₂ x₂
         _ = f ⟨false, x₂⟩    := rfl
         _ = f ((g ⊚ s) ())  := by rw [hgs]
         _ = (f ⊚ g ⊚ s) () := by rw [types_comp_apply (g ⊚ s) f]
         _ = s ()             := by rw [hfgs]
      · -- Prove exclusivity
        rintro ⟨b₁, hb₁⟩
        have h_contra : ⟨true, b₁ ()⟩ = (⟨false, x₂⟩ : Y) :=
          calc ⟨true, b₁ ()⟩
            _ = (g₁ ⊚ b₁) ()        := rfl
            _ = ((g ⊚ j₁) ⊚ b₁) () := by rw [hg₁]
            _ = (g ⊚ j₁ ⊚ b₁) ()   := by rw [Category.assoc]
            _ = (g ⊚ s) ()          := by rw [hb₁]
            _ = ⟨false, x₂⟩          := hgs
        have : true = false := congr_arg Sigma.fst h_contra
        contradiction
```

The proof for 𝑺↻ follows the same line of reasoning as that for 𝑺, though is slightly longer to handle the additional structure of 𝑺↻.

```savedLean
example (S B₁ B₂ : SetWithEndomap) (j₁ : B₁ ⟶ S) (j₂ : B₂ ⟶ S)
    (h_sum : ∀ (Y : SetWithEndomap) (g₁ : B₁ ⟶ Y) (g₂ : B₂ ⟶ Y),
        ∃! g : S ⟶ Y, (g ⊚ j₁ = g₁ ∧ g ⊚ j₂ = g₂))
    : ∀ s : termSWE ⟶ S,
        Xor' (∃ b₁ : termSWE ⟶ B₁, j₁ ⊚ b₁ = s)
             (∃ b₂ : termSWE ⟶ B₂, j₂ ⊚ b₂ = s) := by
  intro s
  -- Set up
  let Y : SetWithEndomap := {
    carrier := Sum B₁.carrier B₂.carrier
    toEnd := fun
      | Sum.inl b1 => Sum.inl (B₁.toEnd b1)
      | Sum.inr b2 => Sum.inr (B₂.toEnd b2)
  }
  let g₁ : B₁ ⟶ Y := ⟨Sum.inl, rfl⟩
  let g₂ : B₂ ⟶ Y := ⟨Sum.inr, rfl⟩
  obtain ⟨g, ⟨hg₁, hg₂⟩, _⟩ := h_sum Y g₁ g₂
  let f : Y ⟶ S := ⟨
    fun
      | Sum.inl b1 => j₁.val b1
      | Sum.inr b2 => j₂.val b2,
    by
      ext (b1 | b2)
      · exact congr_fun j₁.property b1
      · exact congr_fun j₂.property b2
  ⟩
  obtain ⟨e, _, h_uniq⟩ := h_sum S j₁ j₂
  have h_fg_e : f ⊚ g = e := by
    apply h_uniq
    and_intros
    · rw [← Category.assoc, hg₁]
      rfl
    · rw [← Category.assoc, hg₂]
      rfl
  have h_id_e : 𝟙 S = e := by
    apply h_uniq
    exact ⟨rfl, rfl⟩
  have h_fg_id : f ⊚ g = 𝟙 S := by
    rw [h_fg_e, h_id_e]
  have hfgs : f ⊚ g ⊚ s = s := by
    rw [Category.assoc, h_fg_id]
    rfl
  have hfgs' : (f ⊚ g ⊚ s).val () = s.val () := by
    rw [hfgs]
  -- Perform case analysis on (g ⊚ s).val ()
  match hgs : (g ⊚ s).val () with
  | Sum.inl x₁ =>
      left
      refine ⟨⟨⟨
        fun _ => x₁,
        by
          funext ()
          have hgs_comm := congr_fun (g ⊚ s).property ()
          dsimp [termSWE] at hgs_comm
          erw [hgs] at hgs_comm
          exact Sum.inl.inj hgs_comm
      ⟩, ?_⟩, ?_⟩
      · -- Prove existence
        apply Subtype.ext
        funext ()
        calc j₁.val x₁
          _ = f.val (Sum.inl x₁)      := rfl
          _ = f.val ((g ⊚ s).val ()) := by rw [hgs]
          _ = s.val ()                := hfgs'
      · -- Prove exclusivity
        rintro ⟨b₂, hb₂⟩
        have h_contra : Sum.inr (b₂.val ()) = Sum.inl x₁ :=
          calc Sum.inr (b₂.val ())
            _ = (g₂ ⊚ b₂).val ()        := rfl
            _ = ((g ⊚ j₂) ⊚ b₂).val () := by rw [hg₂]
            _ = (g ⊚ j₂ ⊚ b₂).val ()   := by rw [Category.assoc]
            _ = (g ⊚ s).val ()          := by rw [hb₂]
            _ = Sum.inl x₁               := hgs
        contradiction
  | Sum.inr x₂ =>
      right
      refine ⟨⟨⟨
        fun _ => x₂,
        by
          funext ()
          have hgs_comm := congr_fun (g ⊚ s).property ()
          dsimp [termSWE] at hgs_comm
          erw [hgs] at hgs_comm
          exact Sum.inr.inj hgs_comm
      ⟩, ?_⟩, ?_⟩
      · -- Prove existence
        apply Subtype.ext
        funext ()
        calc j₂.val x₂
          _ = f.val (Sum.inr x₂)      := rfl
          _ = f.val ((g ⊚ s).val ()) := by rw [hgs]
          _ = s.val ()                := hfgs'
      · -- Prove exclusivity
        rintro ⟨b₁, hb₁⟩
        have h_contra : Sum.inl (b₁.val ()) = Sum.inr x₂ :=
          calc Sum.inl (b₁.val ())
            _ = (g₁ ⊚ b₁).val ()        := rfl
            _ = ((g ⊚ j₁) ⊚ b₁).val () := by rw [hg₁]
            _ = (g ⊚ j₁ ⊚ b₁).val ()   := by rw [Category.assoc]
            _ = (g ⊚ s).val ()          := by rw [hb₁]
            _ = Sum.inr x₂               := hgs
        contradiction
```

The proof for 𝑺⇊ is a direct translation into the graph structure of the proof for 𝑺↻ (and is again somewhat longer in consequence).

```savedLean
example (S B₁ B₂ : IrreflexiveGraph) (j₁ : B₁ ⟶ S) (j₂ : B₂ ⟶ S)
    (h_sum : ∀ (Y : IrreflexiveGraph) (g₁ : B₁ ⟶ Y) (g₂ : B₂ ⟶ Y),
        ∃! g : S ⟶ Y, (g ⊚ j₁ = g₁ ∧ g ⊚ j₂ = g₂))
    : ∀ s : termIG ⟶ S,
        Xor' (∃ b₁ : termIG ⟶ B₁, j₁ ⊚ b₁ = s)
             (∃ b₂ : termIG ⟶ B₂, j₂ ⊚ b₂ = s) := by
  intro s
  -- Set up
  let Y : IrreflexiveGraph := {
    carrierA := Sum B₁.carrierA B₂.carrierA
    carrierD := Sum B₁.carrierD B₂.carrierD
    toSrc := fun
      | Sum.inl b1 => Sum.inl (B₁.toSrc b1)
      | Sum.inr b2 => Sum.inr (B₂.toSrc b2)
    toTgt := fun
      | Sum.inl b1 => Sum.inl (B₁.toTgt b1)
      | Sum.inr b2 => Sum.inr (B₂.toTgt b2)
  }
  let g₁ : B₁ ⟶ Y := ⟨⟨Sum.inl, Sum.inl⟩, ⟨rfl, rfl⟩⟩
  let g₂ : B₂ ⟶ Y := ⟨⟨Sum.inr, Sum.inr⟩, ⟨rfl, rfl⟩⟩
  obtain ⟨g, ⟨hg₁, hg₂⟩, _⟩ := h_sum Y g₁ g₂
  let f : Y ⟶ S := ⟨(
      fun
        | Sum.inl bA1 => j₁.val.1 bA1
        | Sum.inr bA2 => j₂.val.1 bA2,
      fun
        | Sum.inl bD1 => j₁.val.2 bD1
        | Sum.inr bD2 => j₂.val.2 bD2
    ),
    by
      constructor
      · ext (bA1 | bA2)
        · exact congr_fun j₁.property.1 bA1
        · exact congr_fun j₂.property.1 bA2
      · ext (bD1 | bD2)
        · exact congr_fun j₁.property.2 bD1
        · exact congr_fun j₂.property.2 bD2
  ⟩
  obtain ⟨e, _, h_uniq⟩ := h_sum S j₁ j₂
  have h_fg_e : f ⊚ g = e := by
    apply h_uniq
    and_intros
    · rw [← Category.assoc, hg₁]
      rfl
    · rw [← Category.assoc, hg₂]
      rfl
  have h_id_e : 𝟙 S = e := by
    apply h_uniq
    exact ⟨rfl, rfl⟩
  have h_fg_id : f ⊚ g = 𝟙 S := by
    rw [h_fg_e, h_id_e]
  have hfgs : f ⊚ g ⊚ s = s := by
    rw [Category.assoc, h_fg_id]
    rfl
  have hfgsA : (f ⊚ g ⊚ s).val.1 () = s.val.1 () := by
    rw [hfgs]
  have hfgsD : (f ⊚ g ⊚ s).val.2 () = s.val.2 () := by
    rw [hfgs]
  -- Perform case analysis on (g ⊚ s).val.1 (), (g ⊚ s).val.2 ()
  match hgsA : (g ⊚ s).val.1 (), hgsD : (g ⊚ s).val.2 () with
  | Sum.inl x₁A, Sum.inl x₁D =>
      left
      refine ⟨⟨⟨
        (fun _ => x₁A, fun _ => x₁D),
        by
          constructor
          · funext ()
            have hgsSrc_comm := congr_fun (g ⊚ s).property.1 ()
            dsimp [termIG] at hgsSrc_comm
            erw [hgsA, hgsD] at hgsSrc_comm
            exact Sum.inl.inj hgsSrc_comm
          · funext ()
            have hgsTgt_comm := congr_fun (g ⊚ s).property.2 ()
            dsimp [termIG] at hgsTgt_comm
            erw [hgsA, hgsD] at hgsTgt_comm
            exact Sum.inl.inj hgsTgt_comm
      ⟩, ?_⟩, ?_⟩
      · -- Prove existence
        apply Subtype.ext
        apply Prod.ext
        · funext ()
          calc j₁.val.1 x₁A
            _ = f.val.1 (Sum.inl x₁A)       := rfl
            _ = f.val.1 ((g ⊚ s).val.1 ()) := by rw [hgsA]
            _ = s.val.1 ()                  := hfgsA
        · funext ()
          calc j₁.val.2 x₁D
            _ = f.val.2 (Sum.inl x₁D)       := rfl
            _ = f.val.2 ((g ⊚ s).val.2 ()) := by rw [hgsD]
            _ = s.val.2 ()                  := hfgsD
      · -- Prove exclusivity
        rintro ⟨b₂, hb₂⟩
        have h_contra : Sum.inr (b₂.val.1 ()) = Sum.inl x₁A :=
          calc Sum.inr (b₂.val.1 ())
            _ = (g₂ ⊚ b₂).val.1 ()        := rfl
            _ = ((g ⊚ j₂) ⊚ b₂).val.1 () := by rw [hg₂]
            _ = (g ⊚ j₂ ⊚ b₂).val.1 ()   := by rw [Category.assoc]
            _ = (g ⊚ s).val.1 ()          := by rw [hb₂]
            _ = Sum.inl x₁A                := hgsA
        contradiction
  | Sum.inr x₂A, Sum.inr x₂D =>
      right
      refine ⟨⟨⟨
        (fun _ => x₂A, fun _ => x₂D),
        by
          constructor
          · funext ()
            have hgsSrc_comm := congr_fun (g ⊚ s).property.1 ()
            dsimp [termIG] at hgsSrc_comm
            erw [hgsA, hgsD] at hgsSrc_comm
            exact Sum.inr.inj hgsSrc_comm
          · funext ()
            have hgsTgt_comm := congr_fun (g ⊚ s).property.2 ()
            dsimp [termIG] at hgsTgt_comm
            erw [hgsA, hgsD] at hgsTgt_comm
            exact Sum.inr.inj hgsTgt_comm
      ⟩, ?_⟩, ?_⟩
      · -- Prove existence
        apply Subtype.ext
        apply Prod.ext
        · funext ()
          calc j₂.val.1 x₂A
            _ = f.val.1 (Sum.inr x₂A)       := rfl
            _ = f.val.1 ((g ⊚ s).val.1 ()) := by rw [hgsA]
            _ = s.val.1 ()                  := hfgsA
        · funext ()
          calc j₂.val.2 x₂D
            _ = f.val.2 (Sum.inr x₂D)       := rfl
            _ = f.val.2 ((g ⊚ s).val.2 ()) := by rw [hgsD]
            _ = s.val.2 ()                  := hfgsD
      · -- Prove exclusivity
        rintro ⟨b₁, hb₁⟩
        have h_contra : Sum.inl (b₁.val.1 ()) = Sum.inr x₂A :=
          calc Sum.inl (b₁.val.1 ())
            _ = (g₁ ⊚ b₁).val.1 ()        := rfl
            _ = ((g ⊚ j₁) ⊚ b₁).val.1 () := by rw [hg₁]
            _ = (g ⊚ j₁ ⊚ b₁).val.1 ()   := by rw [Category.assoc]
            _ = (g ⊚ s).val.1 ()          := by rw [hb₁]
            _ = Sum.inr x₂A                := hgsA
        contradiction
  -- Handle unreachable cases
  | Sum.inl xA, Sum.inr xD =>
      have h_contra := congr_fun (g ⊚ s).property.1 ()
      dsimp [termIG] at h_contra
      erw [hgsA, hgsD] at h_contra
      contradiction
  | Sum.inr xA, Sum.inl xD =>
      have h_contra := congr_fun (g ⊚ s).property.1 ()
      dsimp [termIG] at h_contra
      erw [hgsA, hgsD] at h_contra
      contradiction
```
:::

:::question (questionTitle := "Exercise 18") (questionPage := "222")
In 𝑺, there are many maps $`{X \rightarrow \mathbf{1}+\mathbf{1}}` (if $`{X \ne \mathbf{0},\mathbf{1}}`) which do not factor through either injection. (Give examples.)
:::

:::solution (solutionTo := "Exercise 18")
```savedComment
Exercise IV.18 (p. 222)
```

```savedLean -show
namespace ExIV_18
```

We give a simple example in which $`X` is a type with two elements. (We could use any type for $`X` that has two or more elements—i.e., is neither initial nor terminal in 𝑺).

```savedLean
abbrev X := Fin 2
```

Also, since we are using the category `Type` in place of 𝑺, we take the opportunity to introduce the inductive data type `Sum`. `Sum` is the disjoint union of types `α` and `β`, ordinarily written `α ⊕ β`, with left injection provided by `Sum.inl` and right injection by `Sum.inr`.

We define the left and right factor maps.

```savedLean
def f₁ : X ⟶ Unit := fun _ ↦ ()
def j₁ : Unit ⟶ Unit ⊕ Unit := fun _ ↦ Sum.inl ()
def f₂ : X ⟶ Unit := fun _ ↦ ()
def j₂ : Unit ⟶ Unit ⊕ Unit := fun _ ↦ Sum.inr ()
```

The map $`f` factors through the left injection $`j_1` if $`{f = j_1 f_1}`, and it factors through the right injection $`j_2` if $`{f = j_2 f_2}`. But taking $`f` to be

```savedLean
def f : X ⟶ Unit ⊕ Unit
  | 0 => Sum.inl ()
  | 1 => Sum.inr ()
```

we can show that $`f` does not factor through either injection.

```savedLean
example : ∃ f' : X ⟶ Unit ⊕ Unit,
    f' ≠ j₁ ⊚ f₁ ∧ f' ≠ j₂ ⊚ f₂ := by
  use f
  constructor
  · intro h
    have h_contra : Sum.inr () = Sum.inl () :=
      calc Sum.inr ()
        _ = f 1          := rfl
        _ = (j₁ ⊚ f₁) 1 := by rw [h]
        _ = (j₁ ⊚ f₁) 0 := rfl
        _ = f 0          := rfl
        _ = Sum.inl ()   := rfl
    contradiction
  · intro h
    have h_contra : Sum.inl () = Sum.inr () :=
      calc Sum.inl ()
        _ = f 0          := rfl
        _ = (j₂ ⊚ f₂) 0 := by rw [h]
        _ = (j₂ ⊚ f₂) 1 := rfl
        _ = f 1          := rfl
        _ = Sum.inr ()   := rfl
    contradiction
```

```savedLean -show
end ExIV_18
```
:::

:::question (questionTitle := "Exercise 19") (questionPage := "222")
Show that in a category with sums of pairs of objects, the 'iterated sums'
$$`(A+B)+C \quad\text{and}\quad A+(B+C)`
are isomorphic.
:::

:::solution (solutionTo := "Exercise 19")
```savedComment
Exercise IV.19 (p. 222)
```

A manual proof using only the book defintion of sum is given below.

```savedLean
noncomputable example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (A B C AB BC AB_C A_BC : 𝒞)
    (j₁ : A ⟶ AB) (j₂ : B ⟶ AB) (j₃ : AB ⟶ AB_C) (j₄ : C ⟶ AB_C)
    (hAB : ∀ (Y : 𝒞) (g₁ : A ⟶ Y) (g₂ : B ⟶ Y),
        ∃! g : AB ⟶ Y, (g ⊚ j₁ = g₁ ∧ g ⊚ j₂ = g₂))
    (hAB_C : ∀ (Y : 𝒞) (g₁ : AB ⟶ Y) (g₂ : C ⟶ Y),
        ∃! g : AB_C ⟶ Y, (g ⊚ j₃ = g₁ ∧ g ⊚ j₄ = g₂))
    (k₁ : B ⟶ BC) (k₂ : C ⟶ BC) (k₃ : A ⟶ A_BC) (k₄ : BC ⟶ A_BC)
    (hBC : ∀ (Y : 𝒞) (g₁ : B ⟶ Y) (g₂ : C ⟶ Y),
        ∃! g : BC ⟶ Y, (g ⊚ k₁ = g₁ ∧ g ⊚ k₂ = g₂))
    (hA_BC : ∀ (Y : 𝒞) (g₁ : A ⟶ Y) (g₂ : BC ⟶ Y),
        ∃! g : A_BC ⟶ Y, (g ⊚ k₃ = g₁ ∧ g ⊚ k₄ = g₂)) :
    AB_C ≅ A_BC := by
  -- get p : AB ⟶ A_BC from the universal property of AB
  have hp := hAB A_BC k₃ (k₄ ⊚ k₁)
  obtain ⟨⟨hp₁, hp₂⟩, _⟩ := hp.choose_spec
  set p : AB ⟶ A_BC := hp.choose
  -- get q : BC ⟶ AB_C from the universal property of BC
  have hq := hBC AB_C (j₃ ⊚ j₂) j₄
  obtain ⟨⟨hq₁, hq₂⟩, _⟩ := hq.choose_spec
  set q : BC ⟶ AB_C := hq.choose
  -- get f : AB_C ⟶ A_BC from the universal property of AB_C
  have hf := hAB_C A_BC p (k₄ ⊚ k₂)
  obtain ⟨⟨hf₁, hf₂⟩, _⟩ := hf.choose_spec
  set f : AB_C ⟶ A_BC := hf.choose
  -- get g : A_BC ⟶ AB_C from the universal property of A_BC
  have hg := hA_BC AB_C (j₃ ⊚ j₁) q
  obtain ⟨⟨hg₁, hg₂⟩, _⟩ := hg.choose_spec
  set g : A_BC ⟶ AB_C := hg.choose
  -- Show that g ⊚ f = 𝟙 AB_C
  have hgf : g ⊚ f = 𝟙 AB_C := by
    apply ExistsUnique.unique (hAB_C AB_C j₃ j₄)
    · constructor
      · rw [← Category.assoc, hf₁]
        apply ExistsUnique.unique (hAB AB_C (j₃ ⊚ j₁) (j₃ ⊚ j₂))
        · constructor
          · rw [← Category.assoc, hp₁, hg₁]
          · rw [← Category.assoc, hp₂, Category.assoc, hg₂, hq₁]
        · exact ⟨rfl, rfl⟩
      · rw [← Category.assoc, hf₂, Category.assoc, hg₂, hq₂]
    · exact ⟨Category.comp_id j₃, Category.comp_id j₄⟩
  -- Show that f ⊚ g = 𝟙 A_BC
  have hfg : f ⊚ g = 𝟙 A_BC := by
    apply ExistsUnique.unique (hA_BC A_BC k₃ k₄)
    · constructor
      · rw [← Category.assoc, hg₁, Category.assoc, hf₁, hp₁]
      · rw [← Category.assoc, hg₂]
        apply ExistsUnique.unique (hBC A_BC (k₄ ⊚ k₁) (k₄ ⊚ k₂))
        · constructor
          · rw [← Category.assoc, hq₁, Category.assoc, hf₁, hp₂]
          · rw [← Category.assoc, hq₂, hf₂]
        · exact ⟨rfl, rfl⟩
    · exact ⟨Category.comp_id k₃, Category.comp_id k₄⟩
  -- Create the isomorphism structure
  exact {
    hom := f
    inv := g
    hom_inv_id := hgf
    inv_hom_id := hfg
  }
```

The corresponding proof using mathlib's binary coproduct API reduces to the single lemma `coprod.associator`.

```savedLean
noncomputable example {𝒞 : Type u} [Category.{v, u} 𝒞]
    [HasBinaryCoproducts 𝒞] (A B C : 𝒞) :
    (A ⨿ B) ⨿ C ≅ A ⨿ (B ⨿ C) :=
  coprod.associator A B C
```
:::

# 7. Distributive laws

:::definition (definitionTerm := "Distributive law") (definitionPage := "223")
A category is said to satisfy the _distributive law_ if the standard maps...
$$`(A \times B) + (A \times C) \rightarrow A \times (B + C)`
and
$$`\mathbf{0} \rightarrow A \times \mathbf{0}`
are always isomorphisms in the category.
:::

We provide a manual definition following the book.

```savedLean
def DistributiveLaw (T : Type u) [Category.{v, u} T] : Prop :=
  ∀ (A B C AxB AxC AxB_AxC B_C AxB_C : T)
    (p₁ : AxB ⟶ A) (p₂ : AxB ⟶ B)
    (p₃ : AxC ⟶ A) (p₄ : AxC ⟶ C)
    (j₁ : AxB ⟶ AxB_AxC) (j₂ : AxC ⟶ AxB_AxC)
    (j₃ : B ⟶ B_C) (j₄ : C ⟶ B_C)
    (p₅ : AxB_C ⟶ A) (p₆ : AxB_C ⟶ B_C),
    (∀ X f₁ f₂, ∃! f : X ⟶ AxB, p₁ ⊚ f = f₁ ∧ p₂ ⊚ f = f₂) →
    (∀ X f₁ f₂, ∃! f : X ⟶ AxC, p₃ ⊚ f = f₁ ∧ p₄ ⊚ f = f₂) →
    (∀ Y g₁ g₂, ∃! g : AxB_AxC ⟶ Y, g ⊚ j₁ = g₁ ∧ g ⊚ j₂ = g₂) →
    (∀ Y g₁ g₂, ∃! g : B_C ⟶ Y, g ⊚ j₃ = g₁ ∧ g ⊚ j₄ = g₂) →
    (∀ X f₁ f₂, ∃! f : X ⟶ AxB_C, p₅ ⊚ f = f₁ ∧ p₆ ⊚ f = f₂) →
    Nonempty (AxB_AxC ≅ AxB_C)
```

:::question (questionTitle := "Exercise 20") (questionPage := "223")
The category $`\mathbf{1}`/𝑺 of pointed sets does not satisfy the distributive law. Hint: First determine the nature of sums within the category $`\mathbf{1}`/𝑺.
:::

:::solution (solutionTo := "Exercise 20")
```savedComment
Exercise IV.20 (p. 223)
```

```savedLean -show
namespace ExIV_20
```

In the category $`\mathbf{1}`/𝑺 of pointed sets, the sum of two objects is given by the wedge sum, which amalgamates the basepoints of the constituent sets into a single basepoint. Because of this amalgamation, the underlying set of $`{(A \times B) + (A \times C)}` has different cardinality than that of $`{A \times (B + C)}`. We provide a concrete counterexample that exploits this difference in cardinality to show that the standard maps are not always isomorphic in $`\mathbf{1}`/𝑺.

We begin by defining the concrete objects and morphisms of our counterexample.

```savedLean
abbrev A : PointedSet := { carrier := Fin 2, point := fun _ ↦ 0 }
abbrev B : PointedSet := { carrier := Unit, point := id }
abbrev C : PointedSet := { carrier := Unit, point := id }

abbrev AxB : PointedSet := {
  carrier := Fin 2 × Unit
  point := fun _ ↦ (0, ())
}

abbrev AxC : PointedSet := {
  carrier := Fin 2 × Unit
  point := fun _ ↦ (0, ())
}

abbrev AxB_AxC : PointedSet := {
  carrier := (Fin 2 × Unit) ⊕ Unit
  point := fun _ ↦ Sum.inl (0, ())
}

abbrev B_C : PointedSet := { carrier := Unit, point := id }

abbrev AxB_C : PointedSet := {
  carrier := Fin 2 × Unit
  point := fun _ ↦ (0, ())
}

def p₁ : AxB ⟶ A := ⟨fun p ↦ p.1, rfl⟩
def p₂ : AxB ⟶ B := ⟨fun p ↦ p.2, rfl⟩
def p₃ : AxC ⟶ A := ⟨fun p ↦ p.1, rfl⟩
def p₄ : AxC ⟶ C := ⟨fun p ↦ p.2, rfl⟩

def j₁ : AxB ⟶ AxB_AxC := ⟨
  fun
  | (0, _) => Sum.inl (0, ())
  | (1, _) => Sum.inl (1, ()),
  rfl
⟩

def j₂ : AxC ⟶ AxB_AxC := ⟨
  fun
  | (0, _) => Sum.inl (0, ())
  | (1, _) => Sum.inr (),
  rfl
⟩

def j₃ : B ⟶ B_C := ⟨id, rfl⟩
def j₄ : C ⟶ B_C := ⟨id, rfl⟩

def p₅ : AxB_C ⟶ A := ⟨fun p ↦ p.1, rfl⟩
def p₆ : AxB_C ⟶ B_C := ⟨fun p ↦ p.2, rfl⟩
```

Our proof then follows.

```savedLean
example : ¬ DistributiveLaw PointedSet := by
  intro h_distrib
  -- Define a helper to prove the universal property for the products
  let h_univ_prod : ∀ (X : PointedSet) (f₁ : X ⟶ A) (f₂ : X ⟶ B),
      ∃! f, p₁ ⊚ f = f₁ ∧ p₂ ⊚ f = f₂ := by
      intro X f₁ f₂
      -- Provide the witness
      use ⟨fun x ↦ (f₁.val x, f₂.val x), by
        ext
        dsimp
        rw [← types_comp_apply _ f₁.val, f₁.property]; rfl
      ⟩
      constructor
      · -- Verify the diagram commutes
        constructor <;> rfl
      · -- Prove uniqueness
        intro f ⟨hf₁, hf₂⟩
        apply Subtype.ext
        rw [← hf₁]; rfl
  have h_iso := h_distrib A B C AxB AxC AxB_AxC B_C AxB_C
                          p₁ p₂ p₃ p₄ j₁ j₂ j₃ j₄ p₅ p₆
    -- Prove the universal property for AxB
    h_univ_prod
    -- Prove the universal property for AxC
    h_univ_prod
    -- Prove the universal property for AxB_AxC
    (by
      intro Y g₁ g₂
      -- Provide the witness
      use ⟨fun
        | Sum.inl (0, ()) => Y.point ()
        | Sum.inl (1, ()) => g₁.val (1, ())
        | Sum.inr _       => g₂.val (1, ()),
        rfl
      ⟩
      constructor
      · -- Verify the diagram commutes
        constructor
        all_goals
          apply Subtype.ext
          funext x
          match x with
          | (0, _) => first | exact (congr_fun g₁.property ()).symm
                            | exact (congr_fun g₂.property ()).symm
          | (1, _) => rfl
      · -- Prove uniqueness
        intro g ⟨hg₁, hg₂⟩
        apply Subtype.ext
        funext x
        match x with
        | Sum.inl (0, _) => exact (congr_fun g.property ())
        | Sum.inl (1, _) => rw [← hg₁]; rfl
        | Sum.inr _ => rw [← hg₂]; rfl
    )
    -- Prove the universal property for B_C
    (by
      intro Y g₁ g₂
      -- Provide the witness
      use ⟨fun _ ↦ Y.point (), rfl⟩
      constructor
      · -- Verify the diagram commutes
        constructor
        all_goals
          apply Subtype.ext
          funext
          first | exact (congr_fun g₁.property ()).symm
                | exact (congr_fun g₂.property ()).symm
      · -- Prove uniqueness
        intro g ⟨_, _⟩
        apply Subtype.ext
        funext x
        exact (congr_fun g.property ())
    )
    -- Prove the universal property for AxB_C
    h_univ_prod
  obtain ⟨iso⟩ := h_iso
  have h_equiv : AxB_AxC.carrier ≃ AxB_C.carrier := {
    toFun := iso.hom.val
    invFun := iso.inv.val
    left_inv := congrArg Subtype.val iso.hom_inv_id |> congrFun
    right_inv := congrArg Subtype.val iso.inv_hom_id |> congrFun
  }
  exact absurd (Fintype.card_congr h_equiv) (by decide)
```

```savedLean -show
end ExIV_20
```
:::

:::question (questionTitle := "Exercise 21") (questionPage := "223")
If $`A`, $`D` denote the generic arrow and the naked dot in 𝑺⇊, show that
$$`A \times A = A + D + D`
Hint: Besides counting the arrows and dots of an arbitrary graph $`X` (such as $`{X = A \times A}`) via maps $`{A \rightarrow X}`, $`{D \rightarrow X}`, the actual internal structure of $`X` can be calculated by composing these maps with the two maps $`{D \xrightarrow{s} A}`, $`{D \xrightarrow{t} A}`.
:::

:::solution (solutionTo := "Exercise 21")
```savedComment
Exercise IV.21 (p. 223)
```

Our solution this time uses the relevant APIs in mathlib in place of the book definitions, which makes the proof a little more involved, so we have provided a greater than usual number of inline comments to signpost the various steps of the argument.

In outline, though, since $`A` has $`1` arrow and $`2` dots, it follows that $`{A \times A}` has $`{1 \times 1 = 1}` arrow and $`{2 \times 2 = 4}` dots. Label the dots $`{(d₀, d₀)}`, $`{(d₀, d₁)}`, $`{(d₁, d₀)}`, and $`{(d₁, d₁)}`. Now, the source of the single arrow in $`{A \times A}` is $`{(d₀, d₀)}` and the target is $`{(d₁, d₁)}`, which leaves two 'naked dots' $`{(d₀, d₁)}` and $`{(d₁, d₀)}`. That is, $`{A \times A}` is exactly the disjoint union of one copy of $`A` and two copies of $`D`. In other words, $`{A \times A = A+D+D}`, which we prove up to isomorphism in the code that follows.

```savedLean
open IrreflexiveGraph in
example
    (coneAA : BinaryFan A A)
    (limitAA : IsLimit coneAA)
    (coconeADD : Cofan (fun | 0 => A | 1 => D | 2 => D :
        Fin 3 → IrreflexiveGraph))
    (colimitADD : IsColimit coconeADD) :
  coneAA.pt ≅ coconeADD.pt := by
    -- Improve readability
    set AA : IrreflexiveGraph := coneAA.pt with hAA
    set ADD : IrreflexiveGraph := coconeADD.pt with hADD
    set p₁ := coneAA.π.app ⟨WalkingPair.left⟩ with hp₁ -- 𝐀×A ⟶ A
    set p₂ := coneAA.π.app ⟨WalkingPair.right⟩ with hp₂ -- A×𝐀 ⟶ A
    set j₁ := coconeADD.ι.app ⟨0⟩ with hj₁ -- A ⟶ 𝐀+D+D
    set j₂ := coconeADD.ι.app ⟨1⟩ with hj₂ -- D ⟶ A+𝐃+D
    set j₃ := coconeADD.ι.app ⟨2⟩ with hj₃ -- D ⟶ A+D+𝐃
    dsimp at p₁ p₂ j₁ j₂ j₃
    let d₀ : Fin 2 := 0 -- first dot of A
    let d₁ : Fin 2 := 1 -- second dot of A
    -- Construct morphism f : A×A ⟶ A+D+D
    let f : AA ⟶ ADD :=
      let fA : AA.carrierA ⟶ ADD.carrierA := fun _ ↦ j₁.val.1 ()
      let fD : AA.carrierD ⟶ ADD.carrierD := fun x ↦
        match ((p₁.val.2 x, p₂.val.2 x) : Fin 2 × Fin 2) with
        | (0, 0) => j₁.val.2 d₀
        | (0, 1) => j₂.val.2 ()
        | (1, 0) => j₃.val.2 ()
        | (1, 1) => j₁.val.2 d₁
      ⟨(fA, fD), by
        constructor
        · -- Show that source commutes
          funext x
          dsimp [fA, fD]
          -- lhs (fD ⊚ AA.toSrc = j₁.val.2)
          have hl₁ : p₁.val.2 (AA.toSrc x) = d₀ :=
            congr_fun p₁.property.1 x
          have hl₂ : p₂.val.2 (AA.toSrc x) = d₀ :=
            congr_fun p₂.property.1 x
          -- rhs (j₁.val.2 = ADD.toSrc ⊚ fA)
          have hr : j₁.val.2 d₀ = ADD.toSrc (j₁.val.1 ()) :=
            congr_fun j₁.property.1 ()
          rw [hl₁, hl₂, hr]
        · -- Show that target commutes
          funext x
          dsimp [fA, fD]
          -- lhs (fD ⊚ AA.toTgt = j₁.val.2)
          have hl₁ : p₁.val.2 (AA.toTgt x) = d₁ :=
            congr_fun p₁.property.2 x
          have hl₂ : p₂.val.2 (AA.toTgt x) = d₁ :=
            congr_fun p₂.property.2 x
          -- rhs (j₁.val.2 = ADD.toTgt ⊚ fA)
          have hr : j₁.val.2 d₁ = ADD.toTgt (j₁.val.1 ()) :=
            congr_fun j₁.property.2 ()
          rw [hl₁, hl₂, hr]⟩
    -- Construct s which maps unique dot of D to first dot of A
    let s : D ⟶ A := ⟨
      (Empty.elim, fun _ ↦ d₀), ⟨rfl, funext fun e ↦ Empty.elim e⟩
    ⟩
    -- Construct t which maps unique dot of D to second dot of A
    let t : D ⟶ A := ⟨
      (Empty.elim, fun _ ↦ d₁), ⟨funext fun e ↦ Empty.elim e, rfl⟩
    ⟩
    -- Construct cocone over A, D, D with vertex A×A
    let coconeAA : Cofan (fun | 0 => A | 1 => D | 2 => D :
        Fin 3 → IrreflexiveGraph) :=
      Cofan.mk coneAA.pt (fun
        | 0 => limitAA.lift (BinaryFan.mk (𝟙 A) (𝟙 A))
        | 1 => limitAA.lift (BinaryFan.mk s t)
        | 2 => limitAA.lift (BinaryFan.mk t s))
    -- Construct morphism f⁻¹ : A+D+D ⟶ A×A
    let finv : ADD ⟶ AA := colimitADD.desc coconeAA
    exact {
      hom := f
      inv := finv
      hom_inv_id := by
        apply BinaryFan.IsLimit.hom_ext limitAA
        · -- Show that p₁ ⊚ finv ⊚ f = p₁ ⊚ 𝟙 AA
          apply IrreflexiveGraph.hom_ext
          · -- Case fA (morphisms for arrows)
            rfl
          · -- Case fD (morphisms for dots)
            funext x
            change (p₁ ⊚ finv).val.2 (f.val.2 x) = p₁.val.2 x
            dsimp [f]
            generalize p₁.val.2 x = x₁, p₂.val.2 x = x₂
            change Fin 2 at x₁ x₂
            fin_cases x₁ <;> fin_cases x₂
            · change (p₁ ⊚ finv ⊚ j₁).val.2 d₀ = d₀
              erw [colimitADD.fac coconeAA ⟨0⟩,
                   limitAA.fac _ ⟨WalkingPair.left⟩]; rfl
            · change (p₁ ⊚ finv ⊚ j₂).val.2 () = d₀
              erw [colimitADD.fac coconeAA ⟨1⟩,
                   limitAA.fac _ ⟨WalkingPair.left⟩]; rfl
            · change (p₁ ⊚ finv ⊚ j₃).val.2 () = d₁
              erw [colimitADD.fac coconeAA ⟨2⟩,
                   limitAA.fac _ ⟨WalkingPair.left⟩]; rfl
            · change (p₁ ⊚ finv ⊚ j₁).val.2 d₁ = d₁
              erw [colimitADD.fac coconeAA ⟨0⟩,
                   limitAA.fac _ ⟨WalkingPair.left⟩]; rfl
        · -- Show that p₂ ⊚ finv ⊚ f = p₂ ⊚ 𝟙 AA
          apply IrreflexiveGraph.hom_ext
          · -- Case fA (morphisms for arrows)
            rfl
          · -- Case fD (morphisms for dots)
            funext x
            change (p₂ ⊚ finv).val.2 (f.val.2 x) = p₂.val.2 x
            dsimp [f]
            generalize p₁.val.2 x = x₁, p₂.val.2 x = x₂
            change Fin 2 at x₁ x₂
            fin_cases x₁ <;> fin_cases x₂
            · change (p₂ ⊚ finv ⊚ j₁).val.2 d₀ = d₀
              erw [colimitADD.fac coconeAA ⟨0⟩,
                   limitAA.fac _ ⟨WalkingPair.right⟩]; rfl
            · change (p₂ ⊚ finv ⊚ j₂).val.2 () = d₁
              erw [colimitADD.fac coconeAA ⟨1⟩,
                   limitAA.fac _ ⟨WalkingPair.right⟩]; rfl
            · change (p₂ ⊚ finv ⊚ j₃).val.2 () = d₀
              erw [colimitADD.fac coconeAA ⟨2⟩,
                   limitAA.fac _ ⟨WalkingPair.right⟩]; rfl
            · change (p₂ ⊚ finv ⊚ j₁).val.2 d₁ = d₁
              erw [colimitADD.fac coconeAA ⟨0⟩,
                   limitAA.fac _ ⟨WalkingPair.right⟩]; rfl
      inv_hom_id := by
        apply colimitADD.hom_ext
        rintro ⟨j⟩
        fin_cases j
        · -- Show that f ⊚ finv ⊚ j₁ = 𝟙 ADD ⊚ j₁
          apply IrreflexiveGraph.hom_ext
          · -- Case fA (morphisms for arrows)
            rfl
          · -- Case fD (morphisms for dots)
            funext x
            change f.val.2 ((finv ⊚ j₁).val.2 x) = j₁.val.2 x
            dsimp [f]
            change Fin 2 at x
            have h₁ : (p₁ ⊚ finv ⊚ j₁).val.2 x = x := by
              erw [colimitADD.fac coconeAA ⟨0⟩,
                   limitAA.fac _ ⟨WalkingPair.left⟩]; rfl
            have h₂ : (p₂ ⊚ finv ⊚ j₁).val.2 x = x := by
              erw [colimitADD.fac coconeAA ⟨0⟩,
                   limitAA.fac _ ⟨WalkingPair.right⟩]; rfl
            erw [h₁, h₂]
            fin_cases x <;> rfl
        · -- Show that f ⊚ finv ⊚ j₂ = 𝟙 ADD ⊚ j₂
          apply IrreflexiveGraph.hom_ext
          · -- Case fA (morphisms for arrows)
            exact funext fun e ↦ Empty.elim e
          · -- Case fD (morphisms for dots)
            funext x
            change f.val.2 ((finv ⊚ j₂).val.2 x) = j₂.val.2 x
            dsimp [f]
            have h₁ : (p₁ ⊚ finv ⊚ j₂).val.2 x = d₀ := by
              erw [colimitADD.fac coconeAA ⟨1⟩,
                   limitAA.fac _ ⟨WalkingPair.left⟩]; rfl
            have h₂ : (p₂ ⊚ finv ⊚ j₂).val.2 x = d₁ := by
              erw [colimitADD.fac coconeAA ⟨1⟩,
                   limitAA.fac _ ⟨WalkingPair.right⟩]; rfl
            erw [h₁, h₂]; rfl
        · -- Show that f ⊚ finv ⊚ j₃ = 𝟙 ADD ⊚ j₃
          apply IrreflexiveGraph.hom_ext
          · -- Case fA (morphisms for arrows)
            exact funext fun e ↦ Empty.elim e
          · -- Case fD (morphisms for dots)
            funext x
            change f.val.2 ((finv ⊚ j₃).val.2 x) = j₃.val.2 x
            dsimp [f]
            have h₁ : (p₁ ⊚ finv ⊚ j₃).val.2 x = d₁ := by
              erw [colimitADD.fac coconeAA ⟨2⟩,
                   limitAA.fac _ ⟨WalkingPair.left⟩]; rfl
            have h₂ : (p₂ ⊚ finv ⊚ j₃).val.2 x = d₀ := by
              erw [colimitADD.fac coconeAA ⟨2⟩,
                   limitAA.fac _ ⟨WalkingPair.right⟩]; rfl
            erw [h₁, h₂]; rfl
    }
```
:::

```savedLean -show
end CM
```

import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article3
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory


#doc (Manual) "Session 12: Categories of diagrams" =>

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

# 1. Dynamical systems or automata

:::question (questionTitle := "Exercise 1") (questionPage := "161")
Suppose that $`{x' = \alpha^3(x)}` and that $`{X^{↻\alpha} \xrightarrow{f} Y^{↻\beta}}` is a map in 𝑺↻. Let $`{y = f(x)}` and $`{y' = \beta^3(y)}`. Prove that $`{f(x') = y'}`.
:::

:::solution (solutionTo := "Exercise 1")
```savedComment
Exercise 12.1 (p. 161)
```

We proceed by repeatedly applying the property $`{f \circ \alpha = \beta \circ f}`.

```savedLean
example {Xα Yβ : SetWithEndomap} (f : Xα ⟶ Yβ)
    {x x' : Xα.carrier} {y y' : Yβ.carrier}
    (hx' : x' = (Xα.toEnd ⊚ Xα.toEnd ⊚ Xα.toEnd) x)
    (hy : y = f.val x)
    (hy' : y' = (Yβ.toEnd ⊚ Yβ.toEnd ⊚ Yβ.toEnd) y)
    : f.val x' = y' := by
  have hf_comm := f.property
  rw [hy', hy]
  rw [← types_comp_apply f.val (Yβ.toEnd ⊚ Yβ.toEnd ⊚ Yβ.toEnd)]
  rw [← Category.assoc, ← Category.assoc]
  rw [← hf_comm]
  rw [Category.assoc Xα.toEnd]
  rw [← hf_comm]
  rw [Category.assoc, Category.assoc]
  rw [← hf_comm]
  rw [← Category.assoc, ← Category.assoc]
  rw [types_comp_apply]
  rw [hx']
```
:::

:::question (questionTitle := "Exercise 2") (questionPage := "162")
'With age comes stability'. In a finite dynamical system, every state eventually settles into a cycle.

...

For two units of time, $`x` is living on the fringes, but after that he settles into an organized periodic behaviour, repeating the same routine every four units of time. What about $`y` and $`z`? Don’t take the title seriously; humans can change the system! This sort of thing applies to light bulbs, though. If a particular light bulb can only be lit four times before burning out, after which pressing the on—off button has no effect, draw the automaton modeling its behavior.
:::

:::solution (solutionTo := "Exercise 2")
```savedComment
Exercise 12.2 (p. 162)
```

```savedLean -show
namespace Ex12_2
```

The automaton modelling the behaviour of a light bulb that can only be lit four times before burning out may be represented as follows:

```savedLean
inductive BulbState
  | off₀ | on₁ | off₁ | on₂ | off₂ | on₃ | off₃ | on₄ | burntOut
  deriving Fintype, DecidableEq

open BulbState

def pressButton : BulbState ⟶ BulbState
  | off₀ => on₁ -- lit 1st time
  | on₁  => off₁
  | off₁ => on₂ -- lit 2nd time
  | on₂  => off₂
  | off₂ => on₃ -- lit 3rd time
  | on₃  => off₃
  | off₃ => on₄ -- lit 4th time
  | on₄  => burntOut
  | burntOut => burntOut
```

To verify correct operation, we begin by setting up a simulation of pressing the on-off button eight times, starting from `off₀`, and counting how many times the bulb lights up.

```savedLean
abbrev LitCount := Nat

def LitStates : List BulbState := [on₁, on₂, on₃, on₄]

def pressAndCount (this : BulbState) : StateM LitCount BulbState := do
  let next := pressButton this
  if next ∈ LitStates then
    modify (· + 1)
  return next

def EightPresses : List Unit := List.replicate 8 ()

def simulateEightPresses : StateM LitCount BulbState :=
  EightPresses.foldlM (fun s _ ↦ pressAndCount s) off₀
```

Run the simulation starting with a lit count of 0, and return the final bulb state and lit count.

```savedLean
def getResult : BulbState × LitCount := simulateEightPresses.run 0
```

Confirm that at the end of the run, the bulb has been lit four times and is now `burntOut`.

```savedLean
example : getResult = (burntOut, 4) := rfl
```

Lastly, confirm that once the bulb is `burntOut`, pressing the on—off button has no effect (i.e., `burntOut` is a fixed point).

```savedLean
example : Function.IsFixedPt pressButton burntOut := rfl
```

```savedLean -show
end Ex12_2
```
:::

# 2. Family trees

We implement the category 𝑺↻↻ in which an object is a set with a specified pair of endomaps, as described on p. 162.

```savedComment
The category 𝑺↻↻ in which an object is a set with a specified pair of endomaps (p. 162)
```

```savedLean
structure SetWithTwoEndomaps extends SetWithEndomap where
  toEnd2 : carrier ⟶ carrier

instance instCatSetWithTwoEndomaps : Category SetWithTwoEndomaps where
  Hom X Y := {
    f : X.carrier ⟶ Y.carrier //
        f ⊚ X.toEnd = Y.toEnd ⊚ f -- first endomap commutes
        ∧ f ⊚ X.toEnd2 = Y.toEnd2 ⊚ f -- second endomap commutes
  }
  id X := ⟨𝟙 X.carrier, ⟨rfl, rfl⟩⟩
  comp := by
    rintro _ _ _ ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨
      g ⊚ f,
      by
        obtain ⟨hf_comm, hf2_comm⟩ := hf
        obtain ⟨hg_comm, hg2_comm⟩ := hg
        constructor
        · rw [← Category.assoc, hf_comm, Category.assoc, hg_comm,
            ← Category.assoc]
        · rw [← Category.assoc, hf2_comm, Category.assoc, hg2_comm,
            ← Category.assoc]
    ⟩
```

:::question (questionTitle := "Exercise 3") (questionPage := "163")
```savedComment
Exercise 12.3 (p. 163)
```

```savedLean -show
namespace Ex12_3
```

\(a\) Suppose $`{\mathbf{P} = {}^{m↻}P^{↻f}}` is the set $`P` of all people together with the endomaps $`{m = \mathit{mother}}` and $`{f = \mathit{father}}`. Show that 'gender' is a map in the category 𝑺↻↻ from $`\mathbf{P}` to the object

```savedLean
inductive Gender
  | female | male

def m₁ : Gender ⟶ Gender := fun _ ↦ Gender.female

def f₁ : Gender ⟶ Gender := fun _ ↦ Gender.male

def G : SetWithTwoEndomaps := {
  carrier := Gender
  toEnd := m₁
  toEnd2 := f₁
}
```

\(b\) In a certain society, all the people have always been divided into two 'clans', the Wolf-clan and the Bear-clan. Marriages within a clan are forbidden, so that a Wolf may not marry a Wolf. A child's clan is the same as that of its mother. Show that the sorting of people into clans is actually a map in 𝑺↻↻ from $`\mathbf{P}` to the object

```savedLean
inductive Clan
  | wolf | bear

def m₂ : Clan ⟶ Clan := fun c ↦ c

def f₂ : Clan ⟶ Clan
  | Clan.wolf => Clan.bear
  | Clan.bear => Clan.wolf

def C : SetWithTwoEndomaps := {
  carrier := Clan
  toEnd := m₂
  toEnd2 := f₂
}
```

\(c\) Find appropriate 'father' and 'mother' maps to make $`{\mathbf{G} \times \mathbf{C}}` into an object in 𝑺↻↻ so that 'clan' and 'gender' can be combined into a single map $`{\mathbf{P} \rightarrow \mathbf{G} \times \mathbf{C}}`. (Later, when we have the precise definition of multiplication of objects in categories, you will see that $`{\mathbf{G} \times \mathbf{C}}` really _is_ the product of $`\mathbf{G}` and $`\mathbf{C}`.)
:::

:::solution (solutionTo := "Exercise 3")
\(a\) For $`\mathbf{P}` in 𝑺↻↻, we first define a `Person` type to use in place of the set $`P` of all people, and we identity each `Person` as being either a mother or a father.

```savedLean
inductive ParentType
  | isMother | isFather

structure Person₁ where
  parentType : ParentType
```

We next define the `mother` and `father` endomaps on `Person`, which ignore their input (as irrelevant) and simply return a `Person` of the appropriate `ParentType`.

```savedLean
def mother₁ : Person₁ ⟶ Person₁ := fun _ ↦ ⟨ParentType.isMother⟩

def father₁ : Person₁ ⟶ Person₁ := fun _ ↦ ⟨ParentType.isFather⟩
```

Now we can define the object $`\mathbf{P}`.

```savedLean
def P₁ : SetWithTwoEndomaps := {
  carrier := Person₁
  toEnd := mother₁
  toEnd2 := father₁
}
```

Lastly, we define the map `gender`, which sends each `Person` to their corresponding `Gender`.

```savedLean
def gender : P₁.carrier ⟶ G.carrier
  | ⟨ParentType.isMother⟩ => Gender.female
  | ⟨ParentType.isFather⟩ => Gender.male
```

Since we can form a valid morphism using our categorical framework, it follows that `gender` is a map in the category 𝑺↻↻ from $`\mathbf{P}` to $`\mathbf{G}`.

```savedLean
def gender' : P₁ ⟶ G := ⟨
  gender,
  by
    constructor <;> rfl
⟩
```

For good measure, we can also verify the two commutative properties explicitly.

```savedLean
example : gender ⊚ mother₁ = m₁ ⊚ gender := rfl

example : gender ⊚ father₁ = f₁ ⊚ gender := rfl
```

\(b\) The implementation of part (b) is similar to that of part (a), with an appropriate change to our `Person` structure to handle clan.

```savedLean
inductive ParentClan
  | isWolf | isBear

structure Person₂ where
  parentClan : ParentClan

def mother₂ : Person₂ ⟶ Person₂ := fun p ↦ ⟨p.parentClan⟩

def father₂ : Person₂ ⟶ Person₂
  | ⟨ParentClan.isWolf⟩ => ⟨ParentClan.isBear⟩
  | ⟨ParentClan.isBear⟩ => ⟨ParentClan.isWolf⟩

def P₂ : SetWithTwoEndomaps := {
  carrier := Person₂
  toEnd := mother₂
  toEnd2 := father₂
}

def clan : P₂.carrier ⟶ C.carrier
  | ⟨ParentClan.isWolf⟩ => Clan.wolf
  | ⟨ParentClan.isBear⟩ => Clan.bear

def clan' : P₂ ⟶ C := ⟨
  clan,
  by
    constructor
    all_goals
      funext p
      match p with
      | ⟨ParentClan.isWolf⟩ => rfl
      | ⟨ParentClan.isBear⟩ => rfl
⟩
```

\(c\) The implementation of part (c) is a combination of parts (a) and (b).

```savedLean
structure Person₃ where
  parentType : ParentType
  parentClan : ParentClan

def mother₃ : Person₃ ⟶ Person₃ :=
  fun p ↦ ⟨ParentType.isMother, p.parentClan⟩

def father₃ : Person₃ ⟶ Person₃
  | ⟨_, ParentClan.isWolf⟩ => ⟨ParentType.isFather, ParentClan.isBear⟩
  | ⟨_, ParentClan.isBear⟩ => ⟨ParentType.isFather, ParentClan.isWolf⟩

def P₃ : SetWithTwoEndomaps := {
  carrier := Person₃
  toEnd := mother₃
  toEnd2 := father₃
}
```

As required, we define appropriate 'mother' and 'father' maps (`m` and `f`, respectively, to align with the book).

```savedLean
def m₃ : (Gender × Clan) ⟶ (Gender × Clan) :=
  fun (_, c) ↦ (Gender.female, c)

def f₃ : (Gender × Clan) ⟶ (Gender × Clan)
  | (_, Clan.wolf) => (Gender.male, Clan.bear)
  | (_, Clan.bear) => (Gender.male, Clan.wolf)

def GC : SetWithTwoEndomaps := {
  carrier := Gender × Clan
  toEnd := m₃
  toEnd2 := f₃
}

def gender_and_clan : P₃.carrier ⟶ GC.carrier
  | ⟨ParentType.isMother, ParentClan.isWolf⟩ =>
        ⟨Gender.female, Clan.wolf⟩
  | ⟨ParentType.isMother, ParentClan.isBear⟩ =>
        ⟨Gender.female, Clan.bear⟩
  | ⟨ParentType.isFather, ParentClan.isWolf⟩ =>
        ⟨Gender.male, Clan.wolf⟩
  | ⟨ParentType.isFather, ParentClan.isBear⟩ =>
        ⟨Gender.male, Clan.bear⟩

def gender_and_clan' : P₃ ⟶ GC := ⟨
  gender_and_clan,
  by
    constructor
    all_goals
      funext p
      match p with
      | ⟨ParentType.isMother, ParentClan.isWolf⟩ => rfl
      | ⟨ParentType.isMother, ParentClan.isBear⟩ => rfl
      | ⟨ParentType.isFather, ParentClan.isWolf⟩ => rfl
      | ⟨ParentType.isFather, ParentClan.isBear⟩ => rfl
⟩
```

```savedLean -show
end Ex12_3
```
:::

```savedLean -show
end CM
```

import VersoManual
import ConceptualMathematics.Meta.Lean
import ConceptualMathematics.Article3
import ConceptualMathematics.Session12
import Mathlib

open Verso.Genre Manual InlineLean
open ConceptualMathematics
open CategoryTheory
open Limits


#doc (Manual) "Session 21: Products in categories" =>

%%%
htmlSplit := .never
number := false
%%%

```savedImport
import ConceptualMathematics.Article3
import ConceptualMathematics.Session12
import Mathlib
open CategoryTheory
open Limits
```

```savedLean -show
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g
```

:::definition (definitionTerm := "Product") (definitionPage := "237")
Suppose that $`A` and $`B` are objects in a category 𝒞. A _product_ of $`A` and $`B` (in 𝒞) is

1. an object $`P` in 𝒞, and
2. a pair of maps, $`{P \xrightarrow{p_1} A}`, $`{P \xrightarrow{p_2} B}`, in 𝒞 satisfying:

for every object $`T` and every pair of maps $`{T \xrightarrow{q_1} A}`, $`{T \xrightarrow{q_2} B}`, there is exactly one map $`{T \xrightarrow{q} P}` for which $`{q_1 = p_1 \circ q}` and $`{q_2 = p_2 \circ q}`.
:::

See the earlier definition of _product_ on p. 217.

:::theoremDirective (theoremTitle := "Theorem") (theoremPage := "239")
Suppose that $`{A \xleftarrow{p_1} P \xrightarrow{p_2} B}` and $`{A \xleftarrow{q_1} Q \xrightarrow{q_2} B}`, are two products of $`A` and $`B`. Because $`{A \xleftarrow{p_1} P \xrightarrow{p_2} B}` is a product, viewing $`Q` as a 'test object' gives a map $`{Q \rightarrow P}`; because $`{A \xleftarrow{q_1} Q \xrightarrow{q_2} B}` is a product, we also get a map $`{P \rightarrow Q}`. These two maps are necessarily inverse to each other, and therefore the two objects $`P`, $`Q` are isomorphic.
:::

We provided a proof of this theorem in Exercise 12 of Article IV using the mathlib API for (binary) products. We repeat that proof here, but this time using only the book definition.

```savedComment
Theorem (p. 239)
```

```savedLean
theorem uniqueness_of_products'
    {𝒞 : Type u} [Category.{v, u} 𝒞] (A B P Q : 𝒞)
    (p₁ : P ⟶ A) (p₂ : P ⟶ B)
    (hP : ∀ (T : 𝒞) (t₁ : T ⟶ A) (t₂ : T ⟶ B),
        (∃! t : T ⟶ P, t₁ = p₁ ⊚ t ∧ t₂ = p₂ ⊚ t))
    (q₁ : Q ⟶ A) (q₂ : Q ⟶ B)
    (hQ : ∀ (T : 𝒞) (t₁ : T ⟶ A) (t₂ : T ⟶ B),
        (∃! t : T ⟶ Q, t₁ = q₁ ⊚ t ∧ t₂ = q₂ ⊚ t))
    : Nonempty (P ≅ Q) := by
  obtain ⟨f, hf_comm, _⟩ := hQ P p₁ p₂
  obtain ⟨g, hg_comm, _⟩ := hP Q q₁ q₂
  have hgf : g ⊚ f = 𝟙 P := by
    apply (hP P p₁ p₂).unique
    · constructor
      · symm
        calc p₁ ⊚ (g ⊚ f)
          _ = (p₁ ⊚ g) ⊚ f := by rw [Category.assoc]
          _ = q₁ ⊚ f        := by rw [← hg_comm.1]
          _ = p₁             := by rw [← hf_comm.1]
      · symm
        calc p₂ ⊚ (g ⊚ f)
          _ = (p₂ ⊚ g) ⊚ f := by rw [Category.assoc]
          _ = q₂ ⊚ f        := by rw [← hg_comm.2]
          _ = p₂             := by rw [← hf_comm.2]
    · constructor <;> rw [Category.id_comp]
  have hfg : f ⊚ g = 𝟙 Q := by
    apply (hQ Q q₁ q₂).unique
    · constructor
      · symm
        calc q₁ ⊚ (f ⊚ g)
          _ = (q₁ ⊚ f) ⊚ g := by rw [Category.assoc]
          _ = p₁ ⊚ g        := by rw [← hf_comm.1]
          _ = q₁             := by rw [← hg_comm.1]
      · symm
        calc q₂ ⊚ (f ⊚ g)
          _ = (q₂ ⊚ f) ⊚ g := by rw [Category.assoc]
          _ = p₂ ⊚ g        := by rw [← hf_comm.2]
          _ = q₂             := by rw [← hg_comm.2]
    · constructor <;> rw [Category.id_comp]
  apply Nonempty.intro
  exact {
    hom := f
    inv := g
    hom_inv_id := hgf
    inv_hom_id := hfg
  }
```

:::question (questionTitle := "Exercise 1") (questionPage := "241")
```savedComment
Exercise 21.1 (p. 241)
```

```savedLean -show
namespace Ex21_1
```

Is there a map in 𝑺↻ from the 'day clock'

```savedLean
abbrev dayClock : SetWithEndomap := {
  carrier := Fin 24
  toEnd := (· + 1)
}
```

to some $`X^{↻\alpha}` which together with the \['shift clock' and map\]

```savedLean
abbrev shiftClock : SetWithEndomap := {
  carrier := Fin 8
  toEnd := (· + 1)
}

def p₁ : dayClock ⟶ shiftClock := ⟨
  fun n ↦ Fin.ofNat 8 n,
  by
    funext x
    fin_cases x <;> decide
⟩
```

makes the 'day clock' into the product of $`X^{↻\alpha}` and the 'shift clock'?
:::

:::solution (solutionTo := "Exercise 1")
We can use a '3-hour clock' as the object $`X^{↻\alpha}`, with the required map $`{\mathrm{dayClock} \rightarrow X^{↻\alpha}}` given by $`{n \mapsto n \mod 3}`.

```savedLean
abbrev Xα : SetWithEndomap := {
  carrier := Fin 3
  toEnd := (· + 1)
}

def p₂ : dayClock ⟶ Xα := ⟨
  fun n ↦ Fin.ofNat 3 n,
  by
    funext x
    fin_cases x <;> decide
⟩
```

The proof is a direct application of the Chinese Remainder Theorem (CRT), and we begin by defining some helpers:

\[Isomorphism\] Construct `Fin 24` from `Fin 8` and `Fin 3` via CRT.
```savedLean
def crt (a : Fin 8) (b : Fin 3) : Fin 24 :=
  Fin.ofNat 24 (9 * a.val + 16 * b.val)
```

\[Homomorphism\] Show that `crt` preserves `(· + 1)` structure.
```savedLean
lemma h_crt_comm (a : Fin 8) (b : Fin 3) :
    crt (a + 1) (b + 1) = crt a b + 1 := by
  fin_cases a <;> fin_cases b <;> decide
```

\[Commutativity\] Show that `p₁ ∘ crt` and `p₂ ∘ crt` recover components.
```savedLean
lemma h_p₁_crt (a : Fin 8) (b : Fin 3) : p₁.val (crt a b) = a := by
  fin_cases a <;> fin_cases b <;> decide

lemma h_p₂_crt (a : Fin 8) (b : Fin 3) : p₂.val (crt a b) = b := by
  fin_cases a <;> fin_cases b <;> decide
```

\[Uniqueness\] Show that any `Fin 24` decomposes into projections.
```savedLean
lemma h_crt_uniq (x : dayClock.carrier) :
    crt (p₁.val x) (p₂.val x) = x := by
  fin_cases x <;> decide
```

We are now ready to prove that the 'day clock' with the given projections is the product of the 'shift clock' and our '3-hour clock' $`X^{↻\alpha}`.

```savedLean
example : IsLimit (BinaryFan.mk p₁ p₂) := {
  -- Construct morphism f from cone point s.pt to product
  lift s := ⟨
    fun x ↦ crt ((BinaryFan.fst s).val x)
                 ((BinaryFan.snd s).val x),
    by
      funext x
      have hf₁_comm := congr_fun (BinaryFan.fst s).property x
      have hf₂_comm := congr_fun (BinaryFan.snd s).property x
      dsimp at *
      rw [hf₁_comm, hf₂_comm, h_crt_comm]
  ⟩
  -- Verify triangle diagrams commute for both legs of cone s
  fac s j := by
    rcases j with ⟨_ | _⟩
    all_goals
      apply Subtype.ext
      funext x
      first | apply h_p₁_crt | apply h_p₂_crt
  -- Show morphism f is unique by decomposing it into projections
  uniq s f hf := by
    apply Subtype.ext
    funext x
    dsimp [BinaryFan.fst, BinaryFan.snd]
    rw [← h_crt_uniq (f.val x),
        ← hf ⟨WalkingPair.left⟩, ← hf ⟨WalkingPair.right⟩]
    rfl
}
```

```savedLean -show
end Ex21_1
```
:::

:::question (questionTitle := "Exercise 2") (questionPage := "244")
What is the product $`{C_m \times C_n}` of an $`m`-cycle and an $`n`-cycle? For example, what is the product $`{C_{12} \times C_{8}}`? Hint: Start by investigating products of cycles of smaller sizes.
:::

:::solution (solutionTo := "Exercise 2")
```savedComment
Exercise 21.2 (p. 244)
```

{htmlSpan (class := "todo")}[TODO Exercise 21.2]
:::

:::question (questionTitle := "Exercise 3") (questionPage := "244")
Return to Exercise 3 of Session 12. Show that the object which was called $`{\mathbf{G} \times \mathbf{C}}`, when provided with appropriate projection maps, really is the product in the category 𝑺↻↻.
:::

:::solution (solutionTo := "Exercise 3")
```savedComment
Exercise 21.3 (p. 244)
```

See Exercise 3 of Session 12 for the relevant definitions.

```savedLean -show
namespace Ex12_3
```

We begin by defining appropriate projection maps.

```savedLean
def p₁ : GC ⟶ G := ⟨
  fun (g, _) ↦ g,
  by
    constructor
    · funext x
      rfl
    · funext (x₁, x₂)
      cases x₁ <;> cases x₂ <;> rfl
⟩

def p₂ : GC ⟶ C := ⟨
  fun (_, c) ↦ c,
  by
    constructor
    · funext x
      rfl
    · funext (x₁, x₂)
      cases x₁ <;> cases x₂ <;> rfl
⟩
```

We use mathlib's API for binary products in the proof that follows.

```savedLean
example : IsLimit (BinaryFan.mk p₁ p₂) := {
  lift s := ⟨
    fun x ↦ ((BinaryFan.fst s).val x, (BinaryFan.snd s).val x),
    by
      obtain ⟨h_fst_m, h_fst_f⟩ := (BinaryFan.fst s).property
      obtain ⟨h_snd_m, h_snd_f⟩ := (BinaryFan.snd s).property
      dsimp at *
      constructor
      · funext x
        apply Prod.ext
        · change ((BinaryFan.fst s).val ⊚ s.pt.toEnd) x = _
          erw [congr_fun h_fst_m x]; rfl
        · change ((BinaryFan.snd s).val ⊚ s.pt.toEnd) x = _
          erw [congr_fun h_snd_m x]; rfl
      · funext x
        apply Prod.ext
        · change ((BinaryFan.fst s).val ⊚ s.pt.toEnd2) x = _
          erw [congr_fun h_fst_f x]
          dsimp
          generalize (BinaryFan.snd s).val x = c
          cases c <;> rfl
        · change ((BinaryFan.snd s).val ⊚ s.pt.toEnd2) x = _
          erw [congr_fun h_snd_f x]
          dsimp
          generalize (BinaryFan.snd s).val x = c
          cases c <;> rfl
  ⟩
  fac s j := by
    apply Subtype.ext
    funext x
    rcases j with ⟨_, _⟩ <;> rfl
  uniq s m hm := by
    apply Subtype.ext
    funext x
    apply Prod.ext
    · exact congr_arg (fun f ↦ f.val x) (hm ⟨WalkingPair.left⟩)
    · exact congr_arg (fun f ↦ f.val x) (hm ⟨WalkingPair.right⟩)
}
```

```savedLean -show
end Ex12_3
```
:::

```savedLean -show
end CM
```

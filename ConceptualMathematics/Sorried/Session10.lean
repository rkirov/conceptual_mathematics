import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import ConceptualMathematics.Sorried.Article2
open CategoryTheory
open Limits
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

variable {𝒞 : Type u} [Category.{v, u} 𝒞]

/-!
Exercise 10.1 (p. 126)
requires building concrete topological spaces, cannot be done purely categorically.
-/
/-!
Exercise 10.2 (p. 126)
-/
-- to be read as "A is a retract of B"
def IsRetract (A B : 𝒞) : Prop :=
  ∃ (r : B ⟶ A) (s : A ⟶ B), r ⊚ s = 𝟙 A

def FixedMapProp (X T : 𝒞) : Prop := ∀ (f : X ⟶ X), ∃ x : T ⟶ X, f ⊚ x = x

example (A X T : 𝒞) (h : IsRetract A X) (hF : FixedMapProp X T) : FixedMapProp A T := by
  intro f
  obtain ⟨r, s, hrs⟩ := h
  specialize hF (s ⊚ f ⊚ r)
  obtain ⟨x, hx⟩ := hF
  use r ⊚ x
  have := congr_arg (r ⊚ ·) hx
  simp only [Category.assoc] at this
  rw [hrs] at this
  simp only [Category.comp_id] at this
  rw [Category.assoc]
  exact this

/-!
Exercise 10.3 (p. 126)
requires concrete topological spaces.
-/


/-! ## Objectifying Brouwer's argument (pp. 127–129)

We work in a category equipped with the "arrow object" `A`, the sphere `S`, the
ball `B`, and three maps `j`, `h`, `p` satisfying Axioms 1 and 2. `variable` fixes
one arbitrary such configuration, so every theorem below is proved "in any category
in which these axioms hold" (p. 127). The point `1` is the terminal object `⊤_ 𝒞`.
`IsRetractionFor` is reused from Article 2. -/

section Brouwer

variable {A B S : 𝒞}
variable (j : S ⟶ B) (h : A ⟶ B) (p : A ⟶ S)

/-! Axiom 1 (p. 128) -/
variable (ax1 : ∀ (T : 𝒞) (a : T ⟶ A) (s : T ⟶ S), h ⊚ a = j ⊚ s → p ⊚ a = s)

include ax1 in
/-- Theorem 1 (p. 128) -/
theorem theorem1 (a : B ⟶ A) (ha : h ⊚ a ⊚ j = j) :
    IsRetractionFor j (p ⊚ a) := by
  specialize ax1 S (a ⊚ j) (𝟙 S)
  rw [IsRetractionFor]
  rw [← Category.assoc]
  apply ax1
  rw [Category.id_comp]
  exact ha

include ax1 in
/-- Corollary 1 (p. 128) -/
theorem corollary1 (a : B ⟶ A) (ha : h ⊚ a = 𝟙 B) :
    IsRetractionFor j (p ⊚ a) := by
  have : h ⊚ a ⊚ j = j := by rw [Category.assoc, ha, Category.comp_id]
  exact theorem1 j h p ax1 a this

-- we need a category with an unit, in mathlib this is `HasTerminal 𝒞`
variable [HasTerminal 𝒞]
noncomputable
abbrev Unit (𝒞 : Type u) [Category.{v, u} 𝒞] [HasTerminal 𝒞] := (⊤_ 𝒞)

/-! Axiom 2 (p. 129): -/
variable (ax2 : ∀ (T : 𝒞) (f g : T ⟶ B),
  (∃ t : Unit 𝒞 ⟶ T, f ⊚ t = g ⊚ t) ∨ (∃ a : T ⟶ A, h ⊚ a = g))

/-!
Theorem 2 (p. 129)
-/
include ax1 ax2 p in
theorem theorem2 (f g : B ⟶ B) (hg : g ⊚ j = j) :
    (∃ b : Unit 𝒞 ⟶ B, f ⊚ b = g ⊚ b) ∨ HasRetraction j := by
  rcases ax2 B f g with hb | ⟨a, ha⟩
  · exact Or.inl hb
  · right
    use p ⊚ a
    have hfac : h ⊚ a ⊚ j = j := by rw [Category.assoc, ha, hg]
    exact theorem1 j h p ax1 a hfac

/-!
Corollary 2 (p. 129)
-/
include ax1 ax2 p in
example (f : B ⟶ B) : (∃ b : Unit 𝒞 ⟶ B, f ⊚ b = b) ∨ HasRetraction j := by
  have := theorem2 j h p ax1 ax2 f (𝟙 B) (by rw [Category.comp_id])
  simp only [Category.comp_id] at this
  exact this

end Brouwer

/-!
Exercise 10.4 (p. 132) Hard to do formally.
-/
end CM

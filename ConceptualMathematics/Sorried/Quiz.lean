import ConceptualMathematics.Sorried.Article2
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Data.Real.Basic
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

variable {𝒞 : Type u} [Category.{v, u} 𝒞] {C D : 𝒞}

/-!
Problem Quiz.1 (p. 108)
-/

example : ∃ A B : Type, ∃ f : A → B,
  (∃ r : B ⟶ A, IsRetractionFor f r) ∧ (¬ ∃ s : B ⟶ A, IsSectionFor f s) := by
  use Fin 1, Fin 2
  use fun _ => ⟨0, by simp⟩
  constructor
  · use fun _ => ⟨0, by simp⟩
    funext x
    fin_cases x
    simp
  · intro h
    obtain ⟨s, hs⟩ := h
    rw [IsSectionFor] at hs
    have h1 := congr_fun hs ⟨0, by simp⟩
    have h2 := congr_fun hs ⟨1, by simp⟩
    simp at h1 h2

/-!
Problem Quiz.2 (p. 108)
-/
-- a)
example (p : C ⟶ D) (q : D ⟶ C) (hpq : p ⊚ q ⊚ p = p) : IsIdempotent (p ⊚ q) := by
  constructor
  repeat rw [Category.assoc] at hpq ⊢
  rw [hpq]

-- b)
example (p : C ⟶ D) (q : D ⟶ C) (hpq : p ⊚ q ⊚ p = p) : IsIdempotent (q ⊚ p) := by
  constructor
  repeat rw [← Category.assoc]
  rw [hpq]

/-!
Problem Quiz_2* (p. 108)
-/
example (p : C ⟶ D) (q : D ⟶ C) (hpq : p ⊚ q ⊚ p = p) :
    ∃ q', p ⊚ q' ⊚ p = p ∧ q' ⊚ p ⊚ q' = q' := by
  use q ⊚ p ⊚ q
  constructor
  · simp only [Category.assoc, hpq]
    rw [← Category.assoc]
    exact hpq
  · simp only [Category.assoc, hpq]
    rw [show (((q ⊚ p) ⊚ q) ⊚ p) ⊚ q = (q ⊚ (p ⊚ q ⊚ p)) ⊚ q by simp only [Category.assoc]]
    rw [hpq]

/-!
Problem Quiz_1* (p. 108)
-/
example : ∃ A B : Type, Infinite A ∧ Infinite B ∧ ∃ f : A → B,
  (∃ r : B ⟶ A, IsRetractionFor f r) ∧ (¬ ∃ s : B ⟶ A, IsSectionFor f s) := by
  use ℕ, ℝ
  constructor
  · infer_instance
  · constructor
    · exact Infinite.of_injective (Nat.cast : ℕ → ℝ) Nat.cast_injective
    · use fun x => (x:ℝ)
      constructor
      · use fun x => ⌊x⌋₊
        funext x
        simp
      · intro h
        -- A section s : ℝ → ℕ would satisfy ↑(s r) = r for every real r.
        -- But no natural number casts to 1/2, so applying it at 1/2 is absurd.
        obtain ⟨s, hs⟩ := h
        have key := congr_fun hs (1/2 : ℝ)
        have h2 : (s (1/2 : ℝ) : ℝ) = 1/2 := key
        have h3 : (2 * s (1/2 : ℝ) : ℕ) = 1 := by
          exact_mod_cast (by linarith : (2 * s (1/2 : ℝ) : ℝ) = 1)
        omega
end CM

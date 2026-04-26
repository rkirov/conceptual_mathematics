import ConceptualMathematics.Article2
import Mathlib
open CategoryTheory
set_option linter.unusedFintypeInType false
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

namespace AnyCategory

variable {𝒞 : Type u} [Category.{v, u} 𝒞] {A X : 𝒞}
         {j : A ⟶ X} {p : X ⟶ A}

/-!
idempotent
-/
example (hpj : p ⊚ j = 𝟙 A) : (j ⊚ p) ⊚ (j ⊚ p) = (j ⊚ p) := by
  set α := j ⊚ p
  show α ⊚ α = α
  rw [Category.assoc, ← Category.assoc j, hpj, Category.id_comp]

end AnyCategory

namespace CM_Fintype

variable {A X : Type u} [Fintype A] [Fintype X] {j : A ⟶ X} {p : X ⟶ A}

/-!
Function.Surjective
-/
example (hpj : p ⊚ j = 𝟙 A) : ∀ a : A, ∃ x : X, p x = a := by
  intro a
  use j a
  rw [← types_comp_apply j p, hpj]
  rfl

example (hpj : p ⊚ j = 𝟙 A) : Function.Surjective p := by
  intro a
  use j a
  rw [← types_comp_apply j p, hpj]
  rfl

/-!
epi_iff_surjective
-/
example {X Y : Type u} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f :=
  epi_iff_surjective f

/-!
Function.Injective
-/
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

/-!
mono_iff_injective
-/
example {X Y : Type u} (f : X ⟶ Y) : Mono f ↔ Function.Injective f :=
  mono_iff_injective f

/-!
Cardinal.mk_le_of_surjective, Cardinal.mk_le_of_injective
-/
example {α β : Type u} {f : α → β} (hf_surj : Function.Surjective f)
    : Cardinal.mk β ≤ Cardinal.mk α :=
  Cardinal.mk_le_of_surjective hf_surj

open Cardinal in
example (hpj : p ⊚ j = 𝟙 A) : #A ≤ #X := by
  have hp₁ : Section p := { section_ := j }
  have hp₂ : Epi p := hp₁.epi
  have hp₃ : Function.Surjective p := (epi_iff_surjective p).mp hp₂
  exact mk_le_of_surjective hp₃

open Cardinal in
example (hpj : p ⊚ j = 𝟙 A) : #A ≤ #X := by
  have hj₁ : Retraction j := { retraction := p }
  have hj₂ : Mono j := hj₁.mono
  have hj₃ : Function.Injective j := (mono_iff_injective j).mp hj₂
  exact mk_le_of_injective hj₃

/-!
h_cardinal_zero_eq_zero_iff
-/
open Cardinal in
theorem h_cardinal_zero_eq_zero_iff {α : Type u} [Fintype α]
    : #α = 0 ↔ IsEmpty α := by
  rw [mk_fintype]
  norm_cast
  exact Fintype.card_eq_zero_iff

open Cardinal in
example (_ : p ⊚ j = 𝟙 A) : #A = 0 → #X = 0 := by
  repeat rw [h_cardinal_zero_eq_zero_iff]
  intro hA
  apply IsEmpty.mk
  intro x
  exact hA.false (p x)

end CM_Fintype

end CM

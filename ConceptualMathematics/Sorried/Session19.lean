import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Combinatorics.Quiver.ReflQuiver
open CategoryTheory
open Limits
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Theorem (p. 229)
-/
theorem uniqueness_of_terminal_objects'
    {𝒞 : Type u} [Category.{v, u} 𝒞] {T₁ T₂ : 𝒞}
    (hT₁ : ∀ X : 𝒞, (∃ f : X ⟶ T₁, (∀ f' : X ⟶ T₁, f = f')))
    (hT₂ : ∀ X : 𝒞, (∃ f : X ⟶ T₂, (∀ f' : X ⟶ T₂, f = f')))
    : Nonempty (T₁ ≅ T₂) := by
  let f : T₁ ⟶ T₂ := hT₂ T₁ |> Classical.choose
  let g : T₂ ⟶ T₁ := hT₁ T₂ |> Classical.choose
  have hgf : g ⊚ f = 𝟙 T₁ := by
    obtain ⟨t₁, ht₁⟩ := hT₁ T₁
    rw [← ht₁ (g ⊚ f), ← ht₁ (𝟙 T₁)]
  have hfg : f ⊚ g = 𝟙 T₂ := by
    obtain ⟨t₂, ht₂⟩ := hT₂ T₂
    rw [← ht₂ (f ⊚ g), ← ht₂ (𝟙 T₂)]
  apply Nonempty.intro
  exact {
    hom := f
    inv := g
    hom_inv_id := hgf
    inv_hom_id := hfg
  }

end CM

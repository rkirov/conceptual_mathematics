import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Combinatorics.Quiver.ReflQuiver
open CategoryTheory
open Limits
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Diagonal Theorem (pp. 304–305)
-/
theorem diagonal_theorem {𝒞 : Type u} [Category.{v, u} 𝒞] {T Y : 𝒞}
    [HasBinaryProduct T T] [HasTerminal 𝒞]
    (h : ∃ f : T ⨯ T ⟶ Y, ∀ e : T ⟶ Y, ∃ x : ⊤_ 𝒞 ⟶ T,
        e = f ⊚ prod.lift (𝟙 T) (x ⊚ terminal.from T)) :
    ∀ α : Y ⟶ Y, ∃ y : ⊤_ 𝒞 ⟶ Y, α ⊚ y = y := by
  obtain ⟨f, h'⟩ := h
  intro α
  let g : T ⟶ Y := α ⊚ f ⊚ prod.lift (𝟙 T) (𝟙 T)
  obtain ⟨t₀, hg⟩ := h' g
  have hgt₀ : g ⊚ t₀ = f ⊚ prod.lift t₀ t₀ := by
    have : prod.lift (𝟙 T) (t₀ ⊚ terminal.from T) ⊚ t₀ =
        prod.lift t₀ t₀ := by
      apply prod.hom_ext
      · rw [prod.lift_fst, Category.assoc,
            prod.lift_fst, Category.comp_id]
      · rw [prod.lift_snd, Category.assoc,
            prod.lift_snd, ← Category.assoc]
        nth_rw 3 [← Category.id_comp t₀]
        rw [terminal.hom_ext (terminal.from T ⊚ t₀) (𝟙 (⊤_ 𝒞))]
    rw [hg, ← Category.assoc, this]
  have hα : α ⊚ f ⊚ prod.lift t₀ t₀ = f ⊚ prod.lift t₀ t₀ := by
    have : prod.lift (𝟙 T) (𝟙 T) ⊚ t₀ = prod.lift t₀ t₀ := by
      apply prod.hom_ext
      · rw [prod.lift_fst, Category.assoc,
            prod.lift_fst, Category.comp_id]
      · rw [prod.lift_snd, Category.assoc,
            prod.lift_snd, Category.comp_id]
    nth_rw 2 [← hgt₀]
    dsimp [g]
    rw [← Category.assoc, ← Category.assoc, this]
  set y₀ : ⊤_ 𝒞 ⟶ Y := f ⊚ prod.lift t₀ t₀
  use y₀

/-!
Cantor's Contrapositive Corollary (p. 305)
-/
theorem cantor's_contrapositive_corollary
    {𝒞 : Type u} [Category.{v, u} 𝒞] {T Y : 𝒞}
    [HasBinaryProduct T T] [HasTerminal 𝒞]
    (h : ∃ α : Y ⟶ Y, ∀ y : ⊤_ 𝒞 ⟶ Y, α ⊚ y ≠ y) :
    ∀ f : T ⨯ T ⟶ Y, ∃ g : T ⟶ Y, ∀ x : ⊤_ 𝒞 ⟶ T,
        g ≠ f ⊚ prod.lift (𝟙 T) (x ⊚ terminal.from T) := by
  obtain ⟨α, h'⟩ := h
  intro f
  let g : T ⟶ Y := α ⊚ f ⊚ prod.lift (𝟙 T) (𝟙 T)
  use g
  intro x hg
  have hgx : g ⊚ x = f ⊚ prod.lift x x := by
    have : prod.lift (𝟙 T) (x ⊚ terminal.from T) ⊚ x =
        prod.lift x x := by
      apply prod.hom_ext
      · rw [prod.lift_fst, Category.assoc,
            prod.lift_fst, Category.comp_id]
      · rw [prod.lift_snd, Category.assoc,
            prod.lift_snd, ← Category.assoc]
        nth_rw 3 [← Category.id_comp x]
        rw [terminal.hom_ext (terminal.from T ⊚ x) (𝟙 (⊤_ 𝒞))]
    rw [hg, ← Category.assoc, this]
  have hα : α ⊚ f ⊚ prod.lift x x = f ⊚ prod.lift x x := by
    have : prod.lift (𝟙 T) (𝟙 T) ⊚ x = prod.lift x x := by
      apply prod.hom_ext
      · rw [prod.lift_fst, Category.assoc,
            prod.lift_fst, Category.comp_id]
      · rw [prod.lift_snd, Category.assoc,
            prod.lift_snd, Category.comp_id]
    nth_rw 2 [← hgx]
    dsimp [g]
    rw [← Category.assoc, ← Category.assoc, this]
  set y₀ : ⊤_ 𝒞 ⟶ Y := f ⊚ prod.lift x x
  apply h' y₀
  exact hα

/-!
Exercise 29.1 (p. 306)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] {T Y : 𝒞}
    [HasBinaryProduct T T] [HasTerminal 𝒞]
    (h : ∃ f : T ⨯ T ⟶ Y, ∀ e : T ⟶ Y, ∃ x : ⊤_ 𝒞 ⟶ T,
        ∀ t : ⊤_ 𝒞 ⟶ T,
        e ⊚ t = f ⊚ prod.lift (𝟙 T) (x ⊚ terminal.from T) ⊚ t) :
    ∀ α : Y ⟶ Y, ∃ y : ⊤_ 𝒞 ⟶ Y, α ⊚ y = y :=
  sorry

end CM

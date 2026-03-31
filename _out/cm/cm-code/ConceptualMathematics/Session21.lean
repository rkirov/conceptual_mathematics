import ConceptualMathematics.Article3
import ConceptualMathematics.Session12
import Mathlib
open CategoryTheory
open Limits
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Theorem (p. 239)
-/
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

/-!
Exercise 21.1 (p. 241)
-/
namespace Ex21_1

abbrev dayClock : SetWithEndomap := {
  carrier := Fin 24
  toEnd := (· + 1)
}

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

def crt (a : Fin 8) (b : Fin 3) : Fin 24 :=
  Fin.ofNat 24 (9 * a.val + 16 * b.val)

lemma h_crt_comm (a : Fin 8) (b : Fin 3) :
    crt (a + 1) (b + 1) = crt a b + 1 := by
  fin_cases a <;> fin_cases b <;> decide

lemma h_p₁_crt (a : Fin 8) (b : Fin 3) : p₁.val (crt a b) = a := by
  fin_cases a <;> fin_cases b <;> decide

lemma h_p₂_crt (a : Fin 8) (b : Fin 3) : p₂.val (crt a b) = b := by
  fin_cases a <;> fin_cases b <;> decide

lemma h_crt_uniq (x : dayClock.carrier) :
    crt (p₁.val x) (p₂.val x) = x := by
  fin_cases x <;> decide

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

end Ex21_1

/-!
Exercise 21.2 (p. 244)
-/
/-!
Exercise 21.3 (p. 244)
-/
namespace Ex12_3

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

end Ex12_3

end CM


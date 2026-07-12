import ConceptualMathematics.Sorried.Article3
import ConceptualMathematics.Sorried.Article4
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
open CategoryTheory
open Limits
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise 27.1 (p. 288)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] [HasTerminal 𝒞]
    (A B : 𝒞) (p₁ : ⊤_ 𝒞 ⟶ A) (p₂ : ⊤_ 𝒞 ⟶ B)
    (P : IsLimit (BinaryFan.mk p₁ p₂)) :
    Nonempty (A ≅ ⊤_ 𝒞) ∧ Nonempty (B ≅ ⊤_ 𝒞) :=
  sorry

/-!
Exercise 27.2 (p. 290)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞] (C : 𝒞)
    (h : ∀ X : 𝒞, Subsingleton (X ⟶ C)) :
    IsLimit (BinaryFan.mk (𝟙 C) (𝟙 C)) :=
  sorry

example {𝒞 : Type u} [Category.{v, u} 𝒞] [HasTerminal 𝒞] (C : 𝒞) :
    (∀ X : 𝒞, Subsingleton (X ⟶ C)) ↔ Mono (terminal.from C) :=
  sorry

/-!
Exercise 27.3 (p. 291)
-/
example (C : Type) :
    Subsingleton C → IsLimit (BinaryFan.mk (𝟙 C) (𝟙 C)) :=
  sorry

-- Empty
example : IsLimit (BinaryFan.mk (𝟙 emptySWE) (𝟙 emptySWE)) :=
  sorry

-- Single element with identity map (terminal object in 𝑺↻)
example : IsLimit (BinaryFan.mk (𝟙 termSWE) (𝟙 termSWE)) :=
  sorry

-- Empty graph
example : IsLimit (BinaryFan.mk (𝟙 emptyIG) (𝟙 emptyIG)) :=
  sorry

-- Naked dot
open IrreflexiveGraph in
example : IsLimit (BinaryFan.mk (𝟙 D) (𝟙 D)) :=
  sorry

-- Single dot with one looping arrow (terminal object in 𝑺⇊)
open IrreflexiveGraph in
example : IsLimit (BinaryFan.mk (𝟙 termIG) (𝟙 termIG)) :=
  sorry

/-!
Exercise 27.4 (p. 292)
-/
namespace Ex27_4

def tri : ℕ → ℕ
| 0 => 0
| n + 1 => tri n + n + 1

def g : ℕ × ℕ ⟶ ℕ := fun (x, y) ↦ tri (x + y) + y

example : IsIso g :=
  sorry

open Polynomial in
example (f : ℕ ⟶ ℕ × ℕ) [IsIso f] :
    ¬∃ P : ℤ[X], ∀ n : ℕ, P.eval (n : ℤ) = (f n).1 :=
  sorry

end Ex27_4

/-!
Exercise 27.5 (p. 293)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (X Y : 𝒞) (f g : X ⟶ Y) (E F : 𝒞)
    (p : E ⟶ X) (hp₁ : f ⊚ p = g ⊚ p)
    (hp₂ : ∀ (T : 𝒞) (x : T ⟶ X), f ⊚ x = g ⊚ x →
        ∃! e : T ⟶ E, x = p ⊚ e)
    (q : F ⟶ X) (hq₁ : f ⊚ q = g ⊚ q)
    (hq₂ : ∀ (T : 𝒞) (x : T ⟶ X), f ⊚ x = g ⊚ x →
        ∃! e : T ⟶ F, x = q ⊚ e) :
    ∃ e : F ≅ E, p ⊚ e.hom = q :=
  sorry

/-!
Exercise 27.6 (p. 293)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (X Y : 𝒞) (f g : X ⟶ Y) (E : 𝒞)
    (p : E ⟶ X) (hp₁ : f ⊚ p = g ⊚ p)
    (hp₂ : ∀ (T : 𝒞) (x : T ⟶ X), f ⊚ x = g ⊚ x →
        ∃! e : T ⟶ E, x = p ⊚ e) :
    Mono p :=
  sorry

example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (X Y : 𝒞) (f g : X ⟶ Y) [HasEqualizer f g] :
    Mono (equalizer.ι f g) :=
  sorry

/-!
Exercise 27.7 (p. 293)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (A B : 𝒞) (α : B ⟶ A) (β : A ⟶ B)
    (h_idB : 𝟙 B = β ⊚ α) (f : A ⟶ A) (hf : f = α ⊚ β) :
    f ⊚ α = 𝟙 A ⊚ α ∧
    ∀ (T : 𝒞) (x : T ⟶ A), f ⊚ x = 𝟙 A ⊚ x →
        ∃! e : T ⟶ B, x = α ⊚ e :=
  sorry

example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (A B : 𝒞) (α : B ⟶ A) (β : A ⟶ B)
    (h_idB : 𝟙 B = β ⊚ α) (f : A ⟶ A) (hf : f = α ⊚ β) :
    ∃ (w : f ⊚ α = 𝟙 A ⊚ α),
        Nonempty (IsLimit (Fork.ofι α w)) :=
  sorry

/-!
Exercise 27.8 (p. 293)
-/
example (G : IrreflexiveGraph) (E : Type) (p : E ⟶ G.A)
    (w : G.toSrc ⊚ p = G.toTgt ⊚ p)
    (t : IsLimit (Fork.ofι p w)) :
    ∀ a : G.A, (∃ x : E, p x = a) ↔
        G.toSrc a = G.toTgt a :=
  sorry

/-!
Exercise 27.9 (p. 293)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (X Y : 𝒞) [HasBinaryProduct X Y] :
    ∀ f : X ⟶ Y,
        ∃! Γ : SplitEpi prod.fst, f = prod.snd ⊚ Γ.section_ :=
  sorry

/-!
Exercise 27.10 (p. 294)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (X Y : 𝒞) (f g : X ⟶ Y) [HasBinaryProduct X Y]
    -- Equalizer of f, g
    (E₁ : 𝒞) (p : E₁ ⟶ X) (hp : f ⊚ p = g ⊚ p)
    (lift₁ : ∀ {T : 𝒞} (x : T ⟶ X), f ⊚ x = g ⊚ x → (T ⟶ E₁))
    (fac₁ : ∀ {T : 𝒞} (x : T ⟶ X) (h : f ⊚ x = g ⊚ x),
        p ⊚ lift₁ x h = x)
    (uniq₁ : ∀ {T : 𝒞} (x : T ⟶ X) (h : f ⊚ x = g ⊚ x)
        (m : T ⟶ E₁), p ⊚ m = x → m = lift₁ x h)
    -- Graphs of f and g
    (Γf Γg : SplitEpi prod.fst)
    (hΓf : f = prod.snd ⊚ Γf.section_)
    (hΓg : g = prod.snd ⊚ Γg.section_)
    -- Intersection in X × Y of graphs of f and g
    (E₂ : 𝒞) (u : E₂ ⟶ X) (v : E₂ ⟶ X)
    (h_intersect : Γf.section_ ⊚ u = Γg.section_ ⊚ v)
    (lift₂ : ∀ {T : 𝒞} (u' v' : T ⟶ X),
        Γf.section_ ⊚ u' = Γg.section_ ⊚ v' → (T ⟶ E₂))
    (fac_u₂ : ∀ {T : 𝒞} (u' v' : T ⟶ X)
        (h : Γf.section_ ⊚ u' = Γg.section_ ⊚ v'),
        u ⊚ lift₂ u' v' h = u')
    (_ : ∀ {T : 𝒞} (u' v' : T ⟶ X)
        (h : Γf.section_ ⊚ u' = Γg.section_ ⊚ v'),
        v ⊚ lift₂ u' v' h = v')
    (uniq₂ : ∀ {T : 𝒞} (u' v' : T ⟶ X)
        (h : Γf.section_ ⊚ u' = Γg.section_ ⊚ v') (m : T ⟶ E₂),
        u ⊚ m = u' → v ⊚ m = v' → m = lift₂ u' v' h) :
    E₁ ≅ E₂ :=
  sorry

noncomputable example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (X Y : 𝒞) (f g : X ⟶ Y) [HasBinaryProduct X Y]
    -- Equalizer of f, g
    [HasEqualizer f g]
    -- Graphs of f and g
    (Γf Γg : SplitEpi prod.fst)
    (hΓf : f = prod.snd ⊚ Γf.section_)
    (hΓg : g = prod.snd ⊚ Γg.section_)
    -- Intersection in X × Y of graphs of f and g
    [HasPullback Γf.section_ Γg.section_] :
    equalizer f g ≅ pullback Γf.section_ Γg.section_ :=
  sorry

/-!
graphOf (pp. 293–294)
-/
noncomputable def graphOf {𝒞 : Type u} [Category.{v, u} 𝒞]
    {X Y : 𝒞} [HasBinaryProduct X Y] (f : X ⟶ Y) : X ⟶ X ⨯ Y :=
  prod.lift (𝟙 X) f

lemma graphOf_is_section {𝒞 : Type u} [Category.{v, u} 𝒞]
    {X Y : 𝒞} [HasBinaryProduct X Y] (f : X ⟶ Y) :
    prod.fst ⊚ graphOf f = 𝟙 X :=
  prod.lift_fst (𝟙 X) f

lemma graphOf_commutes {𝒞 : Type u} [Category.{v, u} 𝒞]
    {X Y : 𝒞} [HasBinaryProduct X Y] (f : X ⟶ Y) :
    prod.snd ⊚ graphOf f = f :=
  prod.lift_snd (𝟙 X) f

/-!
cographOf (p. 294)
-/
noncomputable def cographOf {𝒞 : Type u} [Category.{v, u} 𝒞]
    {X Y : 𝒞} [HasBinaryCoproduct X Y] (g : Y ⟶ X) : X ⨿ Y ⟶ X :=
  coprod.desc (𝟙 X) g

lemma cographOf_is_retraction {𝒞 : Type u} [Category.{v, u} 𝒞]
    {X Y : 𝒞} [HasBinaryCoproduct X Y] (g : Y ⟶ X) :
    cographOf g ⊚ coprod.inl = 𝟙 X :=
  coprod.inl_desc (𝟙 X) g

lemma cographOf_commutes {𝒞 : Type u} [Category.{v, u} 𝒞]
    {X Y : 𝒞} [HasBinaryCoproduct X Y] (g : Y ⟶ X) :
    cographOf g ⊚ coprod.inr = g :=
  coprod.inr_desc (𝟙 X) g

/-!
Exercise 27.11 (p. 294)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (X Y : 𝒞) (f g : X ⟶ Y) (Z : 𝒞)
    (h : Y ⟶ Z) (hh₁ : h ⊚ f = h ⊚ g)
    (hh₂ : ∀ (Z' : 𝒞) (h' : Y ⟶ Z'), h' ⊚ f = h' ⊚ g →
        ∃! q : Z ⟶ Z', h' = q ⊚ h) :
    Epi h :=
  sorry

/-!
Exercise 27.12 (p. 294)
-/
example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (Y Z : 𝒞) (h : Y ⟶ Z)
    (Xh : 𝒞) (f g : Xh ⟶ Y) (_ : h ⊚ f = h ⊚ g)
    (h_univ : ∀ {X : 𝒞} (f' g' : X ⟶ Y), h ⊚ f' = h ⊚ g' →
        ∃! u : X ⟶ Xh, f ⊚ u = f' ∧ g ⊚ u = g') :
    ∃ r : Y ⟶ Xh, f ⊚ r = 𝟙 Y ∧ g ⊚ r = 𝟙 Y :=
  sorry

example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (Y Z : 𝒞) (h : Y ⟶ Z)
    (Xh : 𝒞) (f g : Xh ⟶ Y) (hh : h ⊚ f = h ⊚ g)
    (h_univ : ∀ {X : 𝒞} (f' g' : X ⟶ Y), h ⊚ f' = h ⊚ g' →
        ∃! u : X ⟶ Xh, f ⊚ u = f' ∧ g ⊚ u = g') :
    ∃ σ : Xh ⟶ Xh,
        σ ⊚ σ = 𝟙 Xh ∧ f ⊚ σ = g ∧ g ⊚ σ = f :=
  sorry

example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (Y Z : 𝒞) (h : Y ⟶ Z)
    (Xh : 𝒞) (f g : Xh ⟶ Y) (hh : h ⊚ f = h ⊚ g)
    (h_univ : ∀ {X : 𝒞} (f' g' : X ⟶ Y), h ⊚ f' = h ⊚ g' →
        ∃! u : X ⟶ Xh, f ⊚ u = f' ∧ g ⊚ u = g') :
    ∀ {T : 𝒞} (y₁ y₂ y₃ : T ⟶ Y) (v₁ v₂ : T ⟶ Xh),
        f ⊚ v₁ = y₁ → g ⊚ v₁ = y₂ → f ⊚ v₂ = y₂ → g ⊚ v₂ = y₃ →
        ∃ v₃ : T ⟶ Xh, f ⊚ v₃ = y₁ ∧ g ⊚ v₃ = y₃ :=
  sorry

example {𝒞 : Type u} [Category.{v, u} 𝒞]
    (Y Z : 𝒞) [HasBinaryProduct Y Y] (h : Y ⟶ Z)
    (Xh : 𝒞) (f g : Xh ⟶ Y) (hh : h ⊚ f = h ⊚ g)
    (h_univ : ∀ {X : 𝒞} (f' g' : X ⟶ Y), h ⊚ f' = h ⊚ g' →
        ∃! u : X ⟶ Xh, f ⊚ u = f' ∧ g ⊚ u = g') :
    ∀ {T : 𝒞} (a b : T ⟶ Xh),
        prod.lift f g ⊚ a = prod.lift f g ⊚ b → a = b :=
  sorry

end CM

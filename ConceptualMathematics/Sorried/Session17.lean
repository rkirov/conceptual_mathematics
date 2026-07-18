import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise 17.1 (p. 200)
-/
namespace Ex17_1_a

inductive Dot
  | x₁

inductive Arrow : Dot → Dot → Type
  | f₁ : Arrow .x₁ .x₁

instance : Quiver Dot where
  Hom := Arrow

open Limits in
example : ¬(HasTerminal (Paths Dot)) := by
  intro h
  -- The only object is x₁, so the terminal object must be x₁ — but x₁ ⟶ x₁ has two
  -- distinct maps: the identity `nil` and the self-loop `f₁`.
  suffices H : ∀ T : Paths Dot, IsTerminal T → False from H _ terminalIsTerminal
  intro T ht
  cases T
  case x₁ =>
    have := ht.hom_ext Quiver.Path.nil (Quiver.Hom.toPath Arrow.f₁)
    simp [Quiver.Hom.toPath] at this


end Ex17_1_a

namespace Ex17_1_b

inductive Dot
  | x₁

inductive Arrow : Dot → Dot → Type

instance : Quiver Dot where
  Hom := Arrow

open Limits in
example : HasTerminal (Paths Dot) := by
  -- Only object x₁, no arrows: the sole path x₁ ⟶ x₁ is `nil`, so x₁ is terminal.
  have hp : ∀ (p : Quiver.Path (Dot.x₁ : Paths Dot) Dot.x₁), p = Quiver.Path.nil :=
    fun p => by cases p with | nil => rfl | cons r e => nomatch e
  haveI : ∀ (Y : Paths Dot), Nonempty (Y ⟶ Dot.x₁) := by
    intro Y; cases Y; exact ⟨Quiver.Path.nil⟩
  haveI : ∀ (Y : Paths Dot), Subsingleton (Y ⟶ Dot.x₁) := by
    intro Y; cases Y; exact ⟨fun p q => (hp p).trans (hp q).symm⟩
  exact hasTerminal_of_unique Dot.x₁

end Ex17_1_b

namespace Ex17_1_c

inductive Dot
  | x₁ | x₂ | x₃ | x₄ | x₅

inductive Arrow : Dot → Dot → Type
  | f₁ : Arrow .x₁ .x₃
  | f₂ : Arrow .x₂ .x₃
  | f₃ : Arrow .x₃ .x₄
  | f₅ : Arrow .x₅ .x₄

instance : Quiver Dot where
  Hom := Arrow

open Limits in
example : HasTerminal (Paths Dot) := by
  -- Every vertex has a unique outgoing edge (or none), all leading into the sink x₄,
  -- so there is exactly one path from each object to x₄. Peeling the last edge of a
  -- path into x₄ leaves only one possibility at every step (impossible edges are
  -- discharged by `cases` on the empty hom-type).
  have hx1 : ∀ (p : Quiver.Path (Dot.x₁ : Paths Dot) Dot.x₄),
      p = (Quiver.Path.nil.cons Arrow.f₁).cons Arrow.f₃ := by
    intro p
    cases p with
    | cons p' e =>
      cases e with
      | f₃ =>
        cases p' with
        | cons p'' e2 =>
          cases e2 with
          | f₁ => cases p'' with
            | nil => rfl
            | cons _ e3 => cases e3
          | f₂ => cases p'' with | cons _ e3 => cases e3
      | f₅ => cases p' with | cons _ e2 => cases e2
  have hx2 : ∀ (p : Quiver.Path (Dot.x₂ : Paths Dot) Dot.x₄),
      p = (Quiver.Path.nil.cons Arrow.f₂).cons Arrow.f₃ := by
    intro p
    cases p with
    | cons p' e =>
      cases e with
      | f₃ =>
        cases p' with
        | cons p'' e2 =>
          cases e2 with
          | f₁ => cases p'' with | cons _ e3 => cases e3
          | f₂ => cases p'' with
            | nil => rfl
            | cons _ e3 => cases e3
      | f₅ => cases p' with | cons _ e2 => cases e2
  have hx3 : ∀ (p : Quiver.Path (Dot.x₃ : Paths Dot) Dot.x₄),
      p = Quiver.Path.nil.cons Arrow.f₃ := by
    intro p
    cases p with
    | cons p' e =>
      cases e with
      | f₃ =>
        cases p' with
        | nil => rfl
        | cons p'' e2 =>
          cases e2 with
          | f₁ => cases p'' with | cons _ e3 => cases e3
          | f₂ => cases p'' with | cons _ e3 => cases e3
      | f₅ => cases p' with | cons _ e2 => cases e2
  have hx4 : ∀ (p : Quiver.Path (Dot.x₄ : Paths Dot) Dot.x₄), p = Quiver.Path.nil := by
    intro p
    cases p with
    | nil => rfl
    | cons p' e =>
      cases e with
      | f₃ =>
        cases p' with
        | cons p'' e2 =>
          cases e2 with
          | f₁ => cases p'' with | cons _ e3 => cases e3
          | f₂ => cases p'' with | cons _ e3 => cases e3
      | f₅ => cases p' with | cons _ e2 => cases e2
  have hx5 : ∀ (p : Quiver.Path (Dot.x₅ : Paths Dot) Dot.x₄),
      p = Quiver.Path.nil.cons Arrow.f₅ := by
    intro p
    cases p with
    | cons p' e =>
      cases e with
      | f₃ =>
        cases p' with
        | cons p'' e2 =>
          cases e2 with
          | f₁ => cases p'' with | cons _ e3 => cases e3
          | f₂ => cases p'' with | cons _ e3 => cases e3
      | f₅ => cases p' with
        | nil => rfl
        | cons _ e2 => cases e2
  haveI : ∀ (Y : Paths Dot), Nonempty (Y ⟶ Dot.x₄) := by
    intro Y
    cases Y
    · exact ⟨(Quiver.Path.nil.cons Arrow.f₁).cons Arrow.f₃⟩
    · exact ⟨(Quiver.Path.nil.cons Arrow.f₂).cons Arrow.f₃⟩
    · exact ⟨Quiver.Path.nil.cons Arrow.f₃⟩
    · exact ⟨Quiver.Path.nil⟩
    · exact ⟨Quiver.Path.nil.cons Arrow.f₅⟩
  haveI : ∀ (Y : Paths Dot), Subsingleton (Y ⟶ Dot.x₄) := by
    intro Y
    cases Y
    · exact ⟨fun p q => (hx1 p).trans (hx1 q).symm⟩
    · exact ⟨fun p q => (hx2 p).trans (hx2 q).symm⟩
    · exact ⟨fun p q => (hx3 p).trans (hx3 q).symm⟩
    · exact ⟨fun p q => (hx4 p).trans (hx4 q).symm⟩
    · exact ⟨fun p q => (hx5 p).trans (hx5 q).symm⟩
  exact hasTerminal_of_unique Dot.x₄

end Ex17_1_c

namespace Ex17_1_d

inductive Dot
  | x₁ | x₂

inductive Arrow : Dot → Dot → Type
  | f₁ : Arrow .x₁ .x₂
  | f₂ : Arrow .x₂ .x₁

instance : Quiver Dot where
  Hom := Arrow

open Limits in
example : ¬(HasTerminal (Paths Dot)) := by
  intro h
  -- Whichever object is terminal has a nontrivial round-trip path distinct from `nil`.
  suffices H : ∀ T : Paths Dot, IsTerminal T → False from H _ terminalIsTerminal
  intro T ht
  cases T
  case x₁ =>
    have := ht.hom_ext Quiver.Path.nil
      ((Quiver.Hom.toPath Arrow.f₁).comp (Quiver.Hom.toPath Arrow.f₂))
    simp [Quiver.Hom.toPath] at this
  case x₂ =>
    have := ht.hom_ext Quiver.Path.nil
      ((Quiver.Hom.toPath Arrow.f₂).comp (Quiver.Hom.toPath Arrow.f₁))
    simp [Quiver.Hom.toPath] at this

end Ex17_1_d

namespace Ex17_1_e

inductive Dot
  | x₁ | x₂

inductive Arrow : Dot → Dot → Type
  | f₁ : Arrow .x₁ .x₂
  | f₂ : Arrow .x₁ .x₂

instance : Quiver Dot where
  Hom := Arrow

open Limits in
example : ¬(HasTerminal (Paths Dot)) := by
  intro h
  -- The terminal object is *some* Dot; rule out each candidate.
  suffices H : ∀ T : Paths Dot, IsTerminal T → False from H _ terminalIsTerminal
  intro T ht
  cases T
  case x₁ =>
    -- No arrow lands on x₁, so there is no path x₂ ⟶ x₁ — but terminality forces one.
    cases ht.from Dot.x₂ with | cons r e => nomatch e
  case x₂ =>
    -- Two distinct arrows x₁ ⟶ x₂ give two distinct maps into the terminal object.
    have := ht.hom_ext (Quiver.Hom.toPath Arrow.f₁) (Quiver.Hom.toPath Arrow.f₂)
    simp only [Quiver.Hom.toPath] at this
    injection this with _ _ _ hf
    exact absurd hf (by simp)

end Ex17_1_e

namespace Ex17_1_f

inductive Dot
  | x₁ | x₂ | x₃

inductive Arrow : Dot → Dot → Type
  | f₁ : Arrow .x₂ .x₁

instance : Quiver Dot where
  Hom := Arrow

open Limits in
example : ¬(HasTerminal (Paths Dot)) := by
  intro h
  -- The terminal object is *some* Dot; rule out each candidate.
  suffices H : ∀ T : Paths Dot, IsTerminal T → False from H _ terminalIsTerminal
  intro T ht
  cases T
  case x₁ =>
    -- x₃ is isolated: no path x₃ ⟶ x₁, contradicting the map terminality provides.
    cases ht.from Dot.x₃ with
    | cons r e => cases e; cases r with | cons r' e' => cases e'
  case x₂ =>
    -- No arrow lands on x₂, so no path x₃ ⟶ x₂.
    cases ht.from Dot.x₃ with | cons r e => cases e
  case x₃ =>
    -- No arrow lands on x₃, so no path x₁ ⟶ x₃.
    cases ht.from Dot.x₁ with | cons r e => cases e

end Ex17_1_f

/-!
Exercise 17.2 (p. 202)
-/
namespace Ex17_2

inductive Dot
  | x₁ | x₂

inductive Arrow : Dot → Dot → Type
  | f : Arrow .x₁ .x₂
  | g : Arrow .x₂ .x₁

instance : Quiver Dot where
  Hom := Arrow

/-- The morphism `F` assigns to the (unique, once the diagram commutes) path between
    any two dots: identities on the diagonal, `f'`/`g'` off it. -/
private def canon {𝒞 : Type u} [Category.{v, u} 𝒞] (F : Paths Dot ⥤ 𝒞) :
    (a b : Dot) → (F.obj a ⟶ F.obj b)
  | .x₁, .x₁ => 𝟙 _
  | .x₁, .x₂ => F.map (Quiver.Hom.toPath Arrow.f)
  | .x₂, .x₁ => F.map (Quiver.Hom.toPath Arrow.g)
  | .x₂, .x₂ => 𝟙 _

-- A diagram of shape G (two dots, an arrow each way) commutes — meaning any two
-- parallel paths in G are sent to the *same* morphism in 𝒞 — iff the maps `f'`, `g'`
-- assigned to the two arrows are inverse to each other.
example {𝒞 : Type u} [Category.{v, u} 𝒞] (F : Paths Dot ⥤ 𝒞) :
    (∀ (a b : Dot) (p q : Quiver.Path a b), F.map p = F.map q) ↔
    F.map (Quiver.Hom.toPath Arrow.g) ⊚ F.map (Quiver.Hom.toPath Arrow.f) = 𝟙 (F.obj Dot.x₁) ∧
    F.map (Quiver.Hom.toPath Arrow.f) ⊚ F.map (Quiver.Hom.toPath Arrow.g) = 𝟙 (F.obj Dot.x₂) := by
  constructor
  · -- Commuting forces the two round trips to equal the identities.
    intro h
    refine ⟨?_, ?_⟩
    · have e := h Dot.x₁ Dot.x₁ (𝟙 ((Paths.of Dot).obj Dot.x₁))
        ((Paths.of Dot).map Arrow.f ≫ (Paths.of Dot).map Arrow.g)
      simp only [Functor.map_comp, Functor.map_id, Paths.of_map, Paths.of_obj] at e
      exact e.symm
    · have e := h Dot.x₂ Dot.x₂ (𝟙 ((Paths.of Dot).obj Dot.x₂))
        ((Paths.of Dot).map Arrow.g ≫ (Paths.of Dot).map Arrow.f)
      simp only [Functor.map_comp, Functor.map_id, Paths.of_map, Paths.of_obj] at e
      exact e.symm
  · -- If the two maps are inverse, every path collapses onto `canon`, so all parallel
    -- paths agree.
    rintro ⟨hf, hg⟩
    have key : ∀ (a : Dot) {b : Dot} (p : Quiver.Path a b), F.map p = canon F a b := by
      intro a b p
      induction p using CategoryTheory.Paths.induction_fixed_source with
      | id => cases a <;> simp [canon]
      | comp p q ih =>
          rw [F.map_comp, ih]
          cases q <;> cases a <;>
            simp_all [canon, CategoryTheory.Paths.of_map, CategoryTheory.Paths.of_obj]
    intro a b p q
    rw [key a p, key a q]

end Ex17_2

/-!
Exercise 17.3 (p. 203)
-/
namespace Ex17_3

inductive Vertex
  | A | B | C | D | E | F | G | H

inductive Edge : Vertex → Vertex → Type
  | f : Edge .A .B
  | g : Edge .B .C
  | h : Edge .C .D
  | i : Edge .A .E
  | j : Edge .B .F
  | k : Edge .C .G
  | l : Edge .D .H
  | m : Edge .E .F
  | n : Edge .F .G
  | p : Edge .G .H

instance : Quiver Vertex where
  Hom := Edge

open Edge Quiver Quiver.Hom Quiver.Path Vertex in
example
    (h₁ : (toPath f |>.comp (toPath j)) =
          (toPath i |>.comp (toPath m) : Path A F))
    (h₂ : (toPath g |>.comp (toPath k)) =
          (toPath j |>.comp (toPath n) : Path B G))
    (h₃ : (toPath h |>.comp (toPath l)) =
          (toPath k |>.comp (toPath p) : Path C H))
    : (toPath i
          |>.comp (toPath m)
          |>.comp (toPath n)
          |>.comp (toPath p)) =
      (toPath f
          |>.comp (toPath g)
          |>.comp (toPath h)
          |>.comp (Hom.toPath l) : Path A H) := by
  -- Chase the three commuting squares, regrouping with associativity between each step:
  --   i;m;n;p = f;j;n;p = f;g;k;p = f;g;h;l
  set F : Quiver.Path Vertex.A Vertex.B := Quiver.Hom.toPath Edge.f
  set G : Quiver.Path Vertex.B Vertex.C := Quiver.Hom.toPath Edge.g
  set K : Quiver.Path Vertex.C Vertex.G := Quiver.Hom.toPath Edge.k
  set J : Quiver.Path Vertex.B Vertex.F := Quiver.Hom.toPath Edge.j
  set N : Quiver.Path Vertex.F Vertex.G := Quiver.Hom.toPath Edge.n
  set P : Quiver.Path Vertex.G Vertex.H := Quiver.Hom.toPath Edge.p
  set Hh : Quiver.Path Vertex.C Vertex.D := Quiver.Hom.toPath Edge.h
  set L : Quiver.Path Vertex.D Vertex.H := Quiver.Hom.toPath Edge.l
  rw [← h₁,
      Quiver.Path.comp_assoc F J N,
      ← h₂,
      ← Quiver.Path.comp_assoc F G K,
      Quiver.Path.comp_assoc (F.comp G) K P,
      ← h₃,
      ← Quiver.Path.comp_assoc (F.comp G) Hh L]

end Ex17_3

/-!
Exercise 17.4 (p. 203)
-/
namespace Ex17_4_a

inductive Vertex
  | A | B

-- Two parallel arrows A ⇉ B.
inductive Edge : Vertex → Vertex → Type
  | f : Edge .A .B
  | g : Edge .A .B

instance : Quiver Vertex where
  Hom := Edge

-- Shortest list of equations making the diagram commute: the single equation `f = g`.
-- Indeed the diagram commutes — any two parallel paths agree — iff 𝐹 sends f and g to
-- the same map. (The graph is acyclic, so `f = g` alone already forces commutativity.)
example {𝒞 : Type u} [Category.{v, u} 𝒞] (F : Paths Vertex ⥤ 𝒞) :
    (∀ (a b : Vertex) (p q : Quiver.Path a b), F.map p = F.map q) ↔
    F.map (Quiver.Hom.toPath Edge.f) = F.map (Quiver.Hom.toPath Edge.g) := by
  constructor
  · -- Commuting equates the two parallel arrows f, g : A ⟶ B.
    intro hcomm
    exact hcomm _ _ (Quiver.Hom.toPath Edge.f) (Quiver.Hom.toPath Edge.g)
  · intro hfg
    -- Normal forms: A→A and B→B contain only `nil`, A→B only `f`/`g`, and B→A is empty.
    have hAB : ∀ (p : Quiver.Path Vertex.A Vertex.B),
        F.map p = F.map (Quiver.Hom.toPath Edge.f) := by
      intro p
      cases p with
      | cons p' e =>
        cases e with
        | f => cases p' with
          | nil => rfl
          | cons _ e' => cases e'
        | g => cases p' with
          | nil => exact hfg.symm
          | cons _ e' => cases e'
    have hAA : ∀ (p : Quiver.Path Vertex.A Vertex.A), p = Quiver.Path.nil := by
      intro p; cases p with
      | nil => rfl
      | cons _ e => cases e
    have hBB : ∀ (p : Quiver.Path Vertex.B Vertex.B), p = Quiver.Path.nil := by
      intro p; cases p with
      | nil => rfl
      | cons p' e =>
        cases e with
        | f => cases p' with | cons _ e' => cases e'
        | g => cases p' with | cons _ e' => cases e'
    intro a b p q
    cases a <;> cases b
    · rw [hAA p, hAA q]
    · rw [hAB p, hAB q]
    · cases p with | cons _ e => cases e
    · rw [hBB p, hBB q]

end Ex17_4_a

namespace Ex17_4_b

inductive Vertex
  | A | B | C

inductive Edge : Vertex → Vertex → Type
  | f : Edge .A .B
  | g : Edge .B .C
  | h : Edge .C .A

instance : Quiver Vertex where
  Hom := Edge

/-- Canonical interpretation of a path once the 3-cycle commutes. -/
private def canon {𝒞 : Type u} [Category.{v, u} 𝒞] (F : Paths Vertex ⥤ 𝒞) :
    (a b : Vertex) → (F.obj a ⟶ F.obj b)
  | .A, .A => 𝟙 _
  | .B, .B => 𝟙 _
  | .C, .C => 𝟙 _
  | .A, .B => F.map (Quiver.Hom.toPath Edge.f)
  | .B, .C => F.map (Quiver.Hom.toPath Edge.g)
  | .C, .A => F.map (Quiver.Hom.toPath Edge.h)
  | .A, .C => F.map (Quiver.Hom.toPath Edge.g) ⊚ F.map (Quiver.Hom.toPath Edge.f)
  | .B, .A => F.map (Quiver.Hom.toPath Edge.h) ⊚ F.map (Quiver.Hom.toPath Edge.g)
  | .C, .B => F.map (Quiver.Hom.toPath Edge.f) ⊚ F.map (Quiver.Hom.toPath Edge.h)

-- Shortest list of equations making the triangle commute: the three round trips
-- f;g;h, g;h;f, h;f;g are identities. (No two of them imply the third — a
-- Set-valued counterexample with |C| = 2 shows all three are needed.)
example {𝒞 : Type u} [Category.{v, u} 𝒞] (F : Paths Vertex ⥤ 𝒞) :
    (∀ (a b : Vertex) (p q : Quiver.Path a b), F.map p = F.map q) ↔
    F.map (Quiver.Hom.toPath Edge.h) ⊚ F.map (Quiver.Hom.toPath Edge.g) ⊚
        F.map (Quiver.Hom.toPath Edge.f) = 𝟙 (F.obj Vertex.A) ∧
    F.map (Quiver.Hom.toPath Edge.f) ⊚ F.map (Quiver.Hom.toPath Edge.h) ⊚
        F.map (Quiver.Hom.toPath Edge.g) = 𝟙 (F.obj Vertex.B) ∧
    F.map (Quiver.Hom.toPath Edge.g) ⊚ F.map (Quiver.Hom.toPath Edge.f) ⊚
        F.map (Quiver.Hom.toPath Edge.h) = 𝟙 (F.obj Vertex.C) := by
  constructor
  · -- Commuting equates each round trip with the identity `nil`.
    intro hcomm
    refine ⟨?_, ?_, ?_⟩
    · have e := hcomm Vertex.A Vertex.A ((Paths.of Vertex).map Edge.f ≫
        (Paths.of Vertex).map Edge.g ≫ (Paths.of Vertex).map Edge.h)
        (𝟙 ((Paths.of Vertex).obj Vertex.A))
      simpa [Functor.map_comp, Functor.map_id, Paths.of_map, Category.assoc] using e
    · have e := hcomm Vertex.B Vertex.B ((Paths.of Vertex).map Edge.g ≫
        (Paths.of Vertex).map Edge.h ≫ (Paths.of Vertex).map Edge.f)
        (𝟙 ((Paths.of Vertex).obj Vertex.B))
      simpa [Functor.map_comp, Functor.map_id, Paths.of_map, Category.assoc] using e
    · have e := hcomm Vertex.C Vertex.C ((Paths.of Vertex).map Edge.h ≫
        (Paths.of Vertex).map Edge.f ≫ (Paths.of Vertex).map Edge.g)
        (𝟙 ((Paths.of Vertex).obj Vertex.C))
      simpa [Functor.map_comp, Functor.map_id, Paths.of_map, Category.assoc] using e
  · -- Conversely, the three identities collapse every path onto `canon`.
    rintro ⟨hA, hB, hC⟩
    have key : ∀ (a : Vertex) {b : Vertex} (p : Quiver.Path a b), F.map p = canon F a b := by
      intro a b p
      induction p using CategoryTheory.Paths.induction_fixed_source with
      | id => cases a <;> simp [canon]
      | comp p q ih =>
          rw [F.map_comp, ih]
          cases q <;> cases a <;>
            simp_all [canon, CategoryTheory.Paths.of_map, CategoryTheory.Paths.of_obj,
              Category.assoc]
    intro a b p q
    rw [key a p, key a q]

end Ex17_4_b

namespace Ex17_4_c

inductive Vertex
  | A | B | C

inductive Edge : Vertex → Vertex → Type
  | f : Edge .A .B
  | g : Edge .A .B
  | h : Edge .B .C
  | i : Edge .C .C
  | j : Edge .C .A

instance : Quiver Vertex where
  Hom := Edge

/-- Canonical interpretation of a path once the diagram commutes (f' = g' and the
    self-loop i' = 𝟙, so the effective cycle is g, h, j). -/
private def canon {𝒞 : Type u} [Category.{v, u} 𝒞] (F : Paths Vertex ⥤ 𝒞) :
    (a b : Vertex) → (F.obj a ⟶ F.obj b)
  | .A, .A => 𝟙 _
  | .B, .B => 𝟙 _
  | .C, .C => 𝟙 _
  | .A, .B => F.map (Quiver.Hom.toPath Edge.g)
  | .B, .C => F.map (Quiver.Hom.toPath Edge.h)
  | .C, .A => F.map (Quiver.Hom.toPath Edge.j)
  | .A, .C => F.map (Quiver.Hom.toPath Edge.h) ⊚ F.map (Quiver.Hom.toPath Edge.g)
  | .B, .A => F.map (Quiver.Hom.toPath Edge.j) ⊚ F.map (Quiver.Hom.toPath Edge.h)
  | .C, .B => F.map (Quiver.Hom.toPath Edge.g) ⊚ F.map (Quiver.Hom.toPath Edge.j)

-- Shortest list of equations making the diagram commute: the parallel pair must agree
-- (f = g), the self-loop must be trivial (i = 𝟙), and the three round trips of the
-- g,h,j-triangle must be identities.
example {𝒞 : Type u} [Category.{v, u} 𝒞] (F : Paths Vertex ⥤ 𝒞) :
    (∀ (a b : Vertex) (p q : Quiver.Path a b), F.map p = F.map q) ↔
    F.map (Quiver.Hom.toPath Edge.j) ⊚ F.map (Quiver.Hom.toPath Edge.h) ⊚
        F.map (Quiver.Hom.toPath Edge.g) = 𝟙 (F.obj Vertex.A) ∧
    F.map (Quiver.Hom.toPath Edge.g) ⊚ F.map (Quiver.Hom.toPath Edge.j) ⊚
        F.map (Quiver.Hom.toPath Edge.h) = 𝟙 (F.obj Vertex.B) ∧
    F.map (Quiver.Hom.toPath Edge.h) ⊚ F.map (Quiver.Hom.toPath Edge.g) ⊚
        F.map (Quiver.Hom.toPath Edge.j) = 𝟙 (F.obj Vertex.C) ∧
    F.map (Quiver.Hom.toPath Edge.f) = F.map (Quiver.Hom.toPath Edge.g) ∧
    F.map (Quiver.Hom.toPath Edge.i) = 𝟙 (F.obj Vertex.C) := by
  constructor
  · intro hcomm
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have e := hcomm Vertex.A Vertex.A ((Paths.of Vertex).map Edge.g ≫
        (Paths.of Vertex).map Edge.h ≫ (Paths.of Vertex).map Edge.j)
        (𝟙 ((Paths.of Vertex).obj Vertex.A))
      simpa [Functor.map_comp, Functor.map_id, Paths.of_map, Category.assoc] using e
    · have e := hcomm Vertex.B Vertex.B ((Paths.of Vertex).map Edge.h ≫
        (Paths.of Vertex).map Edge.j ≫ (Paths.of Vertex).map Edge.g)
        (𝟙 ((Paths.of Vertex).obj Vertex.B))
      simpa [Functor.map_comp, Functor.map_id, Paths.of_map, Category.assoc] using e
    · have e := hcomm Vertex.C Vertex.C ((Paths.of Vertex).map Edge.j ≫
        (Paths.of Vertex).map Edge.g ≫ (Paths.of Vertex).map Edge.h)
        (𝟙 ((Paths.of Vertex).obj Vertex.C))
      simpa [Functor.map_comp, Functor.map_id, Paths.of_map, Category.assoc] using e
    · exact hcomm Vertex.A Vertex.B (Quiver.Hom.toPath Edge.f) (Quiver.Hom.toPath Edge.g)
    · have e := hcomm Vertex.C Vertex.C ((Paths.of Vertex).map Edge.i)
        (𝟙 ((Paths.of Vertex).obj Vertex.C))
      simpa [Functor.map_id, Paths.of_map] using e
  · rintro ⟨hA, hB, hC, hfg, hi⟩
    have key : ∀ (a : Vertex) {b : Vertex} (p : Quiver.Path a b), F.map p = canon F a b := by
      intro a b p
      induction p using CategoryTheory.Paths.induction_fixed_source with
      | id => cases a <;> simp [canon]
      | comp p q ih =>
          rw [F.map_comp, ih]
          cases q <;> cases a <;>
            simp_all [canon, CategoryTheory.Paths.of_map, CategoryTheory.Paths.of_obj,
              Category.assoc]
    intro a b p q
    rw [key a p, key a q]

end Ex17_4_c

end CM

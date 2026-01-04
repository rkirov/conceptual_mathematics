import Mathlib
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
  by_contra h
  have h_uniq : Unique (Quiver.Path Dot.x₁ Dot.x₁) :=
    uniqueToTerminal (C := Paths Dot) Dot.x₁
  have h_sub : Subsingleton (Quiver.Path Dot.x₁ Dot.x₁) :=
    inferInstance
  have h_nontriv : Nontrivial (Quiver.Path Dot.x₁ Dot.x₁) := by
    apply nontrivial_iff.mpr
    use Quiver.Path.nil, (Quiver.Hom.toPath Arrow.f₁)
    intro
    contradiction
  exact false_of_nontrivial_of_subsingleton
      (Quiver.Path Dot.x₁ Dot.x₁)

end Ex17_1_a

namespace Ex17_1_b

inductive Dot
  | x₁

inductive Arrow : Dot → Dot → Type

instance : Quiver Dot where
  Hom := Arrow

open Limits in
example : HasTerminal (Paths Dot) := by
  have h_all_sub
      : ∀ (x : Paths Dot), Subsingleton (x ⟶ Dot.x₁) := by
    intro x
    apply Subsingleton.intro
    intro f g
    let P : {x : Paths Dot} → (x ⟶ Dot.x₁) → Prop :=
      fun p => p = Quiver.Path.nil
    have h_all_eq_id : ∀ {x : Paths Dot} (p : x ⟶ Dot.x₁), P p := by
      intros
      apply Paths.induction_fixed_target
      · rfl
      · intro _ _ _ e _
        nomatch e
    rw [h_all_eq_id f, h_all_eq_id g]
  have h_all_nonempty
      : ∀ (x : Paths Dot), Nonempty (x ⟶ Dot.x₁) := by
    intro x
    exact Nonempty.intro Quiver.Path.nil
  exact hasTerminal_of_unique (C := Paths Dot) Dot.x₁

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
  have h_all_sub
      : ∀ (x : Paths Dot), Subsingleton (x ⟶ Dot.x₄) := by
    intro x
    apply Subsingleton.intro
    intro f g
    cases x
    all_goals
      repeat first
      | (rcases f with _ | ⟨f, _, _⟩) -- deconstruct f
      | (rcases g with _ | ⟨g, _, _⟩) -- deconstruct g
      | contradiction
      | rfl
  have h_all_nonempty
      : ∀ (x : Paths Dot), Nonempty (x ⟶ Dot.x₄) := by
    intro x
    cases x
    · exact Nonempty.intro
          ((Quiver.Hom.toPath Arrow.f₁).cons Arrow.f₃)
    · exact Nonempty.intro
          ((Quiver.Hom.toPath Arrow.f₂).cons Arrow.f₃)
    · exact Nonempty.intro
          (Quiver.Hom.toPath Arrow.f₃)
    · exact Nonempty.intro
          Quiver.Path.nil
    · exact Nonempty.intro
          (Quiver.Hom.toPath Arrow.f₅)
  exact hasTerminal_of_unique (C := Paths Dot) Dot.x₄

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
  by_contra h
  have h_all_uniq
      : ∀ (x : Paths Dot), Unique (x ⟶ ⊤_ Paths Dot) := by
    intro x
    exact uniqueToTerminal x
  have h_all_sub
      : ∀ (x : Paths Dot), Subsingleton (x ⟶ ⊤_ Paths Dot) := by
    intro x
    infer_instance
  have h_nontriv₁ : Nontrivial (Quiver.Path Dot.x₁ Dot.x₁) := by
    apply nontrivial_iff.mpr
    use Quiver.Path.nil, ((Quiver.Hom.toPath Arrow.f₁).cons Arrow.f₂)
    intro
    contradiction
  have h_nontriv₂ : Nontrivial (Quiver.Path Dot.x₂ Dot.x₂) := by
    apply nontrivial_iff.mpr
    use Quiver.Path.nil, ((Quiver.Hom.toPath Arrow.f₂).cons Arrow.f₁)
    intro
    contradiction
  cases hx : ⊤_ (Paths Dot) <;> rw [hx] at h_all_sub
  · exact false_of_nontrivial_of_subsingleton
        (Quiver.Path Dot.x₁ Dot.x₁)
  · exact false_of_nontrivial_of_subsingleton
        (Quiver.Path Dot.x₂ Dot.x₂)

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
  by_contra h
  have h_all_uniq
      : ∀ (x : Paths Dot), Unique (x ⟶ ⊤_ Paths Dot) := by
    intro x
    exact uniqueToTerminal x
  have h_all_sub
      : ∀ (x : Paths Dot), Subsingleton (x ⟶ ⊤_ Paths Dot) := by
    intro x
    infer_instance
  have h_empty₁ : ¬(Nonempty (Quiver.Path Dot.x₂ Dot.x₁)) := by
    by_contra h_empty
    rcases h_empty with ⟨p⟩
    nomatch p
  have h_nontriv₂ : Nontrivial (Quiver.Path Dot.x₁ Dot.x₂) := by
    apply nontrivial_iff.mpr
    use (Quiver.Hom.toPath Arrow.f₁), (Quiver.Hom.toPath Arrow.f₂)
    intro H
    injection H with _ h_arrow
    contradiction
  cases hx : ⊤_ (Paths Dot)
  · rw [hx] at h_all_uniq h_all_sub
    have h_uniq₁ : Unique (Quiver.Path Dot.x₂ Dot.x₁) :=
      h_all_uniq Dot.x₂
    have h_nonempty₁ : Nonempty (Quiver.Path Dot.x₂ Dot.x₁) := by
      infer_instance
    contradiction
  · rw [hx] at h_all_sub
    exact false_of_nontrivial_of_subsingleton
        (Quiver.Path Dot.x₁ Dot.x₂)

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
  by_contra h
  have h_all_uniq
      : ∀ (x : Paths Dot), Unique (x ⟶ ⊤_ Paths Dot) := by
    intro x
    exact uniqueToTerminal x
  have h_all_sub
      : ∀ (x : Paths Dot), Subsingleton (x ⟶ ⊤_ Paths Dot) := by
    intro x
    infer_instance
  have h_empty₁ : ¬(Nonempty (Quiver.Path Dot.x₃ Dot.x₁)) := by
    by_contra h_empty
    rcases h_empty with ⟨p⟩
    match p with
    | .cons p' q =>
      match p' with
      | .nil =>
      nomatch q
  have h_empty₂ : ¬(Nonempty (Quiver.Path Dot.x₃ Dot.x₂)) := by
    by_contra h_empty
    rcases h_empty with ⟨p⟩
    nomatch p
  have h_empty₃ : ¬(Nonempty (Quiver.Path Dot.x₂ Dot.x₃)) := by
    by_contra h_empty
    rcases h_empty with ⟨p⟩
    nomatch p
  cases hx : ⊤_ (Paths Dot) <;> rw [hx] at h_all_uniq h_all_sub
  · have h_uniq₁ : Unique (Quiver.Path Dot.x₃ Dot.x₁) :=
      h_all_uniq Dot.x₃
    have h_nonempty₂ : Nonempty (Quiver.Path Dot.x₃ Dot.x₁) := by
      infer_instance
    contradiction
  · have h_uniq₂ : Unique (Quiver.Path Dot.x₃ Dot.x₂) :=
      h_all_uniq Dot.x₃
    have h_nonempty₂ : Nonempty (Quiver.Path Dot.x₃ Dot.x₂) := by
      infer_instance
    contradiction
  · have h_uniq₃ : Unique (Quiver.Path Dot.x₂ Dot.x₃) :=
      h_all_uniq Dot.x₂
    have h_nonempty₃ : Nonempty (Quiver.Path Dot.x₂ Dot.x₃) := by
      infer_instance
    contradiction

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

example {𝒞 : Type u} [Category.{v, u} 𝒞] (F : Paths Dot ⥤ 𝒞) :
    -- Let x₁' be the object in 𝒞 associated with Dot.x₁ in 𝐹(G)
    let x₁' : 𝒞 := F.obj Dot.x₁
    -- Let x₂' be the object in 𝒞 associated with Dot.x₂ in 𝐹(G)
    let x₂' : 𝒞 := F.obj Dot.x₂
    -- Let f' be the morphism in 𝒞 associated with Arrow.f in 𝐹(G)
    let f' : x₁' ⟶ x₂' := F.map (Quiver.Hom.toPath Arrow.f)
    -- Let g' be the morphism in 𝒞 associated with Arrow.g in 𝐹(G)
    let g' : x₂' ⟶ x₁' := F.map (Quiver.Hom.toPath Arrow.g)
    -- Dot.x₁ ⟶ Dot.x₁ is interpreted as the identity on x₁' in 𝒞
    (∀ p₁ : Quiver.Path Dot.x₁ Dot.x₁, F.map p₁ = 𝟙 x₁') ∧
    -- Dot.x₂ ⟶ Dot.x₂ is interpreted as the identity on x₂' in 𝒞
    (∀ p₂ : Quiver.Path Dot.x₂ Dot.x₂, F.map p₂ = 𝟙 x₂') ∧
    -- Dot.x₁ ⟶ Dot.x₂ is interpreted as f' in 𝒞
    (∀ p₁₂ : Quiver.Path Dot.x₁ Dot.x₂, F.map p₁₂ = f') ∧
    -- Dot.x₂ ⟶ Dot.x₁ is interpreted as g' in 𝒞
    (∀ p₂₁ : Quiver.Path Dot.x₂ Dot.x₁, F.map p₂₁ = g') ↔
    -- The maps assigned to the two arrows in G are inverse
    g' ⊚ f' = 𝟙 x₁' ∧ f' ⊚ g' = 𝟙 x₂' := by
  constructor
  -- Proof of the forward ("only if") direction
  · repeat rw [← F.map_comp]
    intro ⟨h₁, h₂, h₁₂, h₂₁⟩
    constructor
    · rw [h₁]
    · rw [h₂]
  -- Proof of the backward ("if") direction
  · repeat rw [← F.map_comp]
    intro ⟨h₁, h₂⟩
    and_intros
    -- ∀ p₁ : Quiver.Path Dot.x₁ Dot.x₁, F.map p₁ = 𝟙 x₁'
    · let rec aux₁ (p : Quiver.Path Dot.x₁ Dot.x₁)
          : F.map p = 𝟙 (F.obj Dot.x₁) := by
        match p with
        | .nil =>
          exact F.map_id Dot.x₁
        | .cons tail Arrow.g =>
          match tail with
          | .cons tail' Arrow.f =>
            change F.map ((Quiver.Hom.toPath Arrow.g ⊚
                           Quiver.Hom.toPath Arrow.f) ⊚ tail') = _
            rw [Functor.map_comp, h₁, Category.comp_id]
            exact aux₁ tail'
      intro p
      exact aux₁ p
    -- ∀ p₂ : Quiver.Path Dot.x₂ Dot.x₂, F.map p₂ = 𝟙 x₂'
    · let rec aux₂ (p : Quiver.Path Dot.x₂ Dot.x₂)
          : F.map p = 𝟙 (F.obj Dot.x₂) := by
        match p with
        | .nil =>
          exact F.map_id Dot.x₂
        | .cons tail Arrow.f =>
          match tail with
          | .cons tail' Arrow.g =>
            change F.map ((Quiver.Hom.toPath Arrow.f ⊚
                           Quiver.Hom.toPath Arrow.g) ⊚ tail') = _
            rw [Functor.map_comp, h₂, Category.comp_id]
            exact aux₂ tail'
      intro p
      exact aux₂ p
    -- ∀ p₁₂ : Quiver.Path Dot.x₁ Dot.x₂, F.map p₁₂ = f'
    · let rec aux₁₂ (p : Quiver.Path Dot.x₁ Dot.x₂)
          : F.map p = F.map (Quiver.Hom.toPath Arrow.f) := by
        match p with
        | .cons tail Arrow.f =>
          match tail with
          | .nil =>
            rfl
          | .cons tail' Arrow.g =>
            change F.map ((Quiver.Hom.toPath Arrow.f ⊚
                           Quiver.Hom.toPath Arrow.g) ⊚ tail') = _
            rw [Functor.map_comp, h₂, Category.comp_id]
            exact aux₁₂ tail'
      intro p
      exact aux₁₂ p
    -- ∀ p₂₁ : Quiver.Path Dot.x₂ Dot.x₁, F.map p₂₁ = g'
    · let rec aux₂₁ (p : Quiver.Path Dot.x₂ Dot.x₁)
          : F.map p = F.map (Quiver.Hom.toPath Arrow.g) := by
        match p with
        | .cons tail Arrow.g =>
          match tail with
          | .nil =>
            rfl
          | .cons tail' Arrow.f =>
            change F.map ((Quiver.Hom.toPath Arrow.g ⊚
                           Quiver.Hom.toPath Arrow.f) ⊚ tail') = _
            rw [Functor.map_comp, h₁, Category.comp_id]
            exact aux₂₁ tail'
      intro p
      exact aux₂₁ p

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
  rw [comp_assoc, ← h₁]
  rw [← comp_assoc, comp_assoc (a := A) (toPath f), ← h₂]
  rw [comp_assoc, comp_assoc, ← h₃]
  repeat rw [← comp_assoc]

end Ex17_3

/-!
Exercise 17.4 (p. 203)
-/
namespace Ex17_4_a

inductive Vertex
  | A | B

inductive Edge : Vertex → Vertex → Type
  | f : Edge .A .B
  | g : Edge .B .A
  | h : Edge .B .A

instance : Quiver Vertex where
  Hom := Edge

example {𝒞 : Type u} [Category.{v, u} 𝒞] (F : Paths Vertex ⥤ 𝒞) :
    -- Let A' be the object in 𝒞 associated with Vertex.A in 𝐹(G)
    let A' : 𝒞 := F.obj Vertex.A
    -- Let B' be the object in 𝒞 associated with Vertex.B in 𝐹(G)
    let B' : 𝒞 := F.obj Vertex.B
    -- Let f' be the morphism in 𝒞 associated with Edge.f in 𝐹(G)
    let f' : A' ⟶ B' := F.map (Quiver.Hom.toPath Edge.f)
    -- Let g' be the morphism in 𝒞 associated with Edge.g in 𝐹(G)
    let g' : B' ⟶ A' := F.map (Quiver.Hom.toPath Edge.g)
    -- Let h' be the morphism in 𝒞 associated with Edge.h in 𝐹(G)
    let h' : B' ⟶ A' := F.map (Quiver.Hom.toPath Edge.h)
    -- The 3 equations required to make the diagram commute
    g' ⊚ f' = 𝟙 A' ∧
    f' ⊚ g' = 𝟙 B' ∧
    g' = h' →
    -- .A ⟶ .A is interpreted as the identity on A' in 𝒞
    (∀ p : Quiver.Path Vertex.A Vertex.A, F.map p = 𝟙 A') ∧
    -- .B ⟶ .B is interpreted as the identity on B' in 𝒞
    (∀ p : Quiver.Path Vertex.B Vertex.B, F.map p = 𝟙 B') ∧
    -- .A ⟶ .B is interpreted as f' in 𝒞
    (∀ p : Quiver.Path Vertex.A Vertex.B, F.map p = f') ∧
    -- .B ⟶ .A is interpreted as g' in 𝒞
    (∀ p : Quiver.Path Vertex.B Vertex.A, F.map p = g') := by
  intro A' B' f' g' h' ⟨h₁, h₂, h₃⟩
  dsimp [A', B', f', g', h'] at h₁ h₂ h₃
  rw [← F.map_comp] at h₁ h₂
  and_intros
  -- ∀ p : Quiver.Path Vertex.A Vertex.A, F.map p = 𝟙 A'
  · let rec auxAA (p : Quiver.Path Vertex.A Vertex.A)
        : F.map p = 𝟙 (F.obj Vertex.A) := by
      match p with
      | .nil =>
        exact F.map_id _
      | .cons (.cons tail Edge.f) (e : Vertex.B ⟶ Vertex.A) =>
        have : F.map ((tail.cons Edge.f).cons e) =
               F.map ((Quiver.Hom.toPath Edge.g ⊚
                       Quiver.Hom.toPath Edge.f) ⊚ tail) := by
          rcases e
          · rfl
          · change F.map (Quiver.Hom.toPath Edge.h ⊚
                          Quiver.Hom.toPath Edge.f ⊚ tail) = _
            rw [Functor.map_comp, ← h₃, ← Functor.map_comp,
                Category.assoc]
        rw [this]
        rw [Functor.map_comp, h₁, Category.comp_id]
        exact auxAA tail
    intro p
    exact auxAA p
  -- ∀ p : Quiver.Path Vertex.B Vertex.B, F.map p = 𝟙 B'
  · let rec auxBB (p : Quiver.Path Vertex.B Vertex.B)
        : F.map p = 𝟙 (F.obj Vertex.B) := by
      match p with
      | .nil =>
        exact F.map_id _
      | .cons (.cons tail (e : Vertex.B ⟶ Vertex.A)) Edge.f =>
        have : F.map ((tail.cons e).cons Edge.f) =
               F.map ((Quiver.Hom.toPath Edge.f ⊚
                       Quiver.Hom.toPath Edge.g) ⊚ tail) := by
          rcases e
          · rfl
          · change F.map (Quiver.Hom.toPath Edge.f ⊚
                          Quiver.Hom.toPath Edge.h ⊚ tail) = _
            rw [Functor.map_comp, Functor.map_comp, ← h₃,
                ← Functor.map_comp, ← Functor.map_comp,
                Category.assoc]
        rw [this]
        rw [Functor.map_comp, h₂, Category.comp_id]
        exact auxBB tail
    intro p
    exact auxBB p
  -- ∀ p : Quiver.Path Vertex.A Vertex.B, F.map p = f'
  · let rec auxAB (p : Quiver.Path Vertex.A Vertex.B)
        : F.map p = F.map (Quiver.Hom.toPath Edge.f) := by
      match p with
      | .cons .nil Edge.f =>
        rfl
      | .cons (.cons tail (e : Vertex.B ⟶ Vertex.A)) Edge.f =>
        have : F.map ((tail.cons e).cons Edge.f) =
               F.map ((Quiver.Hom.toPath Edge.f ⊚
                       Quiver.Hom.toPath Edge.g) ⊚ tail) := by
          rcases e
          · rfl
          · change F.map ((Quiver.Hom.toPath Edge.f ⊚
                           Quiver.Hom.toPath Edge.h) ⊚ tail) = _
            rw [Functor.map_comp, Functor.map_comp, ← h₃,
                ← Functor.map_comp, ← Functor.map_comp]
        rw [this]
        rw [Functor.map_comp, h₂, Category.comp_id]
        exact auxAB tail
    intro p
    exact auxAB p
  -- ∀ p : Quiver.Path Vertex.B Vertex.A, F.map p = g'
  · let rec auxBA (p : Quiver.Path Vertex.B Vertex.A)
        : F.map p = F.map (Quiver.Hom.toPath Edge.g) := by
      match p with
      | .cons .nil (e : Vertex.B ⟶ Vertex.A) =>
        rcases e
        · rfl
        · rw [h₃]
          rfl
      | .cons (.cons tail Edge.f) (e : Vertex.B ⟶ Vertex.A) =>
        have : F.map ((tail.cons Edge.f).cons e) =
               F.map ((Quiver.Hom.toPath Edge.g ⊚
                       Quiver.Hom.toPath Edge.f) ⊚ tail) := by
          rcases e
          · rfl
          · change F.map ((Quiver.Hom.toPath Edge.h ⊚
                           Quiver.Hom.toPath Edge.f) ⊚ tail) = _
            rw [Functor.map_comp, Functor.map_comp, ← h₃,
                ← Functor.map_comp, ← Functor.map_comp]
        rw [this]
        rw [Functor.map_comp, h₁, Category.comp_id]
        exact auxBA tail
    intro p
    exact auxBA p

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

example {𝒞 : Type u} [Category.{v, u} 𝒞] (F : Paths Vertex ⥤ 𝒞) :
    -- Let A' be the object in 𝒞 associated with Vertex.A in 𝐹(G)
    let A' : 𝒞 := F.obj Vertex.A
    -- Let B' be the object in 𝒞 associated with Vertex.B in 𝐹(G)
    let B' : 𝒞 := F.obj Vertex.B
    -- Let C' be the object in 𝒞 associated with Vertex.C in 𝐹(G)
    let C' : 𝒞 := F.obj Vertex.C
    -- Let f' be the morphism in 𝒞 associated with Edge.f in 𝐹(G)
    let f' : A' ⟶ B' := F.map (Quiver.Hom.toPath Edge.f)
    -- Let g' be the morphism in 𝒞 associated with Edge.g in 𝐹(G)
    let g' : B' ⟶ C' := F.map (Quiver.Hom.toPath Edge.g)
    -- Let h' be the morphism in 𝒞 associated with Edge.h in 𝐹(G)
    let h' : C' ⟶ A' := F.map (Quiver.Hom.toPath Edge.h)
    -- The 3 equations required to make the diagram commute
    h' ⊚ g' ⊚ f' = 𝟙 A' ∧
    f' ⊚ h' ⊚ g' = 𝟙 B' ∧
    g' ⊚ f' ⊚ h' = 𝟙 C' →
    -- .A ⟶ .A is interpreted as the identity on A' in 𝒞
    (∀ p : Quiver.Path Vertex.A Vertex.A, F.map p = 𝟙 A') ∧
    -- .B ⟶ .B is interpreted as the identity on B' in 𝒞
    (∀ p : Quiver.Path Vertex.B Vertex.B, F.map p = 𝟙 B') ∧
    -- .C ⟶ .C is interpreted as the identity on C' in 𝒞
    (∀ p : Quiver.Path Vertex.C Vertex.C, F.map p = 𝟙 C') ∧
    -- .A ⟶ .B is interpreted as f' in 𝒞
    (∀ p : Quiver.Path Vertex.A Vertex.B, F.map p = f') ∧
    -- .B ⟶ .C is interpreted as g' in 𝒞
    (∀ p : Quiver.Path Vertex.B Vertex.C, F.map p = g') ∧
    -- .C ⟶ .A is interpreted as h' in 𝒞
    (∀ p : Quiver.Path Vertex.C Vertex.A, F.map p = h') ∧
    -- .A ⟶ .C is interpreted as g' ⊚ f' in 𝒞
    (∀ p : Quiver.Path Vertex.A Vertex.C, F.map p = g' ⊚ f') ∧
    -- .B ⟶ .A is interpreted as h' ⊚ g' in 𝒞
    (∀ p : Quiver.Path Vertex.B Vertex.A, F.map p = h' ⊚ g') ∧
    -- .C ⟶ .B is interpreted as f' ⊚ h' in 𝒞
    (∀ p : Quiver.Path Vertex.C Vertex.B, F.map p = f' ⊚ h') := by
  intro A' B' C' f' g' h' ⟨h₁, h₂, h₃⟩
  suffices ∀ {u v : Vertex} (p : Quiver.Path u v), F.map p =
    match u, v with
    | .A, .A => 𝟙 A'
    | .B, .B => 𝟙 B'
    | .C, .C => 𝟙 C'
    | .A, .B => f'
    | .B, .C => g'
    | .C, .A => h'
    | .A, .C => g' ⊚ f'
    | .B, .A => h' ⊚ g'
    | .C, .B => f' ⊚ h' by
    simp [this]
  dsimp [A', B', C', f', g', h'] at h₁ h₂ h₃
  intro u v p
  induction p with
  | nil =>
    cases u
    all_goals
      dsimp
      exact F.map_id _
  | cons p e ih =>
    change F.map (Quiver.Hom.toPath e ⊚ p) = _
    rw [F.map_comp, ih]
    cases u <;> rcases e
    all_goals
      dsimp [A', B', C', f', g', h']
      try rw [Category.id_comp]
      try first | rw [h₁] | rw [h₂] | rw [h₃]

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

example {𝒞 : Type u} [Category.{v, u} 𝒞] (F : Paths Vertex ⥤ 𝒞) :
    -- Let A' be the object in 𝒞 associated with Vertex.A in 𝐹(G)
    let A' : 𝒞 := F.obj Vertex.A
    -- Let B' be the object in 𝒞 associated with Vertex.B in 𝐹(G)
    let B' : 𝒞 := F.obj Vertex.B
    -- Let C' be the object in 𝒞 associated with Vertex.C in 𝐹(G)
    let C' : 𝒞 := F.obj Vertex.C
    -- Let f' be the morphism in 𝒞 associated with Edge.f in 𝐹(G)
    let f' : A' ⟶ B' := F.map (Quiver.Hom.toPath Edge.f)
    -- Let g' be the morphism in 𝒞 associated with Edge.g in 𝐹(G)
    let g' : A' ⟶ B' := F.map (Quiver.Hom.toPath Edge.g)
    -- Let h' be the morphism in 𝒞 associated with Edge.h in 𝐹(G)
    let h' : B' ⟶ C' := F.map (Quiver.Hom.toPath Edge.h)
    -- Let i' be the morphism in 𝒞 associated with Edge.i in 𝐹(G)
    let i' : C' ⟶ C' := F.map (Quiver.Hom.toPath Edge.i)
    -- Let j' be the morphism in 𝒞 associated with Edge.j in 𝐹(G)
    let j' : C' ⟶ A' := F.map (Quiver.Hom.toPath Edge.j)
    -- The 5 equations required to make the diagram commute
    j' ⊚ h' ⊚ g' = 𝟙 A' ∧
    g' ⊚ j' ⊚ h' = 𝟙 B' ∧
    h' ⊚ g' ⊚ j' = 𝟙 C' ∧
    f' = g' ∧
    i' = 𝟙 C' →
    -- .A ⟶ .A is interpreted as the identity on A' in 𝒞
    (∀ p : Quiver.Path Vertex.A Vertex.A, F.map p = 𝟙 A') ∧
    -- .B ⟶ .B is interpreted as the identity on B' in 𝒞
    (∀ p : Quiver.Path Vertex.B Vertex.B, F.map p = 𝟙 B') ∧
    -- .C ⟶ .C is interpreted as the identity on C' in 𝒞
    (∀ p : Quiver.Path Vertex.C Vertex.C, F.map p = 𝟙 C') ∧
    -- .A ⟶ .B is interpreted as g' in 𝒞
    (∀ p : Quiver.Path Vertex.A Vertex.B, F.map p = g') ∧
    -- .B ⟶ .C is interpreted as h' in 𝒞
    (∀ p : Quiver.Path Vertex.B Vertex.C, F.map p = h') ∧
    -- .C ⟶ .A is interpreted as j' in 𝒞
    (∀ p : Quiver.Path Vertex.C Vertex.A, F.map p = j') ∧
    -- .A ⟶ .C is interpreted as h' ⊚ g' in 𝒞
    (∀ p : Quiver.Path Vertex.A Vertex.C, F.map p = h' ⊚ g') ∧
    -- .B ⟶ .A is interpreted as j' ⊚ h' in 𝒞
    (∀ p : Quiver.Path Vertex.B Vertex.A, F.map p = j' ⊚ h') ∧
    -- .C ⟶ .B is interpreted as g' ⊚ j' in 𝒞
    (∀ p : Quiver.Path Vertex.C Vertex.B, F.map p = g' ⊚ j') := by
  intro A' B' C' f' g' h' i' j' ⟨h₁, h₂, h₃, h₄, h₅⟩
  suffices ∀ {u v : Vertex} (p : Quiver.Path u v), F.map p =
    match u, v with
    | .A, .A => 𝟙 A'
    | .B, .B => 𝟙 B'
    | .C, .C => 𝟙 C'
    | .A, .B => g'
    | .B, .C => h'
    | .C, .A => j'
    | .A, .C => h' ⊚ g'
    | .B, .A => j' ⊚ h'
    | .C, .B => g' ⊚ j' by
    simp [this]
  dsimp [A', B', C', f', g', h', i', j'] at h₁ h₂ h₃ h₄ h₅
  intro u v p
  induction p with
  | nil =>
    cases u
    all_goals
      dsimp
      exact F.map_id _
  | cons p e ih =>
    change F.map (Quiver.Hom.toPath e ⊚ p) = _
    rw [F.map_comp, ih]
    cases u <;> rcases e
    all_goals
      dsimp [A', B', C', f', g', h', i', j']
      try rw [h₄]
      try rw [h₅]
      try first | rw [Category.comp_id] | rw [Category.id_comp]
      try first | rw [h₁] | rw [h₂] | rw [h₃]

end Ex17_4_c

end CM


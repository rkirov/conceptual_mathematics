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
example : ¬(HasTerminal (Paths Dot)) :=
  sorry

end Ex17_1_a

namespace Ex17_1_b

inductive Dot
  | x₁

inductive Arrow : Dot → Dot → Type

instance : Quiver Dot where
  Hom := Arrow

open Limits in
example : HasTerminal (Paths Dot) :=
  sorry

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
example : HasTerminal (Paths Dot) :=
  sorry

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
example : ¬(HasTerminal (Paths Dot)) :=
  sorry

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
example : ¬(HasTerminal (Paths Dot)) :=
  sorry

end Ex17_1_e

namespace Ex17_1_f

inductive Dot
  | x₁ | x₂ | x₃

inductive Arrow : Dot → Dot → Type
  | f₁ : Arrow .x₂ .x₁

instance : Quiver Dot where
  Hom := Arrow

open Limits in
example : ¬(HasTerminal (Paths Dot)) :=
  sorry

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
    g' ⊚ f' = 𝟙 x₁' ∧ f' ⊚ g' = 𝟙 x₂' :=
  sorry

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
          |>.comp (Hom.toPath l) : Path A H) :=
  sorry

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
    (∀ p : Quiver.Path Vertex.B Vertex.A, F.map p = g') :=
  sorry

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
    (∀ p : Quiver.Path Vertex.C Vertex.B, F.map p = f' ⊚ h') :=
  sorry

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
    (∀ p : Quiver.Path Vertex.C Vertex.B, F.map p = g' ⊚ j') :=
  sorry

end Ex17_4_c

end CM

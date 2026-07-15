import ConceptualMathematics.Sorried.Article3
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise 11.1 (p. 153)
-/
namespace Ex11_1

inductive A
  | a₁ | a₂ | a₃

inductive X
  | x₁ | x₂ | x₃ | x₄

def A' : SetWithEndomap := {
  carrier := A
  toEnd := fun
    | A.a₁ => A.a₂
    | A.a₂ => A.a₃
    | A.a₃ => A.a₁
}

def X' : SetWithEndomap := {
  carrier := X
  toEnd := fun -- a restriction of α to the subset of 3-cycle and 1-cycle
    | X.x₁ => X.x₁
    | X.x₂ => X.x₃
    | X.x₃ => X.x₄
    | X.x₄ => X.x₂
}

def f₁ : A ⟶ X
  | A.a₁ => X.x₂
  | A.a₂ => X.x₃
  | A.a₃ => X.x₄

-- f₁ is structure-preserving
def f₁' : A' ⟶ X' := ⟨f₁, by
  ext x
  cases x <;> simp [A', X', f₁]⟩

def f₂ : A ⟶ X
  | A.a₁ => X.x₃
  | A.a₂ => X.x₄
  | A.a₃ => X.x₂

-- f₂ is structure-preserving
def f₂' : A' ⟶ X' := ⟨f₂, by
  ext x
  cases x <;> simp [A', X', f₂]⟩

def f₃ : A ⟶ X
  | A.a₁ => X.x₄
  | A.a₂ => X.x₂
  | A.a₃ => X.x₃

-- f₃ is structure-preserving
def f₃' : A' ⟶ X' := ⟨f₃, by
  ext x
  cases x <;> simp [A', X', f₃]⟩

def f₄ : A ⟶ X
  | A.a₁ => X.x₁
  | A.a₂ => X.x₁
  | A.a₃ => X.x₁

-- f₄ is structure-preserving
def f₄' : A' ⟶ X' := ⟨f₄, by
  ext x
  cases x <;> simp [A', X', f₄]⟩

-- proof that the four are distinct
example : List.Pairwise (· ≠ ·) [f₁, f₂, f₃, f₄] := by
  simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil,
    and_self, and_true]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
    intro h <;> exact absurd (congrFun h A.a₁) (by simp [f₁, f₂, f₃, f₄])

-- proof that any structure-preserving map is one of the four
example (f : A' ⟶ X') : f = f₁' ∨ f = f₂' ∨ f = f₃' ∨ f = f₄' := by
  cases f with
  | mk g h =>
    have h₁ := congr_fun h A.a₁
    have h₂ := congr_fun h A.a₂
    have h₃ := congr_fun h A.a₃
    simp only [X', A', types_comp_apply] at h₁ h₂ h₃
    rcases hx : g A.a₁ with _ | _ | _ | _ <;>
      simp only [hx] at h₁ <;> simp only [h₁] at h₂
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext (funext fun a => by
        cases a <;> simp [f₄', f₄, hx, h₁, h₂]))))
    · exact Or.inl (Subtype.ext (funext fun a => by
        cases a <;> simp [f₁', f₁, hx, h₁, h₂]))
    · exact Or.inr (Or.inl (Subtype.ext (funext fun a => by
        cases a <;> simp [f₂', f₂, hx, h₁, h₂])))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext (funext fun a => by
        cases a <;> simp [f₃', f₃, hx, h₁, h₂]))))

end Ex11_1

/-!
Exercise 11.2 (p. 158)
-/
namespace Ex11_2

inductive X
  | a | b | c

def α : X ⟶ X
  | X.a => X.b
  | X.b => X.c
  | X.c => X.a

def Xα : SetWithEndomap := {
  carrier := X
  toEnd := α
}

inductive Y
  | p | q | r

def β : Y ⟶ Y
  | Y.p => Y.q
  | Y.q => Y.r
  | Y.r => Y.p

def Yβ : SetWithEndomap := {
  carrier := Y
  toEnd := β
}

def f₁ : X ⟶ Y
  | X.a => Y.p
  | X.b => Y.q
  | X.c => Y.r

def f₂ : X ⟶ Y
  | X.a => Y.q
  | X.b => Y.r
  | X.c => Y.p

def f₃ : X ⟶ Y
  | X.a => Y.r
  | X.b => Y.p
  | X.c => Y.q

def f₁' : Xα ⟶ Yβ := ⟨f₁, by
  ext x
  cases x <;> simp [Xα, Yβ, f₁, α, β]⟩

def f₂' : Xα ⟶ Yβ := ⟨f₂, by
  ext x
  cases x <;> simp [Xα, Yβ, f₂, α, β]⟩

def f₃' : Xα ⟶ Yβ := ⟨f₃, by
  ext x
  cases x <;> simp [Xα, Yβ, f₃, α, β]⟩

-- the inverses of f₁, f₂, f₃
def g₁ : Y ⟶ X
  | Y.p => X.a
  | Y.q => X.b
  | Y.r => X.c

def g₂ : Y ⟶ X
  | Y.p => X.c
  | Y.q => X.a
  | Y.r => X.b

def g₃ : Y ⟶ X
  | Y.p => X.b
  | Y.q => X.c
  | Y.r => X.a

def g₁' : Yβ ⟶ Xα := ⟨g₁, by
  ext x
  cases x <;> simp [Xα, Yβ, g₁, α, β]⟩

def g₂' : Yβ ⟶ Xα := ⟨g₂, by
  ext x
  cases x <;> simp [Xα, Yβ, g₂, α, β]⟩

def g₃' : Yβ ⟶ Xα := ⟨g₃, by
  ext x
  cases x <;> simp [Xα, Yβ, g₃, α, β]⟩

example : IsIso f₁' := by
  refine ⟨g₁', ?_, ?_⟩ <;>
    apply Subtype.ext <;> funext x <;> cases x <;>
      simp [CategoryStruct.comp, CategoryStruct.id, SetWithEndomapHom.comp,
        SetWithEndomapHom.id, f₁', g₁', f₁, g₁]

example : IsIso f₂' := by
  refine ⟨g₂', ?_, ?_⟩ <;>
    apply Subtype.ext <;> funext x <;> cases x <;>
      simp [CategoryStruct.comp, CategoryStruct.id, SetWithEndomapHom.comp,
        SetWithEndomapHom.id, f₂', g₂', f₂, g₂]

example : IsIso f₃' := by
  refine ⟨g₃', ?_, ?_⟩ <;>
    apply Subtype.ext <;> funext x <;> cases x <;>
      simp [CategoryStruct.comp, CategoryStruct.id, SetWithEndomapHom.comp,
        SetWithEndomapHom.id, f₃', g₃', f₃, g₃]

example : List.Pairwise (· ≠ ·) [f₁, f₂, f₃] := by
  simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil,
    and_self, and_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
    intro h <;> exact absurd (congrFun h X.a) (by simp [f₁, f₂, f₃])

example : ∀ f : Xα ⟶ Yβ, IsIso f → f = f₁' ∨ f = f₂' ∨ f = f₃' := by
  rintro ⟨g, h⟩ _
  have h₁ := congr_fun h X.a
  have h₂ := congr_fun h X.b
  have h₃ := congr_fun h X.c
  simp only [Xα, Yβ, α, β, types_comp_apply] at h₁ h₂ h₃
  rcases hx : g X.a with _ | _ | _ <;>
    simp only [hx] at h₁ <;> simp only [h₁] at h₂
  · exact Or.inl (Subtype.ext (funext fun x => by
      cases x <;> simp [f₁', f₁, hx, h₁, h₂]))
  · exact Or.inr (Or.inl (Subtype.ext (funext fun x => by
      cases x <;> simp [f₂', f₂, hx, h₁, h₂])))
  · exact Or.inr (Or.inr (Subtype.ext (funext fun x => by
      cases x <;> simp [f₃', f₃, hx, h₁, h₂])))

end Ex11_2

/-!
Exercise 11.3 (p. 159)
-/
namespace Ex11_3

inductive X
  | x₁ | x₂ | x₃ | x₄

def α : X ⟶ X -- x2, x3, x4 form a 3-cycle and x1 points x2
  | X.x₁ => X.x₂
  | X.x₂ => X.x₃
  | X.x₃ => X.x₄
  | X.x₄ => X.x₂

def Xα : SetWithEndomap := {
  carrier := X
  toEnd := α
}

inductive Y
  | y₁ | y₂ | y₃ | y₄

def β : Y ⟶ Y -- y1, y2, y3, y4 form a 4-cycle
  | Y.y₁ => Y.y₂
  | Y.y₂ => Y.y₃
  | Y.y₃ => Y.y₄
  | Y.y₄ => Y.y₁

def Yβ : SetWithEndomap := {
  carrier := Y
  toEnd := β
}

example : ¬(∃ f : Xα ⟶ Yβ, IsIso f) := by
  push Not
  intro h
  exfalso
  obtain ⟨f, hf⟩ := h
  have h₁ := congr_fun hf X.x₁
  have h₂ := congr_fun hf X.x₂
  have h₃ := congr_fun hf X.x₃
  have h₄ := congr_fun hf X.x₄
  simp only [Yβ, Xα, types_comp_apply, α, β] at h₁ h₂ h₃ h₄
  have : f X.x₁ = f X.x₂ := by grind -- rw h₁ into h₂, h₂ into h₃, etc
  rw [this] at h₁
  cases f X.x₂ <;> grind
end Ex11_3

/-!
Exercise 11.4 (p. 159)
-/
example {Aα Bβ : SetWithEndomap}
    (f : Aα ⟶ Bβ) (g : Bβ.carrier ⟶ Aα.carrier)
    (h : g ⊚ f.val = 𝟙 Aα.carrier ∧ f.val ⊚ g = 𝟙 Bβ.carrier)
    : ∃ finv : Bβ ⟶ Aα, finv.val = g := by
  refine ⟨⟨g, ?_⟩, rfl⟩
  obtain ⟨f, h1⟩ := f
  simp only at h
  have := congr_arg (g ⊚ ·) h1
  simp only [Category.assoc] at this
  rw [h.1] at this
  have := congr_arg (· ⊚ g) this
  simp only [Category.comp_id] at this
  rw [← Category.assoc, h.2] at this
  simp only [Category.id_comp] at this
  exact this.symm

/-!
Exercise 11.5 (p. 159)
-/
namespace Ex11_5

def α := (· + (2 : ℤ))
def β := (· + (3 : ℤ))

abbrev ℤα : SetWithEndomap := {
  carrier := ℤ
  toEnd := α
}

abbrev ℤβ : SetWithEndomap := {
  carrier := ℤ
  toEnd := β
}

example (f : ℤα ⟶ ℤβ) : ¬(IsIso f) := by
  intro h
  obtain ⟨f, hf, hf'⟩ := h
  obtain ⟨f', h⟩ := f
  -- f (n + 3) = f n + 2
  -- f 0, f 1, f 2 determine all values
  -- two of then will have same parity
  -- if they are same parity eventually they collide
  -- f is not injective, so can't be bijection.
  -- Work with the inverse's underlying function as a plain map g : ℤ → ℤ.
  set g : ℤ → ℤ := f' with hgdef
  -- g satisfies g (m + 3) = g m + 2 …
  have hstep : ∀ m : ℤ, g (m + 3) = g m + 2 := by
    intro m
    have := congr_fun h m
    simp only [ℤβ, ℤα, α, β, types_comp_apply] at this
    exact this
  -- … and f ∘ g = id, so g is injective.
  have ha : ∀ m : ℤ, f (g m) = m := by
    intro m
    have := congrFun (congrArg Subtype.val hf') m
    simpa [ℤβ, types_comp_apply] using this
  have hinj : Function.Injective g := by
    intro a b hab
    have h2 : f (g a) = f (g b) := by rw [hab]
    rw [ha, ha] at h2
    exact h2
  -- Iterating the recurrence: g (r + 3 k) = g r + 2 k for every integer k.
  have hgen : ∀ (r : ℤ) (k : ℤ), g (r + 3 * k) = g r + 2 * k := by
    intro r k
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
        have hg : r + 3 * ((n : ℤ) + 1) = (r + 3 * (n : ℤ)) + 3 := by ring
        rw [hg, hstep, ih]; ring
    | pred n ih =>
        have h2 := hstep (r + 3 * (-(n : ℤ) - 1))
        have hg : r + 3 * (-(n : ℤ) - 1) + 3 = r + 3 * (-(n : ℤ)) := by ring
        rw [hg] at h2
        rw [ih] at h2
        omega
  -- If two base values share parity, their residues are ≡ mod 3.
  have key : ∀ i j : ℤ, Even (g i - g j) → (3 : ℤ) ∣ (i - j) := by
    intro i j he
    obtain ⟨t, ht⟩ := he
    have hval : g (j + 3 * t) = g i := by rw [hgen]; omega
    have := hinj hval
    exact ⟨t, by omega⟩
  -- Among g 0, g 1, g 2 two share parity, but 3 ∤ (i - j) for i ≠ j in {0,1,2}.
  rcases Int.even_or_odd (g 0) with e0 | o0 <;>
    rcases Int.even_or_odd (g 1) with e1 | o1 <;>
      rcases Int.even_or_odd (g 2) with e2 | o2
  · exact absurd (key 0 1 (e0.sub e1)) (by omega)
  · exact absurd (key 0 1 (e0.sub e1)) (by omega)
  · exact absurd (key 0 2 (e0.sub e2)) (by omega)
  · exact absurd (key 1 2 (o1.sub_odd o2)) (by omega)
  · exact absurd (key 1 2 (e1.sub e2)) (by omega)
  · exact absurd (key 0 2 (o0.sub_odd o2)) (by omega)
  · exact absurd (key 0 1 (o0.sub_odd o1)) (by omega)
  · exact absurd (key 0 1 (o0.sub_odd o1)) (by omega)

end Ex11_5

/-!
Exercise 11.6 (p. 159)
-/
namespace Ex11_6

inductive A
  | a₁ | a₂ | a₃

inductive D
  | d₁ | d₂ | d₃

def graph_a : IrreflexiveGraph := {
  A := A
  D := D
  toSrc := fun
    | A.a₁ => D.d₂
    | A.a₂ => D.d₁
    | A.a₃ => D.d₃
  toTgt := fun
    | A.a₁ => D.d₃
    | A.a₂ => D.d₂
    | A.a₃ => D.d₂
}

def graph_b : IrreflexiveGraph := {
  A := A
  D := D
  toSrc := fun
    | A.a₁ => D.d₁
    | A.a₂ => D.d₂
    | A.a₃ => D.d₂,
  toTgt := fun
    | A.a₁ => D.d₂
    | A.a₂ => D.d₃
    | A.a₃ => D.d₁
}

def graph_c : IrreflexiveGraph := {
  A := A
  D := D
  toSrc := fun
    | A.a₁ => D.d₁
    | A.a₂ => D.d₁
    | A.a₃ => D.d₁
  toTgt := fun
    | A.a₁ => D.d₃
    | A.a₂ => D.d₂
    | A.a₃ => D.d₃
}

def graph_d : IrreflexiveGraph := {
  A := A
  D := D
  toSrc := fun
    | A.a₁ => D.d₃
    | A.a₂ => D.d₁
    | A.a₃ => D.d₂
  toTgt := fun
    | A.a₁ => D.d₂
    | A.a₂ => D.d₂
    | A.a₃ => D.d₃
}

def graph_e : IrreflexiveGraph := {
  A := A
  D := D
  toSrc := fun
    | A.a₁ => D.d₁
    | A.a₂ => D.d₁
    | A.a₃ => D.d₃
  toTgt := fun
    | A.a₁ => D.d₃
    | A.a₂ => D.d₂
    | A.a₃ => D.d₁
}

def graph_f : IrreflexiveGraph := {
  A := A
  D := D
  toSrc := fun
    | A.a₁ => D.d₁
    | A.a₂ => D.d₁
    | A.a₃ => D.d₁
  toTgt := fun
    | A.a₁ => D.d₂
    | A.a₂ => D.d₃
    | A.a₃ => D.d₃
}

def f₁ : graph_a ⟶ graph_d := ⟨
  ⟨fun
    | A.a₁ => A.a₃
    | A.a₂ => A.a₂
    | A.a₃ => A.a₁
  , id⟩, by
    constructor
    · ext x
      simp [graph_a, graph_d]
      cases x <;> simp
    · ext x
      simp [graph_a, graph_d]
      cases x <;> simp
⟩


def finv₁ : graph_d ⟶ graph_a := ⟨
  ⟨fun
    | A.a₁ => A.a₃
    | A.a₂ => A.a₂
    | A.a₃ => A.a₁
  , id⟩, by
  constructor
  · ext x
    simp [graph_a, graph_d]
    cases x <;> simp
  · ext x
    simp [graph_a, graph_d]
    cases x <;> simp
⟩

example : graph_a ≅ graph_d := by
  use f₁, finv₁
  all_goals (ext x <;> cases x <;> rfl)


def f₂ : graph_b ⟶ graph_e := ⟨
  ⟨fun
    | A.a₁ => A.a₃
    | A.a₂ => A.a₂
    | A.a₃ => A.a₁,
  fun
    | D.d₁ => D.d₃
    | D.d₂ => D.d₁
    | D.d₃ => D.d₂⟩, by
  constructor
  · ext x
    simp [graph_b, graph_e]
    cases x <;> simp
  · ext x
    simp [graph_b, graph_e]
    cases x <;> simp
⟩

def finv₂ : graph_e ⟶ graph_b := ⟨
  ⟨fun
    | A.a₁ => A.a₃
    | A.a₂ => A.a₂
    | A.a₃ => A.a₁,
  fun
    | D.d₁ => D.d₂
    | D.d₂ => D.d₃
    | D.d₃ => D.d₁⟩, by
  constructor
  · ext x
    simp [graph_b, graph_e]
    cases x <;> simp
  · ext x
    simp [graph_b, graph_e]
    cases x <;> simp
⟩

example : graph_b ≅ graph_e := by
  use f₂, finv₂
  all_goals (ext x <;> cases x <;> rfl)

def f₃ : graph_c ⟶ graph_f :=
  ⟨⟨fun
    | A.a₁ => A.a₂
    | A.a₂ => A.a₁
    | A.a₃ => A.a₃, id⟩, by
  constructor
  · ext x
    simp [graph_c, graph_f]
    cases x <;> simp
  · ext x
    simp [graph_c, graph_f]
    cases x <;> simp
⟩

def finv₃ : graph_f ⟶ graph_c :=
  ⟨⟨fun
    | A.a₁ => A.a₂
    | A.a₂ => A.a₁
    | A.a₃ => A.a₃, id⟩, by
  constructor
  · ext x
    simp [graph_c, graph_f]
    cases x <;> simp
  · ext x
    simp [graph_c, graph_f]
    cases x <;> simp
⟩

example : graph_c ≅ graph_f := by
  use f₃, finv₃
  all_goals (ext x <;> cases x <;> rfl)

end Ex11_6

/-!
Exercise 11.7 (p. 160)
-/
namespace Ex11_7

inductive A
  | a₁ | a₂ | a₃ | a₄ | a₅ | a₆

inductive D
  | d₁ | d₂ | d₃ | d₄ | d₅

def graph_L : IrreflexiveGraph := {
  A := A
  D := D
  toSrc := fun
    | A.a₁ => D.d₁
    | A.a₂ => D.d₂
    | A.a₃ => D.d₃
    | A.a₄ => D.d₄
    | A.a₅ => D.d₁
    | A.a₆ => D.d₅
  toTgt := fun
    | A.a₁ => D.d₂
    | A.a₂ => D.d₃
    | A.a₃ => D.d₄
    | A.a₄ => D.d₁
    | A.a₅ => D.d₅
    | A.a₆ => D.d₃
}

def graph_R : IrreflexiveGraph := {
  A := A
  D := D
  toSrc := fun
    | A.a₁ => D.d₂
    | A.a₂ => D.d₃
    | A.a₃ => D.d₃
    | A.a₄ => D.d₄
    | A.a₅ => D.d₁
    | A.a₆ => D.d₅
  toTgt := fun
    | A.a₁ => D.d₁
    | A.a₂ => D.d₂
    | A.a₃ => D.d₄
    | A.a₄ => D.d₁
    | A.a₅ => D.d₅
    | A.a₆ => D.d₃
}

def f : graph_L ⟶ graph_R := ⟨⟨
  fun
    | A.a₁ => A.a₂
    | A.a₂ => A.a₁
    | A.a₃ => A.a₅
    | A.a₄ => A.a₆
    | A.a₅ => A.a₃
    | A.a₆ => A.a₄,
  fun
    | D.d₁ => D.d₃
    | D.d₂ => D.d₂
    | D.d₃ => D.d₁
    | D.d₄ => D.d₅
    | D.d₅ => D.d₄⟩, by
    constructor
    · ext x
      simp [graph_R, graph_L]
      cases x <;> simp
    · ext x
      simp [graph_R, graph_L]
      cases x <;> simp
⟩

def finv : graph_R ⟶ graph_L :=  ⟨⟨
  fun
    | A.a₁ => A.a₂
    | A.a₂ => A.a₁
    | A.a₃ => A.a₅
    | A.a₄ => A.a₆
    | A.a₅ => A.a₃
    | A.a₆ => A.a₄,
  fun
    | D.d₁ => D.d₃
    | D.d₂ => D.d₂
    | D.d₃ => D.d₁
    | D.d₄ => D.d₅
    | D.d₅ => D.d₄⟩, by
    constructor
    · ext x
      simp [graph_R, graph_L]
      cases x <;> simp
    · ext x
      simp [graph_R, graph_L]
      cases x <;> simp
⟩

example : graph_L ≅ graph_R := by
  use f, finv
  all_goals (ext x <;> cases x <;> rfl)

end Ex11_7

/-!
Exercise 11.8 (p. 160)
-/
namespace Ex11_8

inductive A
  | a₁ | a₂ | a₃

abbrev D := Fin 2

def J : IrreflexiveGraph := {
  A := A
  D := D
  toSrc := fun
    | A.a₁ => 0
    | A.a₂ => 1
    | A.a₃ => 1
  toTgt := fun
    | A.a₁ => 0
    | A.a₂ => 0
    | A.a₃ => 1
}

/-- There is an edge in `G` from dot `v` to dot `w`. -/
def hasEdge (G : IrreflexiveGraph) (v w : G.D) : Prop :=
  ∃ a : G.A, G.toSrc a = v ∧ G.toTgt a = w

/-- There is a path in `G` from `v` to `w`: a finite (possibly empty)
sequence of edges laid end to end. -/
inductive hasPath (G : IrreflexiveGraph) : G.D → G.D → Prop
  | refl (v : G.D) : hasPath G v v
  | tail {u v w : G.D} (p : hasPath G u v) (e : hasEdge G v w) : hasPath G u w

/-- (a) If there is a map of graphs `f : G ⟶ J` with `f b = 0` and `f e = 1`,
then there is no path in `G` that begins at `b` and ends at `e`. -/
-- A graph map sends edges to edges (the two commuting squares).
theorem edgePres {G : IrreflexiveGraph} (f : G ⟶ J) {v w : G.D}
    (h : hasEdge G v w) : hasEdge J (f.val.2 v) (f.val.2 w) := by
  obtain ⟨a, hs, ht⟩ := h
  refine ⟨f.val.1 a, ?_, ?_⟩
  · have h1 := congr_fun f.property.1 a
    simp only [types_comp_apply] at h1
    rw [← hs]; exact h1.symm
  · have h2 := congr_fun f.property.2 a
    simp only [types_comp_apply] at h2
    rw [← ht]; exact h2.symm

-- In `J`, every edge out of `0` lands back on `0`.
theorem Jtgt {w : J.D} (h : hasEdge J (0 : Fin 2) w) : w = (0 : Fin 2) := by
  obtain ⟨a, hs, ht⟩ := h
  cases a <;> simp_all [J]

theorem noPath {G : IrreflexiveGraph} (b e : G.D) (f : G ⟶ J)
    (hb : f.val.2 b = (0 : Fin 2)) (he : f.val.2 e = (1 : Fin 2))
    (h : hasPath G b e) : False := by
  -- Induction on the path (≈ on its length): a path from a `0`-vertex ends
  -- at a `0`-vertex. `induction` builds the motive that structural recursion
  -- couldn't, generalizing the moving endpoint `y`.
  have key : ∀ {x y : G.D}, hasPath G x y →
      f.val.2 x = (0 : Fin 2) → f.val.2 y = (0 : Fin 2) := by
    intro x y hxy
    induction hxy with
    | refl => exact id
    | tail p edge ih =>
        intro h0
        have hedge := edgePres f edge
        rw [ih h0] at hedge
        exact Jtgt hedge
  exact Fin.zero_ne_one ((key h hb).symm.trans he)

/-- (b) Conversely, if there is no path in `G` that begins at `b` and ends at
`e`, then there is a map of graphs `f : G ⟶ J` with `f b = 0` and `f e = 1`. -/
example {G : IrreflexiveGraph} (b e : G.D) (h : ¬ hasPath G b e) :
    ∃ f : G ⟶ J, f.val.2 b = (0 : Fin 2) ∧ f.val.2 e = (1 : Fin 2) := by
  -- build f as follows, every D reachable from b maps 0, everything else maps to 1
  -- edges maps naturally, 0 -> 0 is 0cycle, 1-1 1 cycle, 1->0
  -- finally show that no path is equivalent of not needing 0->1
  classical
  refine ⟨⟨(fun a => if hasPath G b (G.toSrc a) then A.a₁
                     else if hasPath G b (G.toTgt a) then A.a₂ else A.a₃,
            fun v => if hasPath G b v then (0 : Fin 2) else (1 : Fin 2)), ?_, ?_⟩, ?_, ?_⟩
  · -- source square commutes (holds in every case: `src` reachable ⟹ image `0`)
    funext a
    simp only [types_comp_apply]
    by_cases hu : hasPath G b (G.toSrc a) <;>
      by_cases hw : hasPath G b (G.toTgt a) <;> simp [hu, hw, J]
  · -- target square commutes
    funext a
    simp only [types_comp_apply]
    by_cases hu : hasPath G b (G.toSrc a)
    · -- if the source is reachable, so is the target (extend the path by this edge)
      have hw : hasPath G b (G.toTgt a) := hu.tail ⟨a, rfl, rfl⟩
      simp [hu, hw, J]
    · by_cases hw : hasPath G b (G.toTgt a) <;> simp [hu, hw, J]
  · -- f b = 0, since b is reachable from itself
    exact if_pos (hasPath.refl b)
  · -- f e = 1, since e is not reachable from b
    exact if_neg h

end Ex11_8

end CM

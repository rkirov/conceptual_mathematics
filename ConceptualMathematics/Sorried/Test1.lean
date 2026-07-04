import ConceptualMathematics.Sorried.Article2
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Problem Test 1.1 (p. 119)
-/
namespace Test1_1

inductive A
  | Mara | Aurelio | Andrea
  deriving Fintype

def f : A ⟶ A
  | A.Mara => A.Mara
  | A.Aurelio => A.Andrea
  | A.Andrea => A.Aurelio

def finv : A ⟶ A := f

example : IsIso f := ⟨finv,
  by
    funext x
    fin_cases x <;> simp [f, finv]
  , by
    funext x
    fin_cases x <;> simp [f, finv]
⟩

def e : A ⟶ A
  | A.Mara => A.Mara
  | A.Aurelio => A.Mara
  | A.Andrea => A.Mara

instance : IsIdempotent e := by
  constructor
  funext x
  fin_cases x <;> simp [e]

inductive B
  | b
  deriving Fintype

def r : A ⟶ B
  | A.Mara => B.b
  | A.Aurelio => B.b
  | A.Andrea => B.b

def s : B ⟶ A
  | B.b => A.Mara
example : r ⊚ s = 𝟙 B ∧ s ⊚ r = e := by
  constructor
  · funext x; fin_cases x; simp [r, s]
  · funext x; fin_cases x <;> simp [s, e]

end Test1_1

/-!
Problem Test 1.2 (p. 119)
-/
example (f : ℝ ⟶ ℝ) (hf : ∀ x : ℝ, f x = 4 * x - 7)
    : IsIso f := ⟨
    fun x => (x + 7) / 4
    , by
      funext x
      simp [hf]
    , by
      funext x
      simp [hf]
      field_simp [hf]
      ring
    ⟩

end CM

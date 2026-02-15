import ConceptualMathematics.Article3
import Mathlib
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise 12.1 (p. 161)
-/
example {Xα Yβ : SetWithEndomap} (f : Xα ⟶ Yβ)
    {x x' : Xα.carrier} {y y' : Yβ.carrier}
    (hx' : x' = (Xα.toEnd ⊚ Xα.toEnd ⊚ Xα.toEnd) x)
    (hy : y = f.val x)
    (hy' : y' = (Yβ.toEnd ⊚ Yβ.toEnd ⊚ Yβ.toEnd) y)
    : f.val x' = y' := by
  have hf_comm := f.property
  rw [hy', hy]
  rw [← types_comp_apply f.val (Yβ.toEnd ⊚ Yβ.toEnd ⊚ Yβ.toEnd)]
  rw [← Category.assoc, ← Category.assoc]
  rw [← hf_comm]
  rw [Category.assoc Xα.toEnd]
  rw [← hf_comm]
  rw [Category.assoc, Category.assoc]
  rw [← hf_comm]
  rw [← Category.assoc, ← Category.assoc]
  rw [types_comp_apply]
  rw [hx']

/-!
Exercise 12.2 (p. 162)
-/
namespace Ex12_2

inductive BulbState
  | off₀ | on₁ | off₁ | on₂ | off₂ | on₃ | off₃ | on₄ | burntOut
  deriving Fintype, DecidableEq

open BulbState

def pressButton : BulbState ⟶ BulbState
  | off₀ => on₁ -- lit 1st time
  | on₁  => off₁
  | off₁ => on₂ -- lit 2nd time
  | on₂  => off₂
  | off₂ => on₃ -- lit 3rd time
  | on₃  => off₃
  | off₃ => on₄ -- lit 4th time
  | on₄  => burntOut
  | burntOut => burntOut

abbrev LitCount := Nat

def LitStates : List BulbState := [on₁, on₂, on₃, on₄]

def pressAndCount (this : BulbState) : StateM LitCount BulbState := do
  let next := pressButton this
  if next ∈ LitStates then
    modify (· + 1)
  return next

def EightPresses : List Unit := List.replicate 8 ()

def simulateEightPresses : StateM LitCount BulbState :=
  EightPresses.foldlM (fun s _ ↦ pressAndCount s) off₀

def getResult : BulbState × LitCount := simulateEightPresses.run 0

example : getResult = (burntOut, 4) := rfl

example : Function.IsFixedPt pressButton burntOut := rfl

end Ex12_2

/-!
The category 𝑺↻↻ in which an object is a set with a specified pair of endomaps (p. 162)
-/
structure SetWithTwoEndomaps extends SetWithEndomap where
  toEnd2 : carrier ⟶ carrier

instance instCatSetWithTwoEndomaps : Category SetWithTwoEndomaps where
  Hom X Y := {
    f : X.carrier ⟶ Y.carrier //
        f ⊚ X.toEnd = Y.toEnd ⊚ f -- first endomap commutes
        ∧ f ⊚ X.toEnd2 = Y.toEnd2 ⊚ f -- second endomap commutes
  }
  id X := ⟨𝟙 X.carrier, ⟨rfl, rfl⟩⟩
  comp := by
    rintro _ _ _ ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨
      g ⊚ f,
      by
        obtain ⟨hf_comm, hf2_comm⟩ := hf
        obtain ⟨hg_comm, hg2_comm⟩ := hg
        constructor
        · rw [← Category.assoc, hf_comm, Category.assoc, hg_comm,
            ← Category.assoc]
        · rw [← Category.assoc, hf2_comm, Category.assoc, hg2_comm,
            ← Category.assoc]
    ⟩

/-!
Exercise 12.3 (p. 163)
-/
namespace Ex12_3

inductive Gender
  | female | male

def m₁ : Gender ⟶ Gender := fun _ ↦ Gender.female

def f₁ : Gender ⟶ Gender := fun _ ↦ Gender.male

def G : SetWithTwoEndomaps := {
  carrier := Gender
  toEnd := m₁
  toEnd2 := f₁
}

inductive Clan
  | wolf | bear

def m₂ : Clan ⟶ Clan := fun c ↦ c

def f₂ : Clan ⟶ Clan
  | Clan.wolf => Clan.bear
  | Clan.bear => Clan.wolf

def C : SetWithTwoEndomaps := {
  carrier := Clan
  toEnd := m₂
  toEnd2 := f₂
}

inductive ParentType
  | isMother | isFather

structure Person₁ where
  parentType : ParentType

def mother₁ : Person₁ ⟶ Person₁ := fun _ ↦ ⟨ParentType.isMother⟩

def father₁ : Person₁ ⟶ Person₁ := fun _ ↦ ⟨ParentType.isFather⟩

def P₁ : SetWithTwoEndomaps := {
  carrier := Person₁
  toEnd := mother₁
  toEnd2 := father₁
}

def gender : P₁.carrier ⟶ G.carrier
  | ⟨ParentType.isMother⟩ => Gender.female
  | ⟨ParentType.isFather⟩ => Gender.male

def gender' : P₁ ⟶ G := ⟨
  gender,
  by
    constructor <;> rfl
⟩

example : gender ⊚ mother₁ = m₁ ⊚ gender := rfl

example : gender ⊚ father₁ = f₁ ⊚ gender := rfl

inductive ParentClan
  | isWolf | isBear

structure Person₂ where
  parentClan : ParentClan

def mother₂ : Person₂ ⟶ Person₂ := fun p ↦ ⟨p.parentClan⟩

def father₂ : Person₂ ⟶ Person₂
  | ⟨ParentClan.isWolf⟩ => ⟨ParentClan.isBear⟩
  | ⟨ParentClan.isBear⟩ => ⟨ParentClan.isWolf⟩

def P₂ : SetWithTwoEndomaps := {
  carrier := Person₂
  toEnd := mother₂
  toEnd2 := father₂
}

def clan : P₂.carrier ⟶ C.carrier
  | ⟨ParentClan.isWolf⟩ => Clan.wolf
  | ⟨ParentClan.isBear⟩ => Clan.bear

def clan' : P₂ ⟶ C := ⟨
  clan,
  by
    constructor
    all_goals
      funext p
      match p with
      | ⟨ParentClan.isWolf⟩ => rfl
      | ⟨ParentClan.isBear⟩ => rfl
⟩

structure Person₃ where
  parentType : ParentType
  parentClan : ParentClan

def mother₃ : Person₃ ⟶ Person₃ :=
  fun p ↦ ⟨ParentType.isMother, p.parentClan⟩

def father₃ : Person₃ ⟶ Person₃
  | ⟨_, ParentClan.isWolf⟩ => ⟨ParentType.isFather, ParentClan.isBear⟩
  | ⟨_, ParentClan.isBear⟩ => ⟨ParentType.isFather, ParentClan.isWolf⟩

def P₃ : SetWithTwoEndomaps := {
  carrier := Person₃
  toEnd := mother₃
  toEnd2 := father₃
}

def m₃ : (Gender × Clan) ⟶ (Gender × Clan) :=
  fun (_, c) ↦ (Gender.female, c)

def f₃ : (Gender × Clan) ⟶ (Gender × Clan)
  | (_, Clan.wolf) => (Gender.male, Clan.bear)
  | (_, Clan.bear) => (Gender.male, Clan.wolf)

def GC : SetWithTwoEndomaps := {
  carrier := Gender × Clan
  toEnd := m₃
  toEnd2 := f₃
}

def gender_and_clan : P₃.carrier ⟶ GC.carrier
  | ⟨ParentType.isMother, ParentClan.isWolf⟩ =>
        ⟨Gender.female, Clan.wolf⟩
  | ⟨ParentType.isMother, ParentClan.isBear⟩ =>
        ⟨Gender.female, Clan.bear⟩
  | ⟨ParentType.isFather, ParentClan.isWolf⟩ =>
        ⟨Gender.male, Clan.wolf⟩
  | ⟨ParentType.isFather, ParentClan.isBear⟩ =>
        ⟨Gender.male, Clan.bear⟩

def gender_and_clan' : P₃ ⟶ GC := ⟨
  gender_and_clan,
  by
    constructor
    all_goals
      funext p
      match p with
      | ⟨ParentType.isMother, ParentClan.isWolf⟩ => rfl
      | ⟨ParentType.isMother, ParentClan.isBear⟩ => rfl
      | ⟨ParentType.isFather, ParentClan.isWolf⟩ => rfl
      | ⟨ParentType.isFather, ParentClan.isBear⟩ => rfl
⟩

end Ex12_3

end CM


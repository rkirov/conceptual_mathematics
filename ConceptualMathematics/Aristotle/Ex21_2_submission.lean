import Mathlib

open CategoryTheory

local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

structure SetWithEndomap where
  carrier : Type
  toEnd : carrier ⟶ carrier

def SetWithEndomapHom (X Y : SetWithEndomap) := {
  f : X.carrier ⟶ Y.carrier //
      f ⊚ X.toEnd = Y.toEnd ⊚ f -- commutes
}

def SetWithEndomapHom.id (X : SetWithEndomap)
    : SetWithEndomapHom X X := ⟨𝟙 X.carrier, rfl⟩

def SetWithEndomapHom.comp {X Y Z : SetWithEndomap}
    (f : SetWithEndomapHom X Y) (g : SetWithEndomapHom Y Z)
    : SetWithEndomapHom X Z := ⟨
  g.val ⊚ f.val,
  by
    have hf_comm := f.property
    have hg_comm := g.property
    rw [← Category.assoc, hf_comm, Category.assoc, hg_comm,
        ← Category.assoc]
⟩

instance instCatSetWithEndomap : Category SetWithEndomap where
  Hom := SetWithEndomapHom
  id := SetWithEndomapHom.id
  comp := SetWithEndomapHom.comp

instance {X Y : SetWithEndomap}
    : FunLike (instCatSetWithEndomap.Hom X Y) X.carrier
                                              Y.carrier where
  coe f := f.val
  coe_injective' := fun _ _ h ↦ Subtype.ext h

instance
    : ConcreteCategory SetWithEndomap instCatSetWithEndomap.Hom where
  hom f := f
  ofHom f := f

def KCycleProd (m n : ℕ) [NeZero m] [NeZero n] : SetWithEndomap where
  carrier := ZMod m × ZMod n
  toEnd := fun (x, y) ↦ (x + 1, y + 1)

def KCycleDecomp (m n : ℕ) [NeZero m] [NeZero n] [NeZero (m.lcm n)] : SetWithEndomap where
  carrier := Fin (m.gcd n) × ZMod (m.lcm n)
  toEnd := fun (i, z) ↦ (i, z + 1)

example (m n : ℕ) [NeZero m] [NeZero n] [NeZero (m.lcm n)] : Nonempty (KCycleProd m n ≅ KCycleDecomp m n) := by
  sorry

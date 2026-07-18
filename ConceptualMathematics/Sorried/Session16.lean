import ConceptualMathematics.Sorried.Session12
import Mathlib.CategoryTheory.Equivalence
open CategoryTheory
namespace CM
local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

/-!
Exercise 16.1 (p. 195)

The slice category `C/G`.  For a fixed object `G` of a category `C`, an object
of `C/G` is an object `X` of `C` equipped with a "sorting" map `X ⟶ G`, and a
map of `C/G` is a map of `C` making the sorting triangle commute:

      h
   X ───▶ Y
    ╲     ╱
   f ╲   ╱ g          g ⊚ h = f
      ▼ ▼
       G

(For example, the kinship category of Session 12 is `𝒮/G` — sets equipped with
father/mother endomaps, sorted into the object `G` of genders.)
-/
variable {C : Type*} [Category C]

/-- An object of the slice category `C/G`: an object of `C` with a sorting map to `G`. -/
structure Slice (G : C) where
  obj : C
  sorting : obj ⟶ G

/-- A map of `C/G`: a map of `C` whose sorting triangle commutes. -/
@[ext]
structure SliceHom {G : C} (X Y : Slice G) where
  hom : X.obj ⟶ Y.obj
  w : Y.sorting ⊚ hom = X.sorting

instance instCategorySlice (G : C) : Category (Slice G) where
  Hom X Y := SliceHom X Y
  id X := ⟨𝟙 X.obj, by simp⟩
  comp f g := ⟨g.hom ⊚ f.hom, by rw [Category.assoc, g.w, f.w]⟩
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

/-- The forgetful functor `C/G ⟶ C` sending `(X, X ⟶ G)` to `X`. -/
def Slice.forget (G : C) : Slice G ⥤ C where
  obj X := X.obj
  map f := f.hom

/-!
### Exercise 16.1, worked out

The two descriptions of the kinship category are the "same" (equivalent).

* **Description A** (`𝒮/G`): the slice `Slice G` of `SetWithTwoEndomaps`
  (Session 12) over the object `G` of genders.  An object is a set with
  `mother`/`father` endomaps and a gender map, which commutativity forces to
  send every mother to a female and every father to a male.
* **Description B**: `ParentLike` (Article III, Ex. 17) — two sets `M` (males)
  and `F` (females) with four structural maps `φ, φ', μ, μ'`
  (father-of-male, father-of-female, mother-of-female, mother-of-male).

The gender map partitions the people into the fibers `M` and `F`, and
mother (`toEnd`) / father (`toEnd2`) restrict to the four structural maps;
conversely `M ⊕ F` reassembles a person set.  This is an equivalence.
-/
open Ex12_3 ExIII_17

/-- **A ⟶ B.**  Split the people by gender into male/female fibers; father
(`toEnd2`) and mother (`toEnd`) restrict to the four structural maps. -/
def toParentLike : Slice G ⥤ ParentLike where
  obj S :=
    { M := {x : S.obj.carrier // S.sorting.1 x = Gender.male}
      F := {x : S.obj.carrier // S.sorting.1 x = Gender.female}
      φ := fun m => ⟨S.obj.toEnd2 m.1, by
        simpa [types_comp_apply, G, f₁] using congr_fun S.sorting.2.2 m.1⟩
      φ' := fun f => ⟨S.obj.toEnd2 f.1, by
        simpa [types_comp_apply, G, f₁] using congr_fun S.sorting.2.2 f.1⟩
      μ := fun f => ⟨S.obj.toEnd f.1, by
        simpa [types_comp_apply, G, m₁] using congr_fun S.sorting.2.1 f.1⟩
      μ' := fun m => ⟨S.obj.toEnd m.1, by
        simpa [types_comp_apply, G, m₁] using congr_fun S.sorting.2.1 m.1⟩ }
  map {S S'} φ := by
    have gp : ∀ z, S'.sorting.1 (φ.hom.1 z) = S.sorting.1 z := fun z => by
      simpa [types_comp_apply] using congr_fun (congrArg Subtype.val φ.w) z
    refine ⟨(fun x => ⟨φ.hom.1 x.1, (gp x.1).trans x.2⟩,
             fun x => ⟨φ.hom.1 x.1, (gp x.1).trans x.2⟩), ?_, ?_, ?_, ?_⟩
    · funext m; apply Subtype.ext; simpa [types_comp_apply] using congr_fun φ.hom.2.2 m.1
    · funext f; apply Subtype.ext; simpa [types_comp_apply] using congr_fun φ.hom.2.2 f.1
    · funext f; apply Subtype.ext; simpa [types_comp_apply] using congr_fun φ.hom.2.1 f.1
    · funext m; apply Subtype.ext; simpa [types_comp_apply] using congr_fun φ.hom.2.1 m.1
  map_id S := rfl
  map_comp φ ψ := rfl

/-- **B ⟶ A.**  Reassemble a person set as `M ⊕ F`; mother (`toEnd`) and father
(`toEnd2`) are built from the four structural maps, and the gender map reads off
the `inl`/`inr` tag. -/
def ofParentLike : ParentLike ⥤ Slice G where
  obj T :=
    { obj :=
        { carrier := T.M ⊕ T.F
          toEnd := Sum.elim (fun m => Sum.inr (T.μ' m)) (fun f => Sum.inr (T.μ f))
          toEnd2 := Sum.elim (fun m => Sum.inl (T.φ m)) (fun f => Sum.inl (T.φ' f)) }
      sorting := ⟨Sum.elim (fun _ => Gender.male) (fun _ => Gender.female),
        ⟨by funext x; cases x <;> rfl, by funext x; cases x <;> rfl⟩⟩ }
  map {T T'} ψ :=
    { hom := ⟨Sum.map ψ.1.1 ψ.1.2,
        ⟨by
          funext x
          cases x with
          | inl m => exact congrArg Sum.inr (by simpa [types_comp_apply] using congr_fun ψ.2.2.2.2 m)
          | inr f => exact congrArg Sum.inr (by simpa [types_comp_apply] using congr_fun ψ.2.2.2.1 f),
         by
          funext x
          cases x with
          | inl m => exact congrArg Sum.inl (by simpa [types_comp_apply] using congr_fun ψ.2.1 m)
          | inr f => exact congrArg Sum.inl (by simpa [types_comp_apply] using congr_fun ψ.2.2.1 f)⟩⟩
      w := by apply Subtype.ext; funext x; cases x <;> rfl }
  map_id T := by apply SliceHom.ext; apply Subtype.ext; funext x; cases x <;> rfl
  map_comp ψ ρ := by apply SliceHom.ext; apply Subtype.ext; funext x; cases x <;> rfl

/-- Read the underlying male out of a male-gendered element of `M ⊕ F`. -/
def fromMale (T : ParentLike) : (ofParentLike ⋙ toParentLike).obj T |>.M → T.M
  | ⟨.inl m, _⟩ => m
  | ⟨.inr _, h⟩ => nomatch h

/-- Read the underlying female out of a female-gendered element of `M ⊕ F`. -/
def fromFemale (T : ParentLike) : (ofParentLike ⋙ toParentLike).obj T |>.F → T.F
  | ⟨.inr f, _⟩ => f
  | ⟨.inl _, h⟩ => nomatch h

/-- **Counit component.**  Splitting `M ⊕ F` by gender and reading off the two
fibers recovers `M` and `F`: `toParentLike (ofParentLike T) ≅ T`. -/
def counitApp (T : ParentLike) : (ofParentLike ⋙ toParentLike).obj T ≅ T where
  hom := ⟨(fromMale T, fromFemale T),
    by refine ⟨?_, ?_, ?_, ?_⟩ <;>
      (funext x; obtain ⟨x, hx⟩ := x; cases x <;> first | rfl | cases hx)⟩
  inv := ⟨(fun m => ⟨.inl m, rfl⟩, fun f => ⟨.inr f, rfl⟩),
    by refine ⟨?_, ?_, ?_, ?_⟩ <;> (funext x; rfl)⟩
  hom_inv_id := by
    apply Subtype.ext; apply Prod.ext <;>
      (funext x; obtain ⟨x, hx⟩ := x; cases x <;> first | rfl | cases hx)
  inv_hom_id := by apply Subtype.ext; apply Prod.ext <;> (funext x; rfl)

/-- Sort a person into their gender fibre. -/
def toSum (S : Slice G) (x : S.obj.carrier) :
    {y // S.sorting.1 y = Gender.male} ⊕ {y // S.sorting.1 y = Gender.female} :=
  match h : S.sorting.1 x with
  | Gender.male => Sum.inl ⟨x, h⟩
  | Gender.female => Sum.inr ⟨x, h⟩

@[simp] lemma toSum_val (S : Slice G) (x : S.obj.carrier) :
    Sum.elim Subtype.val Subtype.val (toSum S x) = x := by unfold toSum; split <;> rfl

lemma toSum_left (S : Slice G) {x : S.obj.carrier} (h : S.sorting.1 x = Gender.male) :
    toSum S x = Sum.inl ⟨x, h⟩ := by
  unfold toSum; split <;> first | rfl | (rename_i heq; exact Gender.noConfusion (h.symm.trans heq))

lemma toSum_right (S : Slice G) {x : S.obj.carrier} (h : S.sorting.1 x = Gender.female) :
    toSum S x = Sum.inr ⟨x, h⟩ := by
  unfold toSum; split <;> first | rfl | (rename_i heq; exact Gender.noConfusion (h.symm.trans heq))

/-- Every person is male or female. -/
lemma gender_cases (S : Slice G) (x : S.obj.carrier) :
    S.sorting.1 x = Gender.male ∨ S.sorting.1 x = Gender.female := by
  cases S.sorting.1 x <;> simp

/-- **Unit component.**  Sorting a person set by gender and reassembling as
`M ⊕ F` recovers it: `S ≅ ofParentLike (toParentLike S)`. -/
def unitApp (S : Slice G) : S ≅ (toParentLike ⋙ ofParentLike).obj S where
  hom := by
    refine ⟨⟨toSum S, ?_, ?_⟩, ?_⟩
    · funext x
      have hmo : S.sorting.1 (S.obj.toEnd x) = Gender.female := by
        simpa [types_comp_apply, G, m₁] using congr_fun S.sorting.2.1 x
      rw [types_comp_apply, types_comp_apply, toSum_right S hmo]
      obtain hgx | hgx := gender_cases S x
      · rw [toSum_left S hgx]; rfl
      · rw [toSum_right S hgx]; rfl
    · funext x
      have hfa : S.sorting.1 (S.obj.toEnd2 x) = Gender.male := by
        simpa [types_comp_apply, G, f₁] using congr_fun S.sorting.2.2 x
      rw [types_comp_apply, types_comp_apply, toSum_left S hfa]
      obtain hgx | hgx := gender_cases S x
      · rw [toSum_left S hgx]; rfl
      · rw [toSum_right S hgx]; rfl
    · apply Subtype.ext; funext x
      change ((toParentLike ⋙ ofParentLike).obj S).sorting.1 (toSum S x) = S.sorting.1 x
      obtain hgx | hgx := gender_cases S x
      · rw [toSum_left S hgx]; exact hgx.symm
      · rw [toSum_right S hgx]; exact hgx.symm
  inv := by
    refine ⟨⟨Sum.elim Subtype.val Subtype.val, ?_, ?_⟩, ?_⟩
    · funext s; obtain ⟨x, hx⟩ | ⟨x, hx⟩ := s <;> rfl
    · funext s; obtain ⟨x, hx⟩ | ⟨x, hx⟩ := s <;> rfl
    · apply Subtype.ext; funext s
      obtain ⟨x, hx⟩ | ⟨x, hx⟩ := s <;> exact hx
  hom_inv_id := by
    apply SliceHom.ext; apply Subtype.ext; funext x; exact toSum_val S x
  inv_hom_id := by
    apply SliceHom.ext; apply Subtype.ext; funext s
    obtain ⟨x, hx⟩ | ⟨x, hx⟩ := s
    · exact toSum_left S hx
    · exact toSum_right S hx

/-- The unit natural isomorphism `𝟭 ≅ toParentLike ⋙ ofParentLike`. -/
def unitIso : 𝟭 (Slice G) ≅ toParentLike ⋙ ofParentLike :=
  NatIso.ofComponents unitApp <| by
    intro S S' φ
    have gp : ∀ z, S'.sorting.1 (φ.hom.1 z) = S.sorting.1 z := fun z => by
      simpa [types_comp_apply] using congr_fun (congrArg Subtype.val φ.w) z
    apply SliceHom.ext; apply Subtype.ext; funext x
    change toSum S' (φ.hom.1 x) =
      Sum.map (fun m : {y // S.sorting.1 y = Gender.male} => (⟨φ.hom.1 m.1, (gp m.1).trans m.2⟩ :
          {y // S'.sorting.1 y = Gender.male}))
        (fun f => ⟨φ.hom.1 f.1, (gp f.1).trans f.2⟩) (toSum S x)
    obtain hgx | hgx := gender_cases S x
    · rw [toSum_left S hgx, toSum_left S' ((gp x).trans hgx)]; rfl
    · rw [toSum_right S hgx, toSum_right S' ((gp x).trans hgx)]; rfl

/-- The counit natural isomorphism `ofParentLike ⋙ toParentLike ≅ 𝟭`. -/
def counitIso : ofParentLike ⋙ toParentLike ≅ 𝟭 ParentLike :=
  NatIso.ofComponents counitApp <| by
    intro T T' ψ
    apply Subtype.ext; apply Prod.ext <;>
      (funext x; obtain ⟨x, hx⟩ := x; cases x <;> first | rfl | cases hx)

/-- **Exercise 16.1.**  The two descriptions of the kinship category are the
same: the slice `𝒮/G` and the `ParentLike` category are equivalent. -/
def kinshipEquiv : Slice G ≌ ParentLike :=
  .mk toParentLike ofParentLike unitIso counitIso

end CM

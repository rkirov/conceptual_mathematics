/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 36f65369-362b-4767-9754-c7c67a67a5e7

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- example (m n : ℕ) [NeZero m] [NeZero n] [NeZero (m.lcm n)] : Nonempty (KCycleProd m n ≅ KCycleDecomp m n)

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Mathlib


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

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

noncomputable section AristotleLemmas

def inv_map (m n : ℕ) [NeZero m] [NeZero n] [NeZero (m.lcm n)] (p : Fin (m.gcd n) × ZMod (m.lcm n)) : ZMod m × ZMod n :=
  (p.2.val, (p.2.val : ZMod n) - (p.1.val : ZMod n))

def fwd_map (m n : ℕ) [NeZero m] [NeZero n] [NeZero (m.lcm n)] (p : ZMod m × ZMod n) : Fin (m.gcd n) × ZMod (m.lcm n) :=
  let g := m.gcd n
  haveI : NeZero g := ⟨Nat.gcd_ne_zero_left (NeZero.ne m)⟩
  let x := p.1
  let y := p.2
  let i : ZMod g := (x.val : ZMod g) - (y.val : ZMod g)
  let a := y.val + i.val
  let b := x.val
  let z_nat := Nat.chineseRemainder' (m := m) (n := n) (a := a) (b := b) (by
  rw [ Nat.gcd_comm, ← ZMod.natCast_eq_natCast_iff ] ; aesop;)
  (⟨i.val, i.val_lt⟩, (z_nat : ZMod (m.lcm n)))

lemma inv_comm (m n : ℕ) [NeZero m] [NeZero n] [NeZero (m.lcm n)] (p : Fin (m.gcd n) × ZMod (m.lcm n)) :
  inv_map m n (p.1, p.2 + 1) = (let r := inv_map m n p; (r.1 + 1, r.2 + 1)) := by
  simp [inv_map]
  have h_add : (p.2 + 1).val % (m.lcm n) = (p.2.val + 1) % (m.lcm n) := by
    simp +decide [ ← ZMod.natCast_eq_natCast_iff' ];
  have h_add : (p.2 + 1).val ≡ p.2.val + 1 [MOD m] ∧ (p.2 + 1).val ≡ p.2.val + 1 [MOD n] := by
    exact ⟨ Nat.ModEq.of_dvd ( Nat.dvd_lcm_left _ _ ) h_add, Nat.ModEq.of_dvd ( Nat.dvd_lcm_right _ _ ) h_add ⟩;
  simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
  ring

lemma fwd_map_fst_comm (m n : ℕ) [NeZero m] [NeZero n] [NeZero (m.lcm n)] (p : ZMod m × ZMod n) :
  (fwd_map m n (p.1 + 1, p.2 + 1)).1 = (fwd_map m n p).1 := by
    -- By definition of fwd_map, we know that the first component is (x.val - y.val) % g. Adding 1 to both x and y does not change their difference modulo g.
    have h_first_comp : (p.1 + 1).val % Nat.gcd m n = (p.1.val + 1) % Nat.gcd m n ∧ (p.2 + 1).val % Nat.gcd m n = (p.2.val + 1) % Nat.gcd m n := by
      cases m <;> cases n <;> simp_all +decide [ ZMod.val_add, Nat.mod_eq_of_lt ];
      simp +decide [ ZMod.val ];
      exact ⟨ Nat.mod_mod_of_dvd _ ( Nat.gcd_dvd_left _ _ ), Nat.mod_mod_of_dvd _ ( Nat.gcd_dvd_right _ _ ) ⟩;
    unfold fwd_map;
    simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ]

lemma fwd_map_snd_comm (m n : ℕ) [NeZero m] [NeZero n] [NeZero (m.lcm n)] (p : ZMod m × ZMod n) :
  (fwd_map m n (p.1 + 1, p.2 + 1)).2 = (fwd_map m n p).2 + 1 := by
    -- By definition of $fwd\_map$, we know that its second component is the second component of its argument.
    simp [fwd_map];
    norm_num [ Nat.chineseRemainder' ];
    split_ifs <;> simp_all +decide [ Nat.lcm_comm ];
    -- Let's simplify the expression for the second component.
    have h_simp : (n * (n.xgcd m).1 * (p.1 + 1).cast + m * (n.xgcd m).2 * ((p.2 + 1).cast + (n * (n.xgcd m).1 * (p.1 + 1).cast + m * (n.xgcd m).2 * (p.2 + 1).cast - (n * (n.xgcd m).1 * (p.1 + 1).cast + m * (n.xgcd m).2 * (p.2 + 1).cast)) / (n.gcd m))) / (n.gcd m) ≡ (n * (n.xgcd m).1 * p.1.cast + m * (n.xgcd m).2 * (p.2.cast + (n * (n.xgcd m).1 * p.1.cast + m * (n.xgcd m).2 * p.2.cast - (n * (n.xgcd m).1 * p.1.cast + m * (n.xgcd m).2 * p.2.cast)) / (n.gcd m))) / (n.gcd m) + 1 [ZMOD m.lcm n] := by
      have h_simp : (n * (n.xgcd m).1 * (p.1 + 1).cast + m * (n.xgcd m).2 * ((p.2 + 1).cast + (n * (n.xgcd m).1 * (p.1 + 1).cast + m * (n.xgcd m).2 * (p.2 + 1).cast - (n * (n.xgcd m).1 * (p.1 + 1).cast + m * (n.xgcd m).2 * (p.2 + 1).cast)) / (n.gcd m))) ≡ (n * (n.xgcd m).1 * p.1.cast + m * (n.xgcd m).2 * (p.2.cast + (n * (n.xgcd m).1 * p.1.cast + m * (n.xgcd m).2 * p.2.cast - (n * (n.xgcd m).1 * p.1.cast + m * (n.xgcd m).2 * p.2.cast)) / (n.gcd m))) + n.gcd m [ZMOD m.lcm n * n.gcd m] := by
        have h_simp : (n * (n.xgcd m).1 * (p.1 + 1).cast + m * (n.xgcd m).2 * ((p.2 + 1).cast)) ≡ (n * (n.xgcd m).1 * p.1.cast + m * (n.xgcd m).2 * p.2.cast) + n.gcd m [ZMOD m.lcm n * n.gcd m] := by
          have h_simp : (n * (n.xgcd m).1 * (p.1 + 1).cast + m * (n.xgcd m).2 * ((p.2 + 1).cast)) ≡ (n * (n.xgcd m).1 * p.1.cast + m * (n.xgcd m).2 * p.2.cast) + (n * (n.xgcd m).1 + m * (n.xgcd m).2) [ZMOD m.lcm n * n.gcd m] := by
            have h_simp : (p.1 + 1).cast ≡ p.1.cast + 1 [ZMOD m] ∧ (p.2 + 1).cast ≡ p.2.cast + 1 [ZMOD n] := by
              simp +decide [ ← ZMod.intCast_eq_intCast_iff ];
            rw [ Int.modEq_iff_dvd ] at *;
            obtain ⟨ k, hk ⟩ := h_simp.1; obtain ⟨ l, hl ⟩ := h_simp.2.symm.dvd; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
            rw [ show ( p.1 + 1 |> ZMod.cast ) = p.1.cast + 1 - k * m by linarith, show ( p.2 + 1 |> ZMod.cast ) = p.2.cast + 1 + l * n by linarith ] ; ring_nf;
            rw [ show ( m.lcm n : ℤ ) = m * n / Nat.gcd m n from ?_, show ( Nat.gcd m n : ℤ ) = Nat.gcd n m from ?_ ];
            · rw [ Int.mul_ediv_cancel' ];
              · exact ⟨ ( n.xgcd m ).1 * k - ( n.xgcd m ).2 * l, by ring ⟩;
              · exact dvd_mul_of_dvd_left ( mod_cast Nat.gcd_dvd_right _ _ ) _;
            · rw [ Nat.gcd_comm ];
            · exact_mod_cast Eq.symm ( Nat.div_eq_of_eq_mul_left ( Nat.gcd_pos_of_pos_left _ ( Nat.pos_of_ne_zero ‹_› ) ) ( by nlinarith [ Nat.gcd_mul_lcm m n ] ) );
          convert h_simp using 1;
          norm_num [ Nat.gcd_eq_gcd_ab ];
          rfl;
        simp_all +decide [ mul_add, add_assoc ];
      rw [ Int.modEq_iff_dvd ] at *;
      obtain ⟨ k, hk ⟩ := h_simp;
      use k;
      rw [ ← @Int.cast_inj ℚ ] at * ; norm_num at *;
      rw [ Int.cast_div, Int.cast_div ] <;> norm_num;
      · rw [ div_add_one, div_sub_div_same, div_eq_iff ] <;> first | positivity | linarith;
      · exact dvd_add ( dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( mod_cast Nat.gcd_dvd_left _ _ ) _ ) _ ) ( dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( mod_cast Nat.gcd_dvd_right _ _ ) _ ) _ );
      · aesop;
      · exact dvd_add ( dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( mod_cast Nat.gcd_dvd_left _ _ ) _ ) _ ) ( dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( mod_cast Nat.gcd_dvd_right _ _ ) _ ) _ );
      · aesop;
    simp_all +decide [ Int.ModEq, Int.emod_nonneg _ ( by positivity : ( m.lcm n : ℤ ) ≠ 0 ) ];
    convert h_simp using 1 ; ring!;
    norm_num [ ← ZMod.intCast_eq_intCast_iff' ];
    rw [ Int.add_ediv_of_dvd_right, Int.add_ediv_of_dvd_right ] <;> norm_num [ dvd_mul_of_dvd_left, dvd_mul_of_dvd_right, Nat.gcd_dvd_left, Nat.gcd_dvd_right ] ; ring!;
    · rw [ Int.add_ediv_of_dvd_right ] <;> norm_num [ dvd_mul_of_dvd_left, dvd_mul_of_dvd_right, Nat.gcd_dvd_left, Nat.gcd_dvd_right ] ; ring!;
      · rw [ Int.add_ediv_of_dvd_left ] <;> norm_num [ dvd_mul_of_dvd_left, dvd_mul_of_dvd_right, Nat.gcd_dvd_left, Nat.gcd_dvd_right ] ; ring!;
        · rw [ Int.add_ediv_of_dvd_left ] <;> norm_num [ dvd_mul_of_dvd_left, dvd_mul_of_dvd_right, Nat.gcd_dvd_left, Nat.gcd_dvd_right ] ; ring!;
          · constructor <;> intro h <;> linear_combination' h;
          · exact dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( mod_cast Nat.gcd_dvd_left _ _ ) _ ) _;
        · exact dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( mod_cast Nat.gcd_dvd_left _ _ ) _ ) _;
      · exact dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( mod_cast Nat.gcd_dvd_right _ _ ) _ ) _;
    · exact dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( mod_cast Nat.gcd_dvd_right _ _ ) _ ) _;
    · exact dvd_mul_of_dvd_left ( dvd_mul_of_dvd_left ( mod_cast Nat.gcd_dvd_right _ _ ) _ ) _

lemma fwd_comm (m n : ℕ) [NeZero m] [NeZero n] [NeZero (m.lcm n)] (p : ZMod m × ZMod n) :
  fwd_map m n (p.1 + 1, p.2 + 1) = (let r := fwd_map m n p; (r.1, r.2 + 1)) := by
  apply Prod.ext
  · exact fwd_map_fst_comm m n p
  · exact fwd_map_snd_comm m n p

lemma left_inv (m n : ℕ) [NeZero m] [NeZero n] [NeZero (m.lcm n)] (p : ZMod m × ZMod n) :
  inv_map m n (fwd_map m n p) = p := by
    -- By definition of fwd_map, we have that fwd_map m n p = (i, z) where i = x.val - y.val and z is the unique solution to the system of congruences.
    obtain ⟨i, z⟩ : ∃ i : Fin (Nat.gcd m n), ∃ z : ZMod (m.lcm n), fwd_map m n p = (i, z) := by
      exact ⟨ _, _, rfl ⟩;
    -- By definition of fwd_map, we have that z ≡ y + i.val (mod n) and z ≡ x (mod m).
    obtain ⟨z, hz⟩ := z
    have hz_mod_n : z.val ≡ p.2.val + i.val [MOD n] := by
      unfold fwd_map at hz;
      -- By definition of the Chinese Remainder Theorem, we have that $z \equiv p.2.val + i.val \pmod{n}$.
      have hz_mod_n : (Nat.chineseRemainder' (m := m) (n := n) (a := p.2.val + i.val) (b := p.1.val) (by
      grind)).val ≡ p.2.val + i.val [MOD n] := by
        convert Nat.chineseRemainder' _ |>.2.1 using 1
      generalize_proofs at *;
      simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
      convert hz_mod_n using 1;
      rw [ ← hz.2 ];
      -- The cast from ZMod (m.lcm n) to ZMod n is the same as the modulo operation with n.
      have h_cast_mod : ∀ (x : ℕ), (x : ZMod (m.lcm n)).cast = (x : ZMod n) := by
        intro x; exact (by
        erw [ ZMod.cast_eq_val ];
        erw [ ZMod.natCast_eq_natCast_iff ];
        simp +decide [ Nat.ModEq, ZMod.val_natCast ];
        rw [ Nat.mod_mod_of_dvd _ ( Nat.dvd_lcm_right _ _ ) ])
        skip
      generalize_proofs at *;
      convert h_cast_mod _ using 1;
      congr! 2;
      · aesop;
      · congr! 1;
        aesop
    have hz_mod_m : z.val ≡ p.1.val [MOD m] := by
      -- By definition of fwd_map, we know that z.val ≡ p.1.val [MOD m].
      have hz_mod_m : z.val ≡ p.1.val [MOD m] := by
        have := hz
        unfold fwd_map at this;
        -- By definition of Chinese Remainder Theorem, we know that $z \equiv p.1.val \pmod{m}$.
        have hz_mod_m : (Nat.chineseRemainder' (m := m) (n := n) (a := p.2.val + (p.1.val - p.2.val : ZMod (Nat.gcd m n)).val) (b := p.1.val) (by
        grind)).val ≡ p.1.val [MOD m] := by
          exact Nat.chineseRemainder' _ |>.2.2
        generalize_proofs at *;
        simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
        convert hz_mod_m using 1;
        rw [ ← this.2 ];
        -- Since $m$ divides $m.lcm n$, the cast from $ZMod (m.lcm n)$ to $ZMod m$ is the identity function.
        have h_cast_id : ∀ x : ℕ, (x : ZMod (m.lcm n)).cast = (x : ZMod m) := by
          intro x; erw [ ZMod.cast_eq_val ] ;
          rw [ ← Nat.mod_add_div x ( m.lcm n ) ] ; norm_num [ Nat.mod_eq_of_lt ( Nat.pos_of_ne_zero ( NeZero.ne m ) ), Nat.mod_eq_of_lt ( Nat.pos_of_ne_zero ( NeZero.ne n ) ), Nat.mod_eq_of_lt ( Nat.pos_of_ne_zero ( NeZero.ne ( m.lcm n ) ) ) ] ;
          norm_num [ show ( m.lcm n : ZMod m ) = 0 from by rw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.dvd_lcm_left _ _ ];
        exact h_cast_id _
      exact hz_mod_m;
    simp_all +decide [ inv_map, Nat.ModEq ];
    haveI := Fact.mk ( NeZero.pos m ) ; haveI := Fact.mk ( NeZero.pos n ) ; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ] ;

lemma right_inv (m n : ℕ) [NeZero m] [NeZero n] [NeZero (m.lcm n)] (p : Fin (m.gcd n) × ZMod (m.lcm n)) :
  fwd_map m n (inv_map m n p) = p := by
    -- By definition of fwd_map, we know that fwd_map m n (inv_map m n p) = p for any p. This follows from the properties of the fwd_map and inv_map, specifically that inv_map￮fwd_map is the identity.
    have h_fst : (fwd_map m n (inv_map m n p)).1 = p.1 := by
      unfold inv_map fwd_map;
      field_simp;
      refine' Fin.ext _;
      -- By definition of ZMod, we know that $p.2.val \equiv p.2.val \pmod{m}$ and $p.2.val \equiv p.2.val \pmod{n}$.
      have h_mod_m : (p.2.val : ZMod m).val ≡ p.2.val [MOD m] := by
        simp +decide [ ← ZMod.natCast_eq_natCast_iff ]
      have h_mod_n : (p.2.val : ZMod n).val ≡ p.2.val [MOD n] := by
        simp +decide [ ← ZMod.natCast_eq_natCast_iff ];
      -- By definition of ZMod, we know that $p.2.val \equiv p.2.val \pmod{m}$ and $p.2.val \equiv p.2.val \pmod{n}$, so we can simplify the expression.
      have h_simp : ((p.2.val : ZMod m).val - ((p.2.val : ZMod n) - p.1.val).val) ≡ p.1.val [ZMOD Nat.gcd m n] := by
        have h_simp : ((p.2.val : ZMod m).val - ((p.2.val : ZMod n) - p.1.val).val) ≡ p.1.val [ZMOD Nat.gcd m n] := by
          have h_mod_m : ((p.2.val : ZMod m).val : ℤ) ≡ p.2.val [ZMOD Nat.gcd m n] := by
            exact Int.natCast_modEq_iff.mpr ( h_mod_m.of_dvd <| Nat.gcd_dvd_left _ _ )
          have h_mod_n : ((p.2.val : ZMod n) - p.1.val).val ≡ p.2.val - p.1.val [ZMOD Nat.gcd m n] := by
            have h_mod_n : ((p.2.val : ZMod n) - p.1.val).val ≡ p.2.val - p.1.val [ZMOD n] := by
              simp +decide [ ← ZMod.intCast_eq_intCast_iff ]
            generalize_proofs at *; (
            exact h_mod_n.of_dvd <| mod_cast Nat.gcd_dvd_right _ _)
          exact Int.ModEq.sub h_mod_m h_mod_n |> Int.ModEq.trans <| by ring_nf; norm_num;
        generalize_proofs at *; (
        convert h_simp using 1);
      simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ];
      exact Nat.mod_eq_of_lt p.1.2
    have h_snd : (fwd_map m n (inv_map m n p)).2 = p.2 := by
      -- By definition of fwd_map, we know that fwd_map m n (inv_map m n p) = p for any p. This follows from the properties of the fwd_map and inv_map, specifically that inv_map￮fwd_map is the identity. Hence, we can conclude that (fwd_map m n (inv_map m n p)).2 = p.2 by the definition of fwd_map.
      apply Eq.symm; exact (by
      apply Eq.symm; exact (by
        have := left_inv m n (inv_map m n p);
        injection this;
        have h_snd_eq : (fwd_map m n (inv_map m n p)).2.val ≡ p.2.val [MOD m.lcm n] := by
          have h_snd_eq : (fwd_map m n (inv_map m n p)).2.val ≡ p.2.val [MOD m] ∧ (fwd_map m n (inv_map m n p)).2.val ≡ p.2.val [MOD n] := by
            simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
          exact Nat.modEq_of_dvd <| by simpa using lcm_dvd ( Nat.modEq_iff_dvd.mp h_snd_eq.1 ) ( Nat.modEq_iff_dvd.mp h_snd_eq.2 ) ;
        rw [ ← ZMod.natCast_eq_natCast_iff ] at * ; aesop;))
    exact Prod.ext h_fst h_snd

end AristotleLemmas

example (m n : ℕ) [NeZero m] [NeZero n] [NeZero (m.lcm n)] : Nonempty (KCycleProd m n ≅ KCycleDecomp m n) := by
  refine' ⟨ _ ⟩;
  fconstructor;
  exact ⟨ fwd_map m n, by
    exact funext fun x => fwd_comm m n x ⟩
  all_goals generalize_proofs at *;
  exact ⟨ inv_map m n, by
    exact funext fun x => inv_comm m n x ⟩
  all_goals generalize_proofs at *;
  · exact Subtype.ext <| funext fun x => left_inv m n x;
  · exact Subtype.eq ( funext fun x => right_inv m n x )
/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.ModularGroup
public import QPainleve.Algebra.Cluster.Word.RationalMap
public import QPainleve.SignedClusterModularGroup.Realization.Agreement
public import QPainleve.SignedClusterModularGroup.Realization.Boundary

import QPainleve.SignedClusterModularGroup.Realization.SignedWord

/-!
# Descent of the Picard action of cluster loops

For a fixed marked toric presentation, geometric realizations of cluster loops induce
a homomorphism from the opposite point-map group to the signed boundary isometry group.
The action on a representative is computed by any geometric realization. For
orientation-preserving realizations the action takes values in the boundary rotations.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite
open QPainleve.CharacterTorus QPainleve.Cluster TauCeti.AlgebraicGeometry TauCeti.Toric
open AlgebraicGeometry.Scheme

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

section Rotation

open SignedBoundaryIsometryGroup

variable {k : Type*} [Field k] {ι : Type*} [DecidableEq ι] {E : SkewExchangeMatrix ι}
  {L : Type*} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L} {n : ℕ} {d : ZMod n → L}
  (ρ : (SignedClusterModularGroup k E)ᵐᵒᵖ →* signedBoundaryIsometryGroup B d)

local notation "incl" => clusterModularGroupInclusion k E
local notation "rot" => rotationInclusion B d
local notation "Positive" => Subgroup.unop (MonoidHom.ker (MonoidHom.comp (sign B d) ρ))

/-- Restrict a signed Picard homomorphism to unsigned X maps with positive
Picard sign, taking values in the boundary rotations. -/
noncomputable def picardRotationHom (hpos : MonoidHom.range incl ≤ Positive) :
    (ClusterModularGroup k E)ᵐᵒᵖ →* boundaryRotationGroup B d :=
  (MonoidHom.ofInjective (rotationInclusion_injective B d)).symm.toMonoidHom.comp
    ((ρ.comp (MonoidHom.op incl)).codRestrict (MonoidHom.range rot) fun x ↦ by
      rw [range_rotationInclusion]
      exact hpos ⟨x.unop, rfl⟩)

/-- Including the rotation recovers the signed action on the given unsigned X map. -/
@[simp]
theorem rotationInclusion_picardRotationHom_apply (hpos : MonoidHom.range incl ≤ Positive)
    (x : (ClusterModularGroup k E)ᵐᵒᵖ) :
    rot (picardRotationHom ρ hpos x) = ρ (MonoidHom.op incl x) :=
  MonoidHom.apply_ofInjective_symm (rotationInclusion_injective B d) _

/-- If positive sign characterizes unsigned maps, the rotation action is
surjective exactly when the signed action realizes every rotation. -/
theorem picardRotationHom_surjective_iff (hpos : Positive = MonoidHom.range incl) :
    Function.Surjective (picardRotationHom ρ hpos.ge) ↔ MonoidHom.range rot ≤ ρ.range := by
  constructor
  · intro hs g hg
    obtain ⟨y, rfl⟩ := hg
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨MonoidHom.op incl x, (rotationInclusion_picardRotationHom_apply ρ hpos.ge x).symm⟩
  · intro hs y
    have hy : rot y ∈ MonoidHom.range rot := ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := hs hy
    have hxpos : x.unop ∈ Positive := by
      rw [Subgroup.mem_unop, op_unop, MonoidHom.mem_ker, MonoidHom.comp_apply, hx]
      rwa [range_rotationInclusion, MonoidHom.mem_ker] at hy
    obtain ⟨u, hu⟩ := hpos ▸ hxpos
    refine ⟨op u, rotationInclusion_injective B d ?_⟩
    simpa only [rotationInclusion_picardRotationHom_apply, MonoidHom.op_apply_apply,
      Function.comp_apply, unop_op, hu, op_unop] using hx

end Rotation

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [hΦ₀ : Nonempty Φ.cones]
  {r m n : ℕ} [NeZero m] [NeZero n] {L : Type} [AddCommGroup L]
  {B : LinearMap.BilinForm ℤ L} {E : SkewExchangeMatrix (Fin r)}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "Dtor[" Φ "," h "]" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h)
local notation "Loops[" E "]" => End (Prefunctor.obj (Paths.of (SkewExchangeMatrix (Fin r))) E)
local notation "word(" w ")" => End.asHom w
local notation "xMap[" E "," w "]" =>
  Quiver.Path.xRationalMap (B := E) (C := E) ℂ (word(w))
local notation "PointMaps[" E "]" => ClusterModularGroup ℂ E
local notation "evalLoop[" E "]" => clusterModularGroupMap ℂ E
local notation "evalSignedLoop[" E "]" => signedClusterModularGroupMap ℂ E

-- The endomorphism projection has the path-category hom type. State the instance
-- at that type so typeclass search can use dominance of the underlying word map.
local instance (w : Loops[E]) : xMap[E,w].IsDominant :=
  Quiver.Path.instIsDominantXRationalMap ℂ (word(w))

variable {T₀ : Over S} [Nonempty T₀.left] [Smooth T₀.hom]
  {P : Point T₀ → MarkedSurface ℂ n B X[r]}
  (D : ZMod n → L) (hD : ∀ c, (P c).pair.hom.left.ker.IsEffectiveCartier)
  (hmark : ∀ c j, (P c).boundaryClass (hD c) j = D j)

variable {b : Module.Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}
  [PrestableFamily (Dtor[Φ,hΦ₀] ↘ S)] {γ : Type*} {a : γ → (Dtor[Φ,hΦ₀] ↘ S).smoothLocus}
  {T : NodalCycleNumbering a m} {origin : ZMod m}
  {ι : L →ₗ[ℤ] Additive (LineBundleClass Φ.algebraicRealization) × (Fin r → ℤ)}
  {centers : Point T₀ → Multiplicative (Fin r → ℤ) →* ℂˣ}
  (hc : Φ.IsComplete) (hι : Function.Injective ι)
  (hindex : (Fan.rayChargeMap s).range.toAddSubgroup.index ≠ 0)
  (hmodels : ∀ c, Nonempty (ContractedToricFiber b s hΦ T origin ι (centers c) (P c)))

local notation "Models[" C "]" =>
  HasToricTargetModels (b := b) (s := s) (hΦ := hΦ) (T := T) (origin := origin)
    (ι := ι) (P₁ := P) centers C

local notation "PicardRotations[" B "," D "]" => boundaryRotationGroup B D
local notation "asIsometry[" B "]" =>
  Equiv.symm (LinearMap.BilinForm.isometryGroupEquivIsometryEquiv B)

open SignedBoundaryIsometryGroup

include hmark hc hι hindex in
private theorem signedAction_eq_of_xMap_eq
    {C C' : T₀.left.PartialMap T₀.left} [IsDominant C.hom] [IsDominant C'.hom]
    [C.IsOver T₀.hom T₀.hom] [C'.IsOver T₀.hom T₀.hom]
    {F F' : X[r] ⤏ X[r]} [F.IsDominant] [F'.IsDominant]
    (R : GeometricRealization P P C F) (R' : GeometricRealization P P C' F') (h : F = F')
    (hC : Models[C]) (hC' : Models[C']) :
    R.toSignedBoundaryIsometry D hD hmark = R'.toSignedBoundaryIsometry D hD hmark := by
  obtain ⟨hpic, hbranch⟩ := R.marked_actions_eq_of_xMap_eq R' h hc hι hindex centers hC hC'
  apply Subtype.ext
  simp only [coe_toSignedBoundaryIsometry, hpic, orientation_def, hbranch]

variable [PreirreducibleSpace T₀.left]

section LoopMap

variable {M : Type} [Monoid M]

private noncomputable def loopSignedAction
    (toLoop : M →* Loops[E]) (C : M → T₀.left.PartialMap T₀.left)
    [∀ w : M, IsDominant (C w).hom] [∀ w : M, (C w).IsOver T₀.hom T₀.hom]
    (R : ∀ w : M, GeometricRealization P P (C w) xMap[E,toLoop w])
    (hC : ∀ w, Models[C w]) :
    Mᵐᵒᵖ →* signedBoundaryIsometryGroup B D :=
  MonoidHom.mk' (fun w ↦ (R w.unop).toSignedBoundaryIsometry D hD hmark) fun w v ↦ by
    -- Opposite loop multiplication executes the left word first.
    have h : xMap[E,toLoop (v.unop * w.unop)] =
        (xMap[E,toLoop w.unop]).comp (xMap[E,toLoop v.unop]) := by
      rw [map_mul toLoop]
      exact Quiver.Path.xRationalMap_comp ℂ _ _
    have hcomp : Models[(C w.unop).comp (C v.unop)] := by
      intro c
      simpa only [Category.assoc, Scheme.PartialMap.compDomainRight_target] using
        hC v.unop (c ≫ (C w.unop).compDomainRight (C v.unop))
    exact (signedAction_eq_of_xMap_eq D hD hmark hc hι hindex
      (R (v.unop * w.unop)) ((R w.unop).comp (R v.unop)) h
        (hC (v.unop * w.unop)) hcomp).trans
      ((R w.unop).toSignedBoundaryIsometry_comp D hD hmark (R v.unop))

include hmark hc hι hindex in
private theorem exists_signedAction_of_loopMap {G : Type} [Monoid G]
    (toLoop : M →* Loops[E]) (C : M → T₀.left.PartialMap T₀.left)
    [∀ w : M, IsDominant (C w).hom] [∀ w : M, (C w).IsOver T₀.hom T₀.hom]
    (R : ∀ w : M, GeometricRealization P P (C w) xMap[E,toLoop w])
    (hC : ∀ w, Models[C w]) (eval : M →* G) (heval : Function.Surjective eval)
    (hmap : ∀ w v, eval w = eval v → xMap[E,toLoop w] = xMap[E,toLoop v]) :
    ∃ ρ : Gᵐᵒᵖ →* signedBoundaryIsometryGroup B D, ∀ (w : M),
      ∀ {C' : T₀.left.PartialMap T₀.left} [IsDominant C'.hom] [C'.IsOver T₀.hom T₀.hom]
        (R' : GeometricRealization P P C' xMap[E,toLoop w]), Models[C'] →
        ρ (op (eval w)) = R'.toSignedBoundaryIsometry D hD hmark := by
  let f := loopSignedAction D hD hmark hc hι hindex toLoop C R hC
  let q := eval.op
  have hq : Function.Surjective q := op_surjective.comp (heval.comp unop_surjective)
  have hker : Con.ker q ≤ Con.ker f := by
    intro w v hwv
    have he := congrArg unop ((Con.ker_rel q).mp hwv)
    exact (Con.ker_rel f).mpr (signedAction_eq_of_xMap_eq D hD hmark hc hι hindex
      (R w.unop) (R v.unop) (hmap w.unop v.unop he) (hC w.unop) (hC v.unop))
  let e := Con.quotientKerEquivOfSurjective q hq
  refine ⟨((Con.ker q).lift f hker).comp e.symm.toMonoidHom, fun w C' _ _ R' hC' ↦ ?_⟩
  have he : e (op w : (Con.ker q).Quotient) = op (eval w) :=
    Con.kerLift_mk (f := q) (op w)
  rw [MonoidHom.comp_apply, ← he, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
    Con.lift_coe]
  exact signedAction_eq_of_xMap_eq D hD hmark hc hι hindex (R w) R' rfl (hC w) hC'

end LoopMap

include hmark hc hι hindex hmodels in
/-- If each inversion-free loop has an orientation-preserving realization over a
fixed ordered toric presentation of finite charge index, there is a unique homomorphism
from the opposite point-map group to the boundary rotation isometries whose value on
each loop is the Picard pullback of any realization of that loop. -/
theorem existsUnique_picardHom
    (hreal : ∀ w : inversionFreeLoops E, ∃ (C : T₀.left.PartialMap T₀.left)
      (hC : IsDominant C.hom) (hCO : C.IsOver T₀.hom T₀.hom),
      letI := hC
      letI := hCO
      ∃ R : GeometricRealization P P C xMap[E,w.val], R.orientation = 1) :
    ∃! ρ : (PointMaps[E])ᵐᵒᵖ →* PicardRotations[B,D], ∀ (w : inversionFreeLoops E),
      ∀ {C' : T₀.left.PartialMap T₀.left} [IsDominant C'.hom] [C'.IsOver T₀.hom T₀.hom]
        (R' : GeometricRealization P P C' xMap[E,w.val]),
        (ρ (op (evalLoop[E] w)) : B.isometryGroup) = asIsometry[B] R'.picard := by
  classical
  choose C hC hCO R horient using hreal
  let : ∀ w : inversionFreeLoops E, IsDominant (C w).hom := hC
  let : ∀ w : inversionFreeLoops E, (C w).IsOver T₀.hom T₀.hom := hCO
  obtain ⟨ρ, hρ⟩ := exists_signedAction_of_loopMap D hD hmark hc hι hindex
    (inversionFreeLoops E).subtype C R (fun w c ↦ hmodels (c ≫ (C w).domainTarget))
    evalLoop[E] (clusterModularGroupMap_surjective ℂ E)
    (fun w v h ↦ (Quiver.Path.xRationalMap_eq_iff ℂ word(w.val) word(v.val)).mpr
      ((clusterModularGroupMap_eq_iff ℂ E w v).mp h))
  have happly (w : inversionFreeLoops E) {C' : T₀.left.PartialMap T₀.left}
      [IsDominant C'.hom] [C'.IsOver T₀.hom T₀.hom]
      (R' : GeometricRealization P P C' xMap[E,w.val]) :
      toIsometry B D (ρ (op (evalLoop[E] w))) = asIsometry[B] R'.picard := by
    calc
      _ = toIsometry B D (R'.toSignedBoundaryIsometry D hD hmark) :=
        congrArg (toIsometry B D) (hρ w R' (fun c ↦ hmodels (c ≫ C'.domainTarget)))
      _ = _ := (toIsometry_apply B D _).trans
        (congrArg Prod.fst (coe_toSignedBoundaryIsometry R' D hD hmark))
  have hmem (g : (PointMaps[E])ᵐᵒᵖ) : toIsometry B D (ρ g) ∈ PicardRotations[B,D] := by
    obtain ⟨w, hw⟩ := clusterModularGroupMap_surjective ℂ E g.unop
    rw [← op_unop g, ← hw, happly w (R w)]
    exact (R w).picard_mem_boundaryRotationGroup D hD hmark (horient w)
  refine ⟨((toIsometry B D).comp ρ).codRestrict _ hmem, ?_, ?_⟩
  · intro w C' _ _ R'
    simpa only [MonoidHom.codRestrict_apply, MonoidHom.comp_apply] using happly w R'
  · intro ρ' hρ'
    ext g : 1
    obtain ⟨w, hw⟩ := clusterModularGroupMap_surjective ℂ E g.unop
    rw [← op_unop g, ← hw]
    apply Subtype.ext
    simpa only [MonoidHom.codRestrict_apply, MonoidHom.comp_apply] using
      (hρ' w (R w)).trans (happly w (R w)).symm

include hmark hc hι hindex in
/-- Realizations of the signed loops over a fixed toric presentation determine
one Picard homomorphism on the opposite group of independent X maps. It computes
inversion parity and agrees with every marked realization whose reached fibers
admit the given toric presentation. -/
theorem existsUnique_signedPicardHom_of_realizations
    (hreal : ∀ w : Loops[E], ∃ (C : T₀.left.PartialMap T₀.left)
      (hC : IsDominant C.hom) (hCO : C.IsOver T₀.hom T₀.hom),
      letI := hC
      letI := hCO
      ∃ R : GeometricRealization P P C xMap[E,w],
        R.orientation = (-1 : ℤˣ) ^ (word(w)).inversionCount ∧ Models[C]) :
    ∃! ρ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ →* signedBoundaryIsometryGroup B D, ∀ (w : Loops[E]),
      sign B D (ρ (op (evalSignedLoop[E] w))) = (-1 : ℤˣ) ^ (word(w)).inversionCount ∧
      ∀ {C' : T₀.left.PartialMap T₀.left} [IsDominant C'.hom] [C'.IsOver T₀.hom T₀.hom]
        (R' : GeometricRealization P P C' xMap[E,w]), Models[C'] →
        ρ (op (evalSignedLoop[E] w)) = R'.toSignedBoundaryIsometry D hD hmark := by
  classical
  choose C hC hCO R horient htarget using hreal
  let : ∀ w : Loops[E], IsDominant (C w).hom := hC
  let : ∀ w : Loops[E], (C w).IsOver T₀.hom T₀.hom := hCO
  obtain ⟨ρ, hρ⟩ := exists_signedAction_of_loopMap D hD hmark hc hι hindex
    (MonoidHom.id _) C R htarget evalSignedLoop[E] (signedClusterModularGroupMap_surjective ℂ E)
    (fun w v h ↦ (Quiver.Path.xRationalMap_eq_iff ℂ word(w) word(v)).mpr
      ((signedClusterModularGroupMap_eq_iff ℂ E w v).mp h))
  refine ⟨ρ, fun w ↦ ⟨?_, hρ w⟩, fun ρ' hρ' ↦ MonoidHom.ext fun g ↦ ?_⟩
  · calc
      _ = sign B D ((R w).toSignedBoundaryIsometry D hD hmark) :=
        congrArg (sign B D) (hρ w (R w) (htarget w))
      _ = (R w).orientation := (sign_apply B D _).trans
        (congrArg Prod.snd (coe_toSignedBoundaryIsometry (R w) D hD hmark))
      _ = _ := horient w
  · obtain ⟨w, hw⟩ := signedClusterModularGroupMap_surjective ℂ E g.unop
    rw [← op_unop g, ← hw, (hρ' w).2 (R w) (htarget w), hρ w (R w) (htarget w)]

include hmark hc hι hindex hmodels in
/-- Orientation-preserving realizations of the inversion-free loops and one
orientation-reversing realization of an odd loop determine the signed Picard
pullback homomorphism of a fixed ordered toric presentation of finite charge index.
Its sign is the inversion parity. Its value on each loop is the marked Picard
pullback and branch sign of any realization of that loop. -/
theorem existsUnique_signedPicardHom
    (hfree : ∀ w : inversionFreeLoops E, ∃ (C : T₀.left.PartialMap T₀.left)
      (hC : IsDominant C.hom) (hCO : C.IsOver T₀.hom T₀.hom),
      letI := hC
      letI := hCO
      ∃ R : GeometricRealization P P C xMap[E,w.val], R.orientation = 1)
    (o : Word E E) (ho : Odd o.inversionCount)
    {Codd : T₀.left.PartialMap T₀.left} [IsDominant Codd.hom] [Codd.IsOver T₀.hom T₀.hom]
    (O : GeometricRealization P P Codd (o.xRationalMap ℂ)) (hO : O.orientation = -1) :
    ∃! ρ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ →* signedBoundaryIsometryGroup B D, ∀ (w : Loops[E]),
      sign B D (ρ (op (evalSignedLoop[E] w))) = (-1 : ℤˣ) ^ (word(w)).inversionCount ∧
      ∀ {C' : T₀.left.PartialMap T₀.left} [IsDominant C'.hom] [C'.IsOver T₀.hom T₀.hom]
        (R' : GeometricRealization P P C' xMap[E,w]),
        ρ (op (evalSignedLoop[E] w)) = R'.toSignedBoundaryIsometry D hD hmark := by
  have hreal (w : Loops[E]) :=
    exists_of_inversionFree_and_odd
      (fun v hv ↦ hfree ⟨End.of v, (mem_inversionFreeLoops_iff E _).mpr hv⟩) o ho O hO
      (word(w))
  have hreal' (w : Loops[E]) : ∃ (C : T₀.left.PartialMap T₀.left)
      (hC : IsDominant C.hom) (hCO : C.IsOver T₀.hom T₀.hom),
      letI := hC
      letI := hCO
      ∃ R : GeometricRealization P P C xMap[E,w],
        R.orientation = (-1 : ℤˣ) ^ (word(w)).inversionCount ∧ Models[C] := by
    obtain ⟨C, hC, hCO, R, hsign⟩ := hreal w
    exact ⟨C, hC, hCO, R, hsign, fun c ↦ hmodels (c ≫ C.domainTarget)⟩
  obtain ⟨ρ, hρ, huniq⟩ :=
    existsUnique_signedPicardHom_of_realizations D hD hmark hc hι hindex (centers := centers) hreal'
  refine ⟨ρ, fun w ↦ ⟨(hρ w).1, fun R' ↦ ?_⟩, fun ρ' hρ' ↦ ?_⟩
  · exact (hρ w).2 R' (fun c ↦ hmodels (c ≫ _))
  · exact huniq ρ' (fun w ↦ ⟨(hρ' w).1, fun R' _ ↦ (hρ' w).2 R'⟩)

end QPainleve.SignedClusterModularGroup.GeometricRealization

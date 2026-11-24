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

/-!
# Descent of the Picard action of cluster loops

For a fixed marked toric presentation, orientation-preserving realizations of the
inversion-free loops induce a Picard pullback on the opposite cluster modular group.
The action on a representative is computed by any geometric realization. The
composition law uses the reverse order of the geometric maps.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite
open QPainleve.CharacterTorus QPainleve.Cluster TauCeti.AlgebraicGeometry TauCeti.Toric
open AlgebraicGeometry.Scheme

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [hΦ₀ : Nonempty Φ.cones]
  {r m n : ℕ} [NeZero m] [NeZero n] {L : Type} [AddCommGroup L]
  {B : LinearMap.BilinForm ℤ L} {E : SkewExchangeMatrix (Fin r)}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "Dtor[" Φ "," h "]" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h)
local notation "Loops[" E "]" => inversionFreeLoops E
local notation "word(" w ")" => End.asHom (Subtype.val w)
local notation "xMap[" E "," w "]" =>
  Quiver.Path.xRationalMap (B := E) (C := E) ℂ (End.asHom (Subtype.val w))
local notation "PointMaps[" E "]" => ClusterModularGroup ℂ E
local notation "evalLoop[" E "]" => clusterModularGroupMap ℂ E

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

local notation "PicardRotations[" B "," D "]" => boundaryRotationGroup B D
local notation "asIsometry[" B "]" =>
  Equiv.symm (LinearMap.BilinForm.isometryGroupEquivIsometryEquiv B)

variable (C : Loops[E] → T₀.left.PartialMap T₀.left)
  [∀ w : Loops[E], IsDominant (C w).hom] [∀ w : Loops[E], (C w).IsOver T₀.hom T₀.hom]
  (R : ∀ w : Loops[E], GeometricRealization P P (C w) xMap[E,w])

include hc hι hindex hmodels in
private theorem loop_picard_eq (w : Loops[E]) {C' : T₀.left.PartialMap T₀.left}
    [IsDominant C'.hom] [C'.IsOver T₀.hom T₀.hom] {F : X[r] ⤏ X[r]} [F.IsDominant]
    (R' : GeometricRealization P P C' F) (hF : xMap[E,w] = F) :
    (R w).picard = R'.picard :=
  ((R w).marked_actions_eq_of_xMap_eq R' hF hc hι hindex centers
    (fun c ↦ hmodels (c ≫ (C w).domainTarget)) (fun c ↦ hmodels (c ≫ C'.domainTarget))).1

variable [PreirreducibleSpace T₀.left]

include hmark hc hι hindex hmodels in
private noncomputable def loopPicardHom (horient : ∀ w, (R w).orientation = 1) :
    Loops[E] →* (PicardRotations[B,D])ᵐᵒᵖ where
  toFun w := op ⟨asIsometry[B] (R w).picard,
    (R w).picard_mem_boundaryRotationGroup D hD hmark (horient w)⟩
  map_one' := by
    have h := loop_picard_eq hc hι hindex hmodels C R 1 (refl P)
      (Quiver.Path.xRationalMap_nil ℂ (B := E))
    apply unop_injective
    apply Subtype.ext
    refine (congrArg asIsometry[B] h).trans ?_
    have h₁ := congrArg (fun p : signedBoundaryIsometryGroup B D ↦ p.val.1)
      (toSignedBoundaryIsometry_refl (P := P) D hD hmark)
    simpa only [unop_one, Subgroup.coe_one, coe_toSignedBoundaryIsometry, Prod.fst_one] using h₁
  map_mul' w v := by
    have h := loop_picard_eq hc hι hindex hmodels C R (w * v) ((R v).comp (R w))
      (Quiver.Path.xRationalMap_comp ℂ word(v) word(w))
    apply unop_injective
    apply Subtype.ext
    refine (congrArg asIsometry[B] h).trans ?_
    have hcomp := congrArg (fun p : signedBoundaryIsometryGroup B D ↦ p.val.1)
      ((R v).toSignedBoundaryIsometry_comp D hD hmark (R w))
    simpa only [unop_mul, unop_op, Subgroup.coe_mul, coe_toSignedBoundaryIsometry, Prod.fst_mul]
      using hcomp

include hmark hc hι hindex hmodels in
private theorem exists_picardHom_of_realizations (horient : ∀ w, (R w).orientation = 1) :
    ∃ ρ : (PointMaps[E])ᵐᵒᵖ →* PicardRotations[B,D], ∀ (w : Loops[E]),
      ∀ {C' : T₀.left.PartialMap T₀.left} [IsDominant C'.hom] [C'.IsOver T₀.hom T₀.hom]
        (R' : GeometricRealization P P C' xMap[E,w]),
        (ρ (op (evalLoop[E] w)) : B.isometryGroup) = asIsometry[B] R'.picard := by
  let f := loopPicardHom D hD hmark hc hι hindex hmodels C R horient
  have hker : Con.ker evalLoop[E] ≤ Con.ker f := by
    intro w v hwv
    have h := (clusterModularGroupMap_eq_iff ℂ E w v).mp ((Con.ker_rel _).mp hwv)
    have hmap := (Quiver.Path.xRationalMap_eq_iff ℂ (word(w) : Word E E) word(v)).2 h
    have he := loop_picard_eq hc hι hindex hmodels C R w (R v) hmap
    exact (Con.ker_rel _).mpr (unop_injective (Subtype.ext (congrArg asIsometry[B] he)))
  let g := ((Con.ker evalLoop[E]).lift f hker).comp
    (unsignedLoopQuotientMulEquiv ℂ E).symm.toMonoidHom
  -- Transfer the opposite from the Picard target to the point-map source.
  let ρ := (MulEquiv.opOp (PicardRotations[B,D])).symm.toMonoidHom.comp (MonoidHom.op g)
  refine ⟨ρ, fun w C' _ _ R' ↦ ?_⟩
  have hg : g (evalLoop[E] w) = f w := by
    rw [← unsignedLoopQuotientMulEquiv_mk, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, Con.lift_coe]
  have hρ : ρ (op (evalLoop[E] w)) = (g (evalLoop[E] w)).unop := rfl
  rw [hρ, hg]
  exact congrArg asIsometry[B] (loop_picard_eq hc hι hindex hmodels C R w R' rfl)

include hmark hc hι hindex hmodels in
/-- If each inversion-free loop has an orientation-preserving realization over a
fixed ordered toric presentation of finite charge index, there is a unique homomorphism
from the opposite point-map group to the boundary rotation isometries whose value on
each loop is the Picard pullback of any realization of that loop. -/
theorem existsUnique_picardHom
    (hreal : ∀ w : Loops[E], ∃ (C : T₀.left.PartialMap T₀.left)
      (hC : IsDominant C.hom) (hCO : C.IsOver T₀.hom T₀.hom),
      letI := hC
      letI := hCO
      ∃ R : GeometricRealization P P C xMap[E,w], R.orientation = 1) :
    ∃! ρ : (PointMaps[E])ᵐᵒᵖ →* PicardRotations[B,D], ∀ (w : Loops[E]),
      ∀ {C' : T₀.left.PartialMap T₀.left} [IsDominant C'.hom] [C'.IsOver T₀.hom T₀.hom]
        (R' : GeometricRealization P P C' xMap[E,w]),
        (ρ (op (evalLoop[E] w)) : B.isometryGroup) = asIsometry[B] R'.picard := by
  classical
  choose C hC hCO R horient using hreal
  let : ∀ w : Loops[E], IsDominant (C w).hom := hC
  let : ∀ w : Loops[E], (C w).IsOver T₀.hom T₀.hom := hCO
  obtain ⟨ρ, hρ⟩ := exists_picardHom_of_realizations D hD hmark hc hι hindex hmodels C R horient
  refine ⟨ρ, hρ, fun ρ' hρ' ↦ MonoidHom.ext fun g ↦ ?_⟩
  obtain ⟨w, hw⟩ := clusterModularGroupMap_surjective ℂ E g.unop
  have hg : op (evalLoop[E] w) = g := unop_injective hw
  rw [← hg]
  exact Subtype.ext ((hρ' w (R w)).trans (hρ w (R w)).symm)

end QPainleve.SignedClusterModularGroup.GeometricRealization

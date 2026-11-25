/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.PicardAction

import QPainleve.Algebra.Cluster.ChargeKernel.Index
import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.Endpoint.Kernel
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber

/-!
# The Picard action of unsigned cluster loops in a marked presentation

The signed Picard action restricts to the unsigned point-map group and takes
values in the boundary rotation group. For a marked toric presentation of a
primitive nef square-zero anticanonical cycle, the action is characterized by
the pullbacks of the realized loops and has trivial kernel.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

open Module (Basis)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "Cnil[" P "]" => Path.centerPartialMap ℂ Path.nil P
local notation "U₀[" P "]" => Path.centerOpen ℂ Path.nil P
local notation "dst(" C "," c ")" =>
  c ≫ Scheme.PartialMap.domainTarget (X := Centers[_]) (Y := Centers[_]) C
local notation "χ[" c "]" => pointsEquiv ℂ _
  (Subtype.mk (Over.Hom.left c) (Over.w c))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L} {E : SkewExchangeMatrix (Fin r)}

local instance instIsDominantRotationLoopXRationalMap (w : inversionFreeLoops E) :
    ((End.asHom w.val).xRationalMap ℂ).IsDominant :=
  Path.instIsDominantXRationalMap ℂ (End.asHom w.val)

local notation "LoopX[" w "]" => Path.xRationalMap ℂ (End.asHom (Subtype.val w))

variable (Q : CompleteToricPresentation i b r L γ)

local notation "Models[" M "," C "]" =>
  HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r])
    (b := b) (hΦ := Q.regular) (T := Q.cycle)
    (origin := Q.origin) (s := Q.rays) (ι := Q.inclusion) (P₁ := M)
    (fun c : Point Centers[r] ↦ χ[c]) C

/-- The Picard pullback along unsigned loop realizations of a fixed marked
presentation defines a unique faithful homomorphism from the opposite group
of independent X maps to the boundary rotations. It suffices to have nodal
models on the initial noncollision open. The reference fiber carrying the
primitive nef square-zero boundary can lie outside this open. -/
theorem existsUnique_picardHom_of_presentation
    (P : ChargeSeed E N)
    (hform : P.form = b.detDualEquiv.toLinearMap)
    (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (M : Point Centers[r] → MarkedSurface ℂ n H XTor[r])
    (models : ∀ c : Point Centers[r], c.left (default : S) ∈ U₀[P] →
      Q.HasNodalModel c (M c))
    {c₀ : Point Centers[r]} (hmodel : Q.HasNodalModel c₀ (M c₀))
    (hD : ∀ c, D[M c].IsEffectiveCartier)
    (hnef : (classOf(hD c₀)).IsNef ℂ ((M c₀).surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ (M c₀).surface classOf(hD c₀) classOf(hD c₀) = 0)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD c₀)))
    (d : ZMod n → L) (hmark : ∀ c j, (M c).boundaryClass (hD c) j = d j) :
    letI := Q.complete.nonempty_cones
    letI := Q.prestable
    letI := Q.neZero
    ∃! f : (ClusterModularGroup ℂ E)ᵐᵒᵖ →* boundaryRotationGroup H d,
      (∀ (w : inversionFreeLoops E)
        {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
        [C.IsOver Centers[r].hom Centers[r].hom]
        (R : GeometricRealization M M C LoopX[w]),
        Models[M,C] →
        rotationInclusion H d (f (op (clusterModularGroupMap ℂ E w))) =
          R.toSignedBoundaryIsometry d hD hmark) ∧ f.ker = ⊥ := by
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  let : IsRationalOver ((M c₀).surface ↘ S) := hmodel.isRationalOver
  have hcan := congrArg Inv.inv (hmodel.canonicalClass (hD c₀))
  have hindex := Q.chargeIndex_ne_zero_of_anticanonical_cycle hmodel (hD c₀) hnef hsq hcan hprim
  have hker : E.matrix.mulVecLin.ker = P.charge.ker := by
    rw [← P.matrix_eq, hform, hcharge]
    exact Fan.ker_chargeExchangeMatrix_rayChargeMap b Q.rays hindex
  have hmodels (x : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P]) :=
    models _ (Path.nil.centerPoint_endpoints_mem_noncollision P hker x).2
  obtain ⟨ρ, ⟨hρ, hpos⟩, -⟩ :=
    existsUnique_signedPicardHom_of_presentation P Q hform hcharge M hmodels
      hmodel hD hnef hsq hcan hprim d hmark
  have hρinj := ρ.ker_eq_bot_iff.mp
    (signedPicardHom_ker_eq_bot_of_presentation Q P hform hcharge M models hD
      hmodel hnef hsq hcan hprim d hmark ρ fun w ↦ (hρ w).2)
  let f := picardRotationHom ρ hpos.ge
  have hf (w : inversionFreeLoops E)
      {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
      [C.IsOver Centers[r].hom Centers[r].hom] (R : GeometricRealization M M C LoopX[w])
      (hR : Models[M,C]) :
      rotationInclusion H d (f (op (clusterModularGroupMap ℂ E w))) =
        R.toSignedBoundaryIsometry d hD hmark := by
    simpa only [f, rotationInclusion_picardRotationHom_apply, MonoidHom.op_apply_apply,
      Function.comp_apply, unop_op, clusterModularGroupInclusion_clusterModularGroupMap]
      using (hρ w.val).2 R hR
  refine ⟨f, ⟨hf, f.ker_eq_bot_iff.mpr ?_⟩, ?_⟩
  · exact picardRotationHom_injective ρ hpos.ge hρinj
  · intro f' hf'
    refine MonoidHom.ext fun g ↦ ?_
    obtain ⟨w, hw⟩ := clusterModularGroupMap_surjective ℂ E g.unop
    rw [← op_unop g, ← hw]
    obtain ⟨R, -, -, hR⟩ := exists_realize_signed_loop (End.asHom w.val) P Q
      hform hcharge M hmodels hmodel hD hnef hsq hprim d hmark
    let C := Path.centerPartialMap ℂ (End.asHom w.val) P
    let : C.IsOver Centers[r].hom Centers[r].hom :=
      Path.instIsOverCenterPartialMapHomSchemeMkStructureMapForallInt (K := ℂ) (End.asHom w.val) P
    let : IsDominant C.hom :=
      Path.instIsDominantHomCenterPartialMap (K := ℂ) (End.asHom w.val) P
    have htargets : Models[M,C] := fun x ↦ by
      have hx : Q.HasNodalModel (dst(C,x)) (M (dst(C,x))) := hR x
      exact hx.nonempty_contractedToricFiber
    exact rotationInclusion_injective H d
      ((hf'.1 w (C := C) R htargets).trans (hf w (C := C) R htargets).symm)

end QPainleve.SignedClusterModularGroup.GeometricRealization

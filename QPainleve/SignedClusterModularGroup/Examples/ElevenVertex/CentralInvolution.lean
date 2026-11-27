/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Examples.ElevenVertex.PicardAction
public import QPainleve.SignedClusterModularGroup.Examples.ElevenVertex.Presentation
public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.PicardAction

import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Reference
import QPainleve.SignedClusterModularGroup.SignExtension
import TauCeti.LinearAlgebra.Matrix.Dual

/-!
# The central sign involution of the eleven-vertex seed

The ordered triangle blowups and the two nodal blowdowns give a reference
fiber in the original seed basis. The signed Picard equivalence sends
`involutionWord` to the identity isometry with negative branch sign.
The nodal Picard identification supplies the comparison for this reference
fiber and all its loop realizations.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory MulOpposite Multiplicative Quiver
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open QPainleve.SignedClusterModularGroup QPainleve.SignedClusterModularGroup.GeometricRealization
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric TauCeti.Toric.Fan

namespace QPainleve.ElevenVertex

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀] [Uncountable k₀]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "Centers" => Over.mk (structureMap k₀ (Fin 11 → ℤ))
local notation "XTor" => scheme k₀ (Fin 11 →₀ ℤ)
local notation "b" => Pi.basisFun ℤ (Fin 2)
local notation "Φ" => Fan.projectiveSpace b (isIntegralLattice_intCast 2)
local notation "planeLattice" => AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin 2)
local notation "cartier[" M "]" => MarkedSurface.isEffectiveCartier_boundaryIdeal M
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "χ[" c "]" => pointsEquiv k₀ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "params[" c "]" => (fun j : Fin 11 ↦ χ[c] (ofAdd (Pi.single j 1)))
local notation "Γ" => SignedClusterModularGroup k₀ exchangeMatrix

/-- The signed Picard identification for the ordered plane model with center
parameters `u`. The reference fiber uses the original lattice frame and the
eleven prescribed rays. -/
structure PlanePicardIdentification (u : Fin 11 → k₀ˣ) where
  /-- The rank of the reference Picard lattice. -/
  rank : ℕ
  /-- The reference intersection form in free integral coordinates. -/
  form : LinearMap.BilinForm ℤ (Fin rank → ℤ)
  /-- The ordered plane presentation in the original frame. -/
  presentation : CompleteToricPresentation k₀ planeLattice b 11 (Fin rank → ℤ) Empty
  /-- The center of the reference fiber. -/
  center : Point Centers
  /-- The marked reference surface and its rational X evaluation. -/
  reference : MarkedSurface k₀ 1 form XTor
  /-- The center has the prescribed parameters in the original frame. -/
  params_eq : params[center] = u
  /-- The presentation contains the standard plane fan and the prescribed labeled rays. -/
  rays_eq : ∃ hfan : presentation.fan = Φ, hfan ▸ presentation.rays = planeCenterRay
  /-- The Picard equivalence, its evaluation on loops, and its central involution. -/
  identification : InvolutionPicardIdentification presentation center reference

variable [NeZero (2 : k₀)]

/-- Every choice of ordered center parameters gives the marked one-component plane
model and its signed Picard equivalence in the original lattice frame. -/
theorem nonempty_planePicardIdentification (u : Fin 11 → k₀ˣ) :
    Nonempty (PlanePicardIdentification u) := by
  obtain ⟨W, s, hs, D, hD, _, hpre, _, _, A, U, R, a, _, hW, hproj, hrat, _, _, _,
    hprim, hnef, hsq, hR, hbase, hker, _, _, _, _⟩ := exists_eleven_vertex_toric_presentation u
  let : W.Over S := ⟨s⟩
  let : SmoothOfRelativeDimension 2 (W ↘ S) := hs
  let : IsIntegral W := hW
  let : W.IsProjectiveOver k₀ := hproj
  let : IsRationalOver (W ↘ S) := hrat
  let : PrestableFamily (D.subscheme ↘ S) := hpre
  let : (Iso.refl D.subscheme).hom.IsOver S :=
    inferInstanceAs ((𝟙 D.subscheme : D.subscheme ⟶ D.subscheme).IsOver S)
  let A' := (Iso.refl D.subscheme).mapNodalCycleNumbering A
    (q := (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus))
  let : Module.Free ℤ (Additive (LineBundleClass W)) := W.free_picard_of_isRationalOver k₀
  let : Module.Finite ℤ (Additive (LineBundleClass W)) := W.finite_picard_of_isRationalOver k₀
  let B := Chow.intersectionBilinForm k₀ W
  let e := (Module.finBasis ℤ (Additive (LineBundleClass W))).equivFun.symm
  let μ := (B.isometryEquivOfCompLinearEquiv e).symm
  obtain ⟨A'', ⟨Q, c, f, hm⟩, _, hparams, hrays⟩ :=
    exists_marked_reference_fiber_of_ordered_towers_fixed_basis
      (isRegular_projectiveSpace b (isIntegralLattice_intCast 2))
      (isComplete_projectiveSpace b (isIntegralLattice_intCast 2))
      planeCenterRay u hR a hbase hker hD A' μ
  let M := MarkedSurface.ofBoundary D A'' μ f
  have hclass : classOf(cartier[M]) = classOf(hD) :=
    MarkedSurface.ofBoundary_boundaryIdeal_class D A'' μ f cartier[M] hD
  obtain ⟨p, hp⟩ := hm.exists_isNodalContraction cartier[M]
  have hE : exchangeMatrix.matrix =
      chargeExchangeMatrix (b).detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays) := by
    obtain ⟨hfan, hr⟩ := hrays
    have hcharge {F G : Fan planeLattice} (h : F = G) (rays : Fin 11 → F.Ray) :
        Fan.rayChargeMap (h ▸ rays : Fin 11 → G.Ray) = Fan.rayChargeMap rays := by
      subst G
      rfl
    rw [← hcharge hfan Q.rays, hr, rayChargeMap_planeCenterRay,
      exchangeMatrix_eq_chargeExchangeMatrix]
  obtain ⟨I⟩ := nonempty_involutionPicardIdentification_of_nodal_contraction p hp hE
    (hclass.symm ▸ hprim) (hclass.symm ▸ hnef) (hclass.symm ▸ hsq)
  exact ⟨⟨_, _, Q, c, M, hparams, hrays, I⟩⟩

/-- The eleven-vertex involution commutes with every independent signed cluster X map. -/
theorem involutionWord_mem_center :
    signedClusterModularGroupMap k₀ exchangeMatrix (End.of involutionWord) ∈ Subgroup.center Γ := by
  obtain ⟨I⟩ := nonempty_planePicardIdentification (k₀ := k₀) 1
  have hn : (1 : ℕ) ≤ 2 := by decide
  rw [(eq_picardCentralInvolution_iff I.identification.signedEquiv hn _).mpr
    I.identification.signedEquiv_apply_involutionWord]
  exact picardCentralInvolution_mem_center I.identification.signedEquiv hn

end QPainleve.ElevenVertex

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

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers" => Over.mk (structureMap ℂ (Fin 11 → ℤ))
local notation "XTor" => scheme ℂ (Fin 11 →₀ ℤ)
local notation "b" => Pi.basisFun ℤ (Fin 2)
local notation "Φ" => Fan.projectiveSpace b (isIntegralLattice_intCast 2)
local notation "planeLattice" => AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin 2)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "cartier[" M "]" => MarkedSurface.isEffectiveCartier_boundaryIdeal M
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "params[" c "]" => (fun j : Fin 11 ↦ χ[c] (ofAdd (Pi.single j 1)))
local notation "Γ" => SignedClusterModularGroup ℂ exchangeMatrix
local notation "eval[" w "]" => op (signedClusterModularGroupMap ℂ exchangeMatrix (End.of w))

/-- The signed Picard identification for the ordered plane model with center
parameters `u`. The reference fiber uses the original lattice frame and the
eleven prescribed rays. -/
structure PlanePicardIdentification (u : Fin 11 → ℂˣ) where
  /-- The rank of the reference Picard lattice. -/
  rank : ℕ
  /-- The reference intersection form in free integral coordinates. -/
  form : LinearMap.BilinForm ℤ (Fin rank → ℤ)
  /-- The ordered plane presentation in the original frame. -/
  presentation : CompleteToricPresentation planeLattice b 11 (Fin rank → ℤ) Empty
  /-- The center of the reference fiber. -/
  center : Point Centers
  /-- The marked reference surface and its rational X evaluation. -/
  reference : MarkedSurface ℂ 1 form XTor
  /-- The center has the prescribed parameters in the original frame. -/
  params_eq : params[center] = u
  /-- The presentation contains the standard plane fan and the prescribed labeled rays. -/
  rays_eq : ∃ hfan : presentation.fan = Φ, hfan ▸ presentation.rays = planeCenterRay
  /-- The Picard equivalence, its evaluation on loops, and its central involution. -/
  identification : InvolutionPicardIdentification presentation center reference

/-- Every choice of ordered center parameters gives the marked one-component plane
model and its signed Picard equivalence in the original lattice frame. -/
theorem nonempty_planePicardIdentification (u : Fin 11 → ℂˣ) :
    Nonempty (PlanePicardIdentification u) := by
  obtain ⟨W, s, hs, D, hD, _, hpre, _, _, A, U, R, a, _, hW, hproj, hrat, _, _, _,
    hprim, hnef, hsq, hR, hbase, hker, _, _, _, _⟩ := exists_eleven_vertex_toric_presentation u
  let : W.Over S := ⟨s⟩
  let : SmoothOfRelativeDimension 2 (W ↘ S) := hs
  let : IsIntegral W := hW
  let : W.IsProjectiveOver ℂ := hproj
  let : IsRationalOver (W ↘ S) := hrat
  let : PrestableFamily (D.subscheme ↘ S) := hpre
  let : (Iso.refl D.subscheme).hom.IsOver S :=
    inferInstanceAs ((𝟙 D.subscheme : D.subscheme ⟶ D.subscheme).IsOver S)
  let A' := (Iso.refl D.subscheme).mapNodalCycleNumbering A
    (q := (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus))
  let : Module.Free ℤ (Additive (LineBundleClass W)) := W.free_picard_of_isRationalOver ℂ
  let : Module.Finite ℤ (Additive (LineBundleClass W)) := W.finite_picard_of_isRationalOver ℂ
  let B := Chow.intersectionBilinForm ℂ W
  let e := (Module.finBasis ℤ (Additive (LineBundleClass W))).equivFun.symm
  let μ := (B.isometryEquivOfCompLinearEquiv e).symm
  obtain ⟨A'', ⟨Q, c, f, hm⟩, _, hparams, hrays⟩ :=
    exists_marked_reference_fiber_of_ordered_towers_fixed_basis
      (isRegular_projectiveSpace b (isIntegralLattice_intCast 2))
      (isComplete_projectiveSpace b (isIntegralLattice_intCast 2))
      planeCenterRay u hR a hbase hker hD A' μ
  let M := MarkedSurface.ofBoundary D A'' μ f
  have hclass : classOf(cartier[M]) = classOf(hD) :=
    congrArg Inv.inv (LineBundleClass.mk_toInvertibleSheaf_congr cartier[M] hD
      (MarkedSurface.ofBoundary_ker ..))
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

/-- For any ordered center parameters, the plane model gives a marked one-component
reference fiber whose faithful signed Picard action sends the specified odd loop
to the central sign element. Its values on loops are the marked pullbacks of their
geometric realizations, with sign given by inversion parity. -/
theorem exists_eleven_vertex_signedPicardHom (u : Fin 11 → ℂˣ) :
    ∃ (L : Type) (_ : AddCommGroup L) (H : LinearMap.BilinForm ℤ L)
      (Q : CompleteToricPresentation planeLattice b 11 L Empty)
      (c : Point Centers) (M : Point Centers → MarkedSurface ℂ 1 H XTor)
      (hD : ∀ a, D[M a].IsEffectiveCartier),
      params[c] = u ∧ (∃ hfan : Q.fan = Φ, hfan ▸ Q.rays = planeCenterRay) ∧
      ∃ (hfamily : ∀ a, Q.HasNodalModel a (M a) ∧
          (M a).boundaryClass (hD a) = (M c).boundaryClass (hD c))
        (ρ : Γᵐᵒᵖ →* signedBoundaryIsometryGroup H ((M c).boundaryClass (hD c))),
        Function.Injective ρ ∧
        ρ eval[involutionWord] = centralSign H ((M c).boundaryClass (hD c)) (by decide) ∧
        ∀ (w : Word exchangeMatrix exchangeMatrix), sign H ((M c).boundaryClass (hD c))
            (ρ eval[w]) = (-1 : ℤˣ) ^ w.inversionCount ∧
          ∀ {C : (Centers).left.PartialMap (Centers).left} [IsDominant C.hom]
            [C.IsOver (Centers).hom (Centers).hom]
            (R : GeometricRealization M M C (w.xRationalMap ℂ)),
            ρ eval[w] = R.toSignedBoundaryIsometry ((M c).boundaryClass (hD c)) hD
              (fun a j ↦ congrFun (hfamily a).2 j) := by
  obtain ⟨⟨rank, H, Q, c, M₀, hparams, hrays, I⟩⟩ := nonempty_planePicardIdentification u
  rcases I with ⟨M, hMc, hmodels, hmark, Θ, hz, hsign, hΘ⟩
  subst M₀
  refine ⟨Fin rank → ℤ, inferInstance, H, Q, c, M, (fun a ↦ cartier[M a]), hparams, hrays,
    fun a ↦ ⟨hmodels a, funext (hmark a)⟩, Θ.toMonoidHom, Θ.injective, hz, fun w ↦ ⟨?_, ?_⟩⟩
  · simpa only [SignedBoundaryIsometryGroup.sign_apply, MulEquiv.coe_toMonoidHom] using hsign w
  · intro C _ _ R
    exact hΘ w R

/-- The eleven-vertex involution commutes with every independent signed cluster X map. -/
theorem involutionWord_mem_center :
    signedClusterModularGroupMap ℂ exchangeMatrix (End.of involutionWord) ∈ Subgroup.center Γ := by
  obtain ⟨I⟩ := nonempty_planePicardIdentification 1
  let z := signedClusterModularGroupMap ℂ exchangeMatrix (End.of involutionWord)
  have hz : I.identification.signedEquiv (op z) ∈ Subgroup.center _ := by
    dsimp only [z]
    rw [I.identification.signedEquiv_apply_involutionWord]
    exact centralSign_mem_center I.form (I.reference.boundaryClass cartier[I.reference]) (by decide)
  have hop : op z ∈ Subgroup.center Γᵐᵒᵖ :=
    (MulEquivClass.apply_mem_center_iff I.identification.signedEquiv).mp hz
  exact ((Subgroup.centerToMulOpposite Γ).symm ⟨_, hop⟩).property

end QPainleve.ElevenVertex

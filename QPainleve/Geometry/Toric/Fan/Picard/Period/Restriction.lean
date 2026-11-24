/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Picard
public import QPainleve.Geometry.Toric.Fan.Picard.Orthogonal

/-!
# Boundary restriction of toric charge classes

The inverse charge comparison represents a line bundle on the original surface.
Pulling its restriction back to the fixed toric boundary gives the restriction of
the toric part tensored with the center ideals to the powers given by the charge relation.
The toric part is determined by the charge relation and the fan, so it cancels when
comparing two choices of center parameters.

This gives the restriction calculation behind the period formula in Gross, Hacking
and Keel, *Moduli of surfaces with an anti-canonical cycle*, Proposition 2.9.
The coordinates come from `exists_picardBoundaryOrthogonalEquivChargeKernel_symm_marking`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}

local notation "Dtor" => Φ.boundaryIdeal inferInstance
local notation "Pic(" S ")" => Additive (LineBundleClass S)

variable {X Y : Scheme} {D : X.IdealSheafData} {d : ℕ} {T : QPainleve.BlowupTower X d Y}
  (J : Fin n →
    {I : (Φ.boundaryIdeal inferInstance).subscheme.IdealSheafData // I.IsEffectiveCartier})
  (e : Y ≅ (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι J).1)

local notation "model" => alongBoundary (subschemeι Dtor) J
local notation "boundaryι" => WithBoundary.boundaryι (Sigma.snd model)

variable (hD : ((D.comap T.toBase).comap e.inv).support =
  (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι J).2.boundaryι.ker.support)

/-- In a toric presentation, the projection from the internal blowup model to the
original surface maps the fixed reduced toric boundary into the original boundary. -/
def toricBoundaryToBase : (Dtor).subscheme ⟶ D.subscheme :=
  IsClosedImmersion.lift D.subschemeι (boundaryι ≫ e.inv ≫ T.toBase) (by
    have : IsReduced (Dtor).subscheme := by
      rw [Φ.boundaryIdeal_def]
      infer_instance
    rw [ker_subschemeι]
    refine (le_support_iff_le_vanishingIdeal.mp le_rfl).trans
      (vanishingIdeal_le_ker_of_range_subset _ ?_)
    rintro _ ⟨y, rfl⟩
    have hy : boundaryι y ∈ ((boundaryι).ker.support : Set (model).1) := by
      rw [(boundaryι).support_ker]
      exact subset_closure (Set.mem_range_self y)
    simpa only [← hD, support_comap, Closeds.coe_preimage, Set.mem_preimage,
      Scheme.Hom.comp_apply] using hy)

/-- The map on boundaries commutes with their embeddings in the two surfaces. -/
@[reassoc (attr := simp)]
theorem toricBoundaryToBase_comp_subschemeι :
    toricBoundaryToBase J e hD ≫ D.subschemeι = boundaryι ≫ e.inv ≫ T.toBase :=
  IsClosedImmersion.lift_fac _ _ _

/-- The toric boundary projection is over any base for which the presentation
identification commutes with the two projections to that base. -/
theorem isOver_toricBoundaryToBase {X Y Z : Scheme} [X.Over Z]
    [Φ.algebraicRealization.Over Z]
    {D : X.IdealSheafData} {d : ℕ} {T : QPainleve.BlowupTower X d Y}
    (J : Fin n → {I : (Dtor).subscheme.IdealSheafData // I.IsEffectiveCartier})
    (e : Y ≅ (alongBoundary (subschemeι Dtor) J).1)
    (he : e.inv ≫ T.toBase ≫ (X ↘ Z) =
      (alongBoundary (subschemeι Dtor) J).2.toTower.toBase ≫ (Φ.algebraicRealization ↘ Z))
    (hD : ((D.comap T.toBase).comap e.inv).support =
      (alongBoundary (subschemeι Dtor) J).2.boundaryι.ker.support) :
    (toricBoundaryToBase J e hD).IsOver Z := by
  constructor
  rw [D.over_eq_subschemeι_comp, toricBoundaryToBase_comp_subschemeι_assoc, he,
    WithBoundary.boundaryι_toBase_assoc, ← (Dtor).over_eq_subschemeι_comp]

local notation "Z" => Φ.algebraicRealization

variable [Φ.algebraicRealization.IsProjectiveOver ℂ]
  (hΦ : Φ.IsRegular) (hdim : Module.finrank ℤ N = 2)
  (s : Fin n → Φ.Ray) (m : Fin n → N →+ ℤ)
  (hm : ∀ j, m j (s j).primitiveGenerator = 0) (hprim : ∀ j, Function.Surjective (m j))
  (c : Fin n → ℂˣ)
  (hJ : ∀ j, (J j).val = ((s j).binomialCenterOnBoundary hdim (hm j) (hprim j) (c j)).ker)
  [X.Over (Spec (.of ℂ))] [X.IsProjectiveOver ℂ] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm ℂ X)]
  (hT : IsNodalBoundaryTower D (X ↘ Spec (.of ℂ)) (𝟙 X) T)
  (he : e.inv ≫ T.toBase ≫ (X ↘ Spec (.of ℂ)) =
    (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι J).2.toTower.toBase ≫
      (Φ.algebraicRealization ↘ Spec (.of ℂ)))

local notation "chargeEquiv" =>
  picardBoundaryOrthogonalEquivChargeKernel hΦ hdim s m hm hprim c J hJ hT e he hD

include hJ hT he hD in
/-- A charge relation `x` gives a boundary restriction on the original surface.
After pullback to the fixed toric boundary, it is the toric part of the marking
restricted to that boundary, tensored with each center ideal line bundle to the
power `x j`. The toric part `H` is specified by its degrees on the ray divisors. -/
theorem pullback_toricBoundaryToBase_picardBoundaryOrthogonalEquivChargeKernel_symm
    (x : (rayChargeMap s).ker) (H : Pic(Z))
    (hH : ∀ v : Φ.Ray → ℤ, Chow.classIntersectionNumber ℂ Z
      (Φ.rayDivisorToPicard hΦ v).toMul H.toMul = ∑ j, v (s j) * (x : Fin n → ℤ) j) :
    pullback (toricBoundaryToBase J e hD) (pullback D.subschemeι ((chargeEquiv).symm x).val.toMul) =
      pullback (subschemeι Dtor) H.toMul *
        ∏ j, (LineBundleClass.mk (J j).property.toInvertibleSheaf) ^ ((x : Fin n → ℤ) j) := by
  obtain ⟨G, hMarking, hDegree⟩ :=
    exists_picardBoundaryOrthogonalEquivChargeKernel_symm_marking
      hΦ hdim s m hm hprim c J hJ hT e he hD x
  have hEq := (hDegree H).mp hH
  subst G
  rw [pullback_comp, toricBoundaryToBase_comp_subschemeι, ← pullback_comp, ← hMarking,
    pullback_picardHom_alongBoundary]
  simp only [Pi.neg_apply, neg_neg]

end TauCeti.Toric.Fan

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Quotient
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Canonical
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
public import QPainleve.AlgebraicGeometry.Chow.CurveCone

import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Chow.NegativeCurve
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.ClosedImmersion
import QPainleve.AlgebraicGeometry.Morphisms.ClosedImmersion.IsoLocus
import QPainleve.AlgebraicGeometry.Morphisms.Pullback.IsoLocus
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Internal curves under nodal blowups

An integral curve disjoint from the reduced total boundary descends isomorphically to
an integral curve disjoint from the original boundary. Conversely, each curve disjoint
from the original boundary lifts isomorphically. The curve class upstairs is the Picard
pullback, so the comparison preserves self-intersection. This lets one transport the
absence of internal curves of square `-2` to a nodal auxiliary model, as in the
proof of Theorem 4.7 of [Gross, Hacking and Keel][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S4.Thmtheorem7
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsNodalBoundaryTower

variable {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y} {D : X.IdealSheafData}
  {S : Scheme.{u}} {f : X ⟶ S}

local notation "U" => (D.support.compl : X.Opens)
local notation "π" => T.toBase

/-- The complement of the original boundary is contained in the isomorphism locus of
the projection of a nodal blowup tower. -/
theorem boundaryCompl_le_isoLocus (hT : IsNodalBoundaryTower D f (𝟙 X) T) :
    U ≤ (π).isoLocus := by
  have h := hT.isIso_morphismRestrict_boundaryCompl
  rw [Scheme.IdealSheafData.comap_id] at h
  exact (π).le_isoLocus_iff.mpr h

/-- A closed subscheme disjoint from the reduced total boundary maps isomorphically
onto a closed subscheme disjoint from the original boundary. Its ideal is the pullback
of the image ideal. -/
theorem isClosedImmersion_comp_and_ker_eq_comap (hT : IsNodalBoundaryTower D f (𝟙 X) T)
    [IsLocallyNoetherian X] {C : Scheme.{u}} (i : C ⟶ Y) [IsClosedImmersion i]
    (hi : Disjoint (Set.range i) (D.comap π).support) :
    IsClosedImmersion (i ≫ π) ∧ (i ≫ π).ker.comap π = i.ker := by
  have hr : Set.range (i ≫ π) ⊆ U := by
    rintro _ ⟨x, rfl⟩
    exact fun hx ↦ Set.disjoint_left.mp hi (Set.mem_range_self x) (by
      simpa only [support_comap, Closeds.coe_preimage, Set.mem_preimage, Scheme.Hom.comp_apply]
        using hx)
  have hU : Set.range (i ≫ π) ⊆ (π).isoLocus := hr.trans hT.boundaryCompl_le_isoLocus
  have := T.isProper_toBase
  have hj := i.isClosedImmersion_comp_of_range_subset_isoLocus π
    (i ≫ π).isClosedMap.isClosed_range hU
  exact ⟨hj, (ker_eq_comap_of_isPullback _
    ((π).isPullback_of_isIso_of_range_subset_isoLocus i (𝟙 C) (i ≫ π) (by simp) hU)).symm⟩

/-- A closed immersion disjoint from the original boundary lifts to a closed immersion
from the same scheme. The lift and the original immersion form a pullback square. -/
theorem exists_isPullback_of_disjoint_boundary (hT : IsNodalBoundaryTower D f (𝟙 X) T)
    {C : Scheme.{u}} (j : C ⟶ X) [IsClosedImmersion j]
    (hj : Disjoint (Set.range j) D.support) :
    ∃ i : C ⟶ Y, IsClosedImmersion i ∧ IsPullback i (𝟙 C) π j := by
  have hU : Set.range j ⊆ Set.range (Scheme.Opens.ι U) := by
    rw [Scheme.Opens.range_ι]
    exact fun _ hx ↦ fun hy ↦ Set.disjoint_left.mp hj hx hy
  let j' := IsOpenImmersion.lift (Scheme.Opens.ι U) j hU
  have : IsIso (π ∣_ U) := (π).le_isoLocus_iff.mp hT.boundaryCompl_le_isoLocus
  let i := (j' ≫ inv (π ∣_ U)) ≫ (π ⁻¹ᵁ U).ι
  have hcomm : i ≫ π = j := by
    dsimp only [i]
    rw [Category.assoc, ← morphismRestrict_ι π U]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, IsOpenImmersion.lift_fac, j']
  have hpb := (π).isPullback_of_isIso_of_range_subset_isoLocus i (𝟙 C) j
    (by rw [hcomm, Category.id_comp]) (by
      rw [Scheme.Opens.range_ι] at hU
      exact hU.trans hT.boundaryCompl_le_isoLocus)
  exact ⟨i, MorphismProperty.of_isPullback hpb.flip inferInstance, hpb⟩

variable (k : Type u) [Field k] [IsAlgClosed k] [X.Over (Spec (.of k))]
  [X.IsProjectiveOver k] [IsIntegral X] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "f₀" => (X ↘ Spec (CommRingCat.of k))

/-- Nodal blowups preserve the existence of an integral curve of square `-2`
disjoint from the boundary. The boundary upstairs is the reduced total boundary,
whose support is the support of the inverse-image ideal. -/
theorem exists_internal_minus_two_curve_iff (hT : IsNodalBoundaryTower D f₀ (𝟙 X) T) :
    let : Y.Over (Spec (.of k)) := ⟨π ≫ f₀⟩
    (∃ (C : Scheme.{u}) (i : C ⟶ Y) (_ : IsClosedImmersion i) (_ : IsIntegral C)
        (hi : i.ker.IsEffectiveCartier),
      topologicalKrullDim C = 1 ∧ Disjoint (Set.range i) (D.comap π).support ∧
        Chow.classIntersectionNumber k Y (mk hi.toInvertibleSheaf)⁻¹
          (mk hi.toInvertibleSheaf)⁻¹ = -2) ↔
    (∃ (C : Scheme.{u}) (j : C ⟶ X) (_ : IsClosedImmersion j) (_ : IsIntegral C)
        (hj : j.ker.IsEffectiveCartier),
      topologicalKrullDim C = 1 ∧ Disjoint (Set.range j) D.support ∧
        Chow.classIntersectionNumber k X (mk hj.toInvertibleSheaf)⁻¹
          (mk hj.toInvertibleSheaf)⁻¹ = -2) := by
  let : Y.Over (Spec (.of k)) := ⟨π ≫ f₀⟩
  have : IsNoetherian X := isNoetherian_of_finiteType f₀
  have : IsIntegral Y := hT.isClosedPointTower.isIntegral f₀
  have : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
    hT.isClosedPointTower.smoothOfRelativeDimension f₀
  have : Smooth f₀ := SmoothOfRelativeDimension.smooth 2 f₀
  have : Smooth (Y ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsRegular X := IsRegular.of_smooth f₀
  have : IsRegular Y := IsRegular.of_smooth (Y ↘ Spec (.of k))
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f₀ (n := 2)
  have hY := topologicalKrullDim_eq_of_smoothOfRelativeDimension (Y ↘ Spec (.of k)) (n := 2)
  have hsq {C : Scheme.{u}} {i : C ⟶ Y} {j : C ⟶ X}
      (hi : i.ker.IsEffectiveCartier) (hj : j.ker.IsEffectiveCartier)
      (he : j.ker.comap π = i.ker) :
      Chow.classIntersectionNumber k Y (mk hi.toInvertibleSheaf)⁻¹
        (mk hi.toInvertibleSheaf)⁻¹ =
      Chow.classIntersectionNumber k X (mk hj.toInvertibleSheaf)⁻¹
        (mk hj.toInvertibleSheaf)⁻¹ := by
    have hclass := hj.pullback_mk_toInvertibleSheaf (g := π) (he.symm ▸ hi)
    rw [mk_toInvertibleSheaf_congr _ hi he] at hclass
    rw [← hclass, ← pullback_inv, hT.isClosedPointTower.classIntersectionNumber_pullback k]
  have hdisjComp {C : Scheme.{u}} (i : C ⟶ Y) :
      Disjoint (Set.range (i ≫ π)) D.support ↔ Disjoint (Set.range i) (D.comap π).support := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.disjoint_image_left,
      support_comap, Closeds.coe_preimage]
  constructor
  · rintro ⟨C, i, hi, hC, hiC, hdim, hdisj, hneg⟩
    obtain ⟨hj, hker⟩ := hT.isClosedImmersion_comp_and_ker_eq_comap i hdisj
    have hjC := (i ≫ π).isEffectiveCartier_ker_of_isRegular_of_dim_eq_two k hX hdim
    exact ⟨C, i ≫ π, hj, hC, hjC, hdim, (hdisjComp i).mpr hdisj,
      (hsq hiC hjC hker).symm.trans hneg⟩
  · rintro ⟨C, j, hj, hC, hjC, hdim, hdisj, hneg⟩
    obtain ⟨i, hi, hpb⟩ := hT.exists_isPullback_of_disjoint_boundary j hdisj
    have hiC := i.isEffectiveCartier_ker_of_isRegular_of_dim_eq_two k hY hdim
    have hcomm : i ≫ π = j := by simpa only [Category.id_comp] using hpb.w
    exact ⟨C, i, hi, hC, hiC, hdim, (hdisjComp i).mp (hcomm.symm ▸ hdisj),
      (hsq hiC hjC (ker_eq_comap_of_isPullback j hpb).symm).trans hneg⟩

/-- For an anticanonical pair, the real Picard criterion excluding internal
`(-2)`-curves is invariant under nodal blowups. This is the criterion on
prime classes used in the nef cone of the auxiliary pair. -/
theorem forall_realPrimeDivisorClass_self_ne_neg_two_iff
    [Scheme.IsRationalOver f₀]
    (hT : IsNodalBoundaryTower D f₀ (𝟙 X) T)
    (hD : D.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ f₀))
    (hcan : mk hD.toInvertibleSheaf = mk (QPainleve.canonicalBundle k X 2)) :
    letI : IsNoetherian X := isNoetherian_of_finiteType f₀
    letI : Y.Over (Spec (.of k)) := ⟨π ≫ f₀⟩
    letI : Y.IsProjectiveOver k := T.isProjectiveOver k
    letI : IsIntegral Y := hT.isClosedPointTower.isIntegral f₀
    letI : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
      hT.isClosedPointTower.smoothOfRelativeDimension f₀
    (∀ p : CodimensionOnePoint Y, (p : Y) ∉ (D.comap π).support →
      Chow.realIntersectionBilinForm k Y (Chow.realPrimeDivisorClass k p)
        (Chow.realPrimeDivisorClass k p) ≠ -2) ↔
    (∀ q : CodimensionOnePoint X, (q : X) ∉ D.support →
      Chow.realIntersectionBilinForm k X (Chow.realPrimeDivisorClass k q)
        (Chow.realPrimeDivisorClass k q) ≠ -2) := by
  let : Y.Over (Spec (.of k)) := ⟨π ≫ f₀⟩
  have : IsNoetherian X := isNoetherian_of_finiteType f₀
  have : Y.IsProjectiveOver k := T.isProjectiveOver k
  have : IsIntegral Y := hT.isClosedPointTower.isIntegral f₀
  have : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
    hT.isClosedPointTower.smoothOfRelativeDimension f₀
  have : Scheme.IsRationalOver (Y ↘ Spec (.of k)) := hT.isClosedPointTower.isRationalOver f₀
  let R := (D.comap π).radical
  have hR : R.IsEffectiveCartier := (hT.radical_comap_toBase hD hN).1
  have hcanR : mk hR.toInvertibleSheaf = mk (QPainleve.canonicalBundle k Y 2) :=
    (hT.canonicalClass_radical_comap_toBase_iff hD hN).mpr hcan
  have hX := Chow.exists_realPrimeDivisorClass_self_eq_neg_two_iff k hD hcan
  have hY := Chow.exists_realPrimeDivisorClass_self_eq_neg_two_iff k hR hcanR
  simp only [R, support_radical] at hY
  simpa only [not_exists, not_and] using
    (hY.trans ((hT.exists_internal_minus_two_curve_iff k).trans hX.symm)).not

end QPainleve.BlowupTower.IsNodalBoundaryTower

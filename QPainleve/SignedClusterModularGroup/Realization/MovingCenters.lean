/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Presentation

import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Numbering
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Canonical
import QPainleve.AlgebraicGeometry.Curves.Node.Reindex
import QPainleve.AlgebraicGeometry.IdealSheaf.Image.Over
import QPainleve.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import QPainleve.Geometry.Toric.Fan.Boundary.Canonical
import QPainleve.Geometry.Toric.Fan.Logarithmic.InternalBlowup
import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Marking
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.SignedClusterModularGroup.Realization.Boundary

/-!
# Marking a nodal contraction after moving the centers

In two ordered blowup models with the same contracted rays, the pullbacks from
their nodal contractions occupy the same orthogonal complement in the auxiliary
Picard lattice. The surviving origin fixes the rotation of the descended boundary
numbering. These comparisons keep the marking and the evaluation in the fixed
coordinates of the presentation. The construction uses
`Fan.contractedPicardMarkingOfRaySet` and
`IsClosedPointTower.exists_numbering_of_anticanonical_boundary_tower_blowdown_of_iso`.
-/

public section

open AlgebraicGeometry CategoryTheory Additive Multiplicative
open QPainleve.BlowupTower QPainleve.CharacterTorus
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData LinearMap.BilinForm

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

open GeometricRealization (Point)

local notation "SpecC" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "centers[" c "]" => (fun j ↦ χ[c] (ofAdd (Pi.single j 1)))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L}
  (Q : CompleteToricPresentation i b r L γ)
  {c d : Point Centers[r]} {M : MarkedSurface ℂ n H XTor[r]}

local instance instNonemptyMovingCentersCones : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance instNeZeroMovingCentersLength : NeZero Q.length := Q.neZero
local instance instPrestableMovingCentersBoundary :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ SpecC) :=
  Q.prestable

local notation "ToricBoundary" => subscheme (Fan.boundaryIdeal Q.fan Q.complete.nonempty_cones)
local notation "A[" c "]" => Fan.internalBlowupTower b Q.rays centers[c]
local notation "R[" c "]" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd (A[c])))

variable {X Y : Scheme} [X.Over SpecC] [IsIntegral X] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ SpecC)] {E : X.IdealSheafData}
  {l : ℕ} {U : BlowupTower X l Y}
  (hU : IsNodalBoundaryTower E (X ↘ SpecC) (𝟙 X) U)
  (e : (Fan.internalBlowupTower b Q.rays centers[d]).1 ≅ Y)
  (he : e.hom ≫ U.toBase ≫ (X ↘ SpecC) =
    (Fan.internalBlowupTower b Q.rays centers[d]).2.toTower.toBase ≫
      Q.fan.algebraicRealizationStructureMap)
  (hE : (E.comap (e.hom ≫ U.toBase)).support =
    (Fan.internalBlowupTower b Q.rays centers[d]).2.boundaryι.ker.support)

local notation "proj" => (e.hom ≫ U.toBase)
local notation "Pair" =>
  Arrow.mk (Over.homMk (U := Over.mk (E.subscheme ↘ SpecC)) (V := Over.mk (X ↘ SpecC))
    E.subschemeι (Eq.symm (Scheme.IdealSheafData.over_eq_subschemeι_comp (S := SpecC) E)))
local notation "μ[" c "]" => Fan.internalBlowupPicardMarking b Q.rays centers[c] Q.regular

variable (p : ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c] M)
  {W : Scheme} {m : ℕ} {T : BlowupTower M.surface m W}
  (hT : IsNodalBoundaryTower D[M] (M.surface ↘ SpecC) (𝟙 M.surface) T)
  (a : W ≅ (Fan.internalBlowupTower b Q.rays centers[c]).1) (hp : p.projection = a.inv ≫ T.toBase)

local notation "prime[" c "," ρ "]" =>
  Fan.internalBlowupBoundaryPrimeEquiv Q.regular b Q.rays centers[c] ρ

include hU he hE hT a hp in
/-- The fixed auxiliary Picard inclusion is realized by an isometry on a second
contraction that contracts the same strict boundary rays as the reference fiber. -/
private theorem exists_marking_of_same_contracted_rays
    (hrays : ∀ ρ : Q.fan.Ray,
      proj (prime[d,ρ]).val ∈ E.boundaryPrimes ↔
        p.projection (prime[c,ρ]).val ∈ D[M].boundaryPrimes) :
    ∃ g : H.IsometryEquiv (Chow.intersectionBilinForm ℂ X),
      ∀ a : L, (μ[d]).symm (Additive.ofMul (LineBundleClass.pullback proj (g a).toMul)) =
        Q.inclusion a := by
  let : Q.fan.algebraicRealization.IsProjectiveOver ℂ :=
    Q.fan.isProjectiveOver_algebraicRealization_of_isComplete Q.regular Q.complete b
  let : SmoothOfRelativeDimension 2 (M.surface ↘ SpecC) := M.smooth
  let : M.surface.IsProjectiveOver ℂ := M.projective
  have hc : a.symm.hom ≫ T.toBase ≫ (M.surface ↘ SpecC) =
      toBase (WithBoundary.toTower (Sigma.snd (A[c]))) ≫ Q.fan.algebraicRealizationStructureMap :=
    calc
      _ = p.projection ≫ (M.surface ↘ SpecC) := congrArg (· ≫ (M.surface ↘ SpecC)) hp.symm
      _ = _ := p.projection_over
  have hD : (D[M].comap (a.symm.hom ≫ T.toBase)).support = R[c].support :=
    hp.symm ▸ p.support_comap
  let K := Fan.contractedRaySet Q.regular b Q.rays centers[c] hT a.symm hD
  have hK : K = Fan.contractedRaySet Q.regular b Q.rays centers[d] hU e hE := by
    ext ρ
    rw [Fan.mem_contractedRaySet_iff, Fan.mem_contractedRaySet_iff, hrays, Iso.symm_hom, ← hp]
  let g₀ := Fan.contractedPicardMarkingOfRaySet Q.regular b Q.rays centers[c] hT
    a.symm hc hD K rfl
  let g₁ := Fan.contractedPicardMarkingOfRaySet Q.regular b Q.rays centers[d] hU
    e he hE K hK
  let gM : H.IsometryEquiv (Chow.intersectionBilinForm ℂ M.surface) := M.marking
  refine ⟨(gM.trans g₀.symm).trans g₁, fun x ↦ ?_⟩
  have hx := Fan.coe_contractedPicardMarkingOfRaySet_symm_apply Q.regular b Q.rays centers[d]
    hU e he hE K hK (g₁ (g₀.symm (gM x))).toMul
  have hx' := Fan.coe_contractedPicardMarkingOfRaySet_symm_apply Q.regular b Q.rays centers[c]
    hT a.symm hc hD K rfl (M.picardMarking x).toMul
  rw [ofMul_toMul, Iso.symm_hom, ← hp, p.marked_pullback] at hx'
  rw [ofMul_toMul] at hx
  -- The same contracted-ray complement is used by the two isometries.
  change (g₁.symm (g₁ (g₀.symm (gM x)))).val = _ at hx
  have hcancel := congrArg Subtype.val (g₁.symm_apply_apply (g₀.symm (gM x)))
  have hM := congrArg (fun y ↦ (g₀.symm y).val) (M.picardMarking_apply x).symm
  exact hx.symm.trans (hcancel.trans (hM.trans hx'))

include hU he hE hT a hp in
/-- A nodal contraction with the same surviving rays as a reference fiber carries
the original Picard marking. A compatible boundary numbering anchored at the
presentation origin then makes it a nodal model for the new center. -/
private theorem exists_nodal_model_of_numbered_contraction
    [PrestableFamily (E.subscheme ↘ SpecC)]
    (C : NodalCycleNumbering (Empty.elim : Empty → (E.subscheme ↘ SpecC).smoothLocus) n)
    (v : ToricBoundary ⟶ E.subscheme)
    (hv : v ≫ E.subschemeι = WithBoundary.boundaryι (Sigma.snd (A[d])) ≫ proj)
    (hC : v.IsOrientedCycleSubdivision Q.cycle C)
    (hzero : v (Q.cycle.componentGenericPoint Q.origin) = C.componentGenericPoint 0)
    (hCart : E.IsEffectiveCartier)
    (hrays : ∀ ρ : Q.fan.Ray,
      proj (prime[d,ρ]).val ∈ E.boundaryPrimes ↔
        p.projection (prime[c,ρ]).val ∈ D[M].boundaryPrimes) :
    ∃ (P : MarkedSurface ℂ n H XTor[r])
      (q : ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[d] P),
      D[P].IsEffectiveCartier ∧ Q.HasNodalModel d P ∧
        ∃ j : P.pair ≅ Pair, q.projection ≫ j.hom.right.left = proj := by
  let : IsModification proj := Fan.isModification_orderedContraction Q.regular b Q.rays
    centers[d] hU e
  obtain ⟨g, hg⟩ := exists_marking_of_same_contracted_rays Q hU e he hE p hT a hp hrays
  let F : X ⤏ XTor[r] := Fan.contractedXEvaluation b Q.rays χ[d] Q.regular proj
  let P : MarkedSurface ℂ n H XTor[r] :=
    { pair := Pair
      closedImmersion := inferInstanceAs (IsClosedImmersion E.subschemeι)
      integral := by exact ‹IsIntegral X›
      smooth := inferInstanceAs (SmoothOfRelativeDimension 2 (X ↘ SpecC))
      projective := inferInstanceAs (X.IsProjectiveOver ℂ)
      prestable := inferInstanceAs (PrestableFamily (E.subscheme ↘ SpecC))
      cycle := C
      marking := g
      evaluation := F }
  have hker : D[P] = E := ker_subschemeι E
  have hvOver : v.IsOver SpecC := ⟨by
    rw [E.over_eq_subschemeι_comp, reassoc_of% hv, he, WithBoundary.boundaryι_toBase_assoc,
      (Fan.boundaryIdeal Q.fan Q.complete.nonempty_cones).over_eq_subschemeι_comp,
      Fan.algebraicRealization_over]⟩
  let q : ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[d] P :=
    { projection := proj
      modification := inferInstance
      projection_over := he
      support_comap := by simpa only [hker] using hE
      boundaryMap := v
      boundary_comp := hv
      boundary_over := hvOver
      orientedSubdivision := hC
      component_zero := hzero
      marked_pullback x := by
        rw [MarkedSurface.picardMarking_apply]
        exact hg x
      evaluation_eq := by rfl }
  have hTower : IsNodalBoundaryTower D[P] (P.surface ↘ SpecC) (𝟙 P.surface) U := hker ▸ hU
  exact ⟨P, q, hker.symm ▸ hCart, (Q.hasNodalModel_iff d P).mpr
    ⟨q, Y, l, U, e.symm, hTower, rfl⟩, Iso.refl Pair, Category.comp_id proj⟩

local notation "Z" => Sigma.fst (A[d])
local notation "ιd" => WithBoundary.boundaryι (Sigma.snd (A[d]))
local notation "πd" => toBase (WithBoundary.toTower (Sigma.snd (A[d])))

include hU he hE in
private theorem exists_descended_numbering [PrestableFamily (E.subscheme ↘ SpecC)]
    (hCart : E.IsEffectiveCartier) :
    ∃ (k : ℕ) (_ : NeZero k)
      (C : NodalCycleNumbering (Empty.elim : Empty → (E.subscheme ↘ SpecC).smoothLocus) k)
      (v : ToricBoundary ⟶ E.subscheme),
      v ≫ E.subschemeι = ιd ≫ proj ∧ v.IsOrientedCycleSubdivision Q.cycle C := by
  let : IsModification proj := Fan.isModification_orderedContraction Q.regular b Q.rays
    centers[d] hU e
  let : (Z).Over SpecC := ⟨πd ≫ (Q.fan.algebraicRealization ↘ SpecC)⟩
  let hrank := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let : SmoothOfRelativeDimension 2 (Q.fan.algebraicRealization ↘ SpecC) :=
    (Fan.algebraicRealization_over Q.fan).symm ▸
      (hrank ▸ Q.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap Q.regular)
  let : SmoothOfRelativeDimension 2 ((Z) ↘ SpecC) :=
    (Fan.isClosedPointTower_internalBlowupTower b Q.rays centers[d]).smoothOfRelativeDimension _
  let : (proj).IsOver SpecC := ⟨he.trans
    (congrArg (πd ≫ ·) (Fan.algebraicRealization_over Q.fan).symm)⟩
  let : (ιd).IsOver SpecC := ⟨by
    change ιd ≫ πd ≫ (Q.fan.algebraicRealization ↘ SpecC) = ToricBoundary ↘ SpecC
    rw [WithBoundary.boundaryι_toBase_assoc,
      (Fan.boundaryIdeal Q.fan Q.complete.nonempty_cones).over_eq_subschemeι_comp]⟩
  let isoB : ToricBoundary ≅ R[d].subscheme := asIso (ιd).toImage
  have hBcomp : isoB.hom ≫ R[d].subschemeι = ιd := (ιd).toImage_imageι
  let hB : isoB.hom.IsOver SpecC := inferInstanceAs ((ιd).toImage.IsOver SpecC)
  let : PrestableFamily (R[d].subscheme ↘ SpecC) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @PrestableFamily)
      isoB.hom _).mp (hB.comp_over.symm ▸ Q.prestable)
  let hN : AtWorstNodalOfRelativeDimensionOne (E.subschemeι ≫ X ↘ SpecC) :=
    (E.over_eq_subschemeι_comp (S := SpecC)) ▸
      (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := E.subscheme ↘ SpecC))
  obtain ⟨hrad, hmap⟩ := E.radical_comap_eq_and_map_eq_of_support_eq proj hE
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := R[d].subscheme ↘ SpecC)).isReduced
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := E.subscheme ↘ SpecC)).isReduced
  have hR : (E.comap U.toBase).radical.comap e.hom = R[d] := by
    rw [← radical_comap_of_isOpenImmersion (E.comap U.toBase) e.hom, ← comap_comp, hrad]
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ SpecC)
  let hF : R[d].IsEffectiveCartier := hR ▸ (hU.radical_comap_toBase hCart hN).1.comap e.hom
  let hI := Q.fan.isEffectiveCartier_boundaryIdeal Q.regular Q.complete hrank
  have hK := Fan.canonicalClass_internalBlowupTower b Q.rays centers[d] Q.regular hI hF
    (Q.fan.canonicalClass_boundaryIdeal Q.regular Q.complete b hI)
  let C₀ := isoB.mapNodalCycleNumbering Q.cycle
    (q := (Empty.elim : Empty → (R[d].subscheme ↘ SpecC).smoothLocus))
  have hsub := isoB.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one Q.cycle C₀
    (by rw [Iso.boundaryCycleAction_mapNodalCycleNumbering, map_one])
  have hnumbered :=
    hU.isClosedPointTower.exists_numbering_of_anticanonical_boundary_tower_blowdown_of_iso
      e rfl hF C₀ hK
  dsimp only at hnumbered
  rw [hmap] at hnumbered
  obtain ⟨_, hpre, _, k, hk, C, v, hv, hvsub⟩ := hnumbered
  let : (Iso.refl E.subscheme).hom.IsOver SpecC := ⟨Category.id_comp _⟩
  let C' := (Iso.refl E.subscheme).mapNodalCycleNumbering C
    (q := (Empty.elim : Empty → (E.subscheme ↘ SpecC).smoothLocus))
  refine ⟨k, hk, C', isoB.hom ≫ v, ?_, ?_⟩
  · rw [Category.assoc, hv, reassoc_of% hBcomp]
  · simpa only [Iso.refl_hom, Category.comp_id] using (hsub.comp hvsub).comp
      ((Iso.refl E.subscheme).isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one C C'
        (by simp [C']))

include hU hE in
private theorem exists_anchored_numbering [PrestableFamily (E.subscheme ↘ SpecC)]
    (hCart : E.IsEffectiveCartier) (hD : D[M].IsEffectiveCartier)
    {k : ℕ} [NeZero k]
    (C : NodalCycleNumbering (Empty.elim : Empty → (E.subscheme ↘ SpecC).smoothLocus) k)
    (v : ToricBoundary ⟶ E.subscheme)
    (hv : v ≫ E.subschemeι = ιd ≫ proj)
    (hC : v.IsOrientedCycleSubdivision Q.cycle C)
    (hrays : ∀ ρ : Q.fan.Ray,
      proj (prime[d,ρ]).val ∈ E.boundaryPrimes ↔
        p.projection (prime[c,ρ]).val ∈ D[M].boundaryPrimes) :
    ∃ C' : NodalCycleNumbering (Empty.elim : Empty → (E.subscheme ↘ SpecC).smoothLocus) n,
      v.IsOrientedCycleSubdivision Q.cycle C' ∧
        v (Q.cycle.componentGenericPoint Q.origin) = C'.componentGenericPoint 0 := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ SpecC)
  let : Smooth (X ↘ SpecC) := SmoothOfRelativeDimension.smooth 2 _
  let : IsRegular X := IsRegular.of_smooth (X ↘ SpecC)
  let : IsNormalScheme X := IsRegular.isNormal
  let : IsModification proj := Fan.isModification_orderedContraction Q.regular b Q.rays
    centers[d] hU e
  let re := Fan.contractedBoundaryRayEmbedding Q.regular b Q.rays centers[d] proj hE
  let rd := Fan.contractedBoundaryRayEmbedding Q.regular b Q.rays centers[c]
    p.projection p.support_comap
  have hrange : Set.range re = Set.range rd := by
    ext ρ
    exact (Fan.mem_range_contractedBoundaryRayEmbedding_iff Q.regular b Q.rays centers[d]
      proj hE ρ).trans ((hrays ρ).trans
        (Fan.mem_range_contractedBoundaryRayEmbedding_iff Q.regular b Q.rays centers[c]
          p.projection p.support_comap ρ).symm)
  let er := (Equiv.ofInjective re re.injective).trans
    ((Set.equivOfEq hrange).trans (Equiv.ofInjective rd rd.injective).symm)
  let er' := (C.boundaryPrimeEquiv hCart).trans
    (er.trans (Equiv.ofBijective _ ⟨(M.numberedBoundaryPrimes hD).injective,
      M.numberedBoundaryPrimes_surjective hD⟩).symm)
  have hkn : k = n := by simpa only [Nat.card_zmod] using Nat.card_congr er'
  subst k
  let ρ := Q.rayOrder Q.origin
  have hpoint (x : Point Centers[r]) : (prime[x,ρ]).val =
      (A[x]).2.boundaryι (Q.cycle.componentGenericPoint Q.origin) := by
    rw [Fan.internalBlowupBoundaryPrime_val, ← Q.component_eq Q.origin,
      ← Q.cycle.componentGenericPoint_def]
  have hsurvive : p.projection (prime[c,ρ]).val ∈ D[M].boundaryPrimes := by
    rw [hpoint, ← Scheme.Hom.comp_apply, ← p.boundary_comp, Scheme.Hom.comp_apply]
    let : PrestableFamily (M.boundary ↘ SpecC) := M.prestable
    rw [p.component_zero]
    simpa only [M.numberedBoundaryPrimes_apply_val, M.coe_boundaryPrime] using
      (M.numberedBoundaryPrimes hD 0).property
  let x : E.boundaryPrimes := ⟨_, (hrays ρ).mpr hsurvive⟩
  obtain ⟨t, ht⟩ := (C.boundaryPrimeEquiv hCart).surjective x
  have ht' : v (Q.cycle.componentGenericPoint Q.origin) = C.componentGenericPoint t := by
    apply E.subschemeι.injective
    rw [← Scheme.Hom.comp_apply, hv, Scheme.Hom.comp_apply, ← hpoint]
    rw [← C.boundaryPrimeEquiv_apply_val hCart]
    exact (congrArg Subtype.val ht).symm
  refine ⟨C.reindex (.r t), ?_, by simpa only [NodalCycleNumbering.reindex_componentGenericPoint,
    DihedralGroup.cycleVertexPerm_r_apply, zero_add] using ht'⟩
  exact (Scheme.Hom.isOrientedCycleSubdivision_reindex_target_iff (.r t)).mpr
    (by simpa only [DihedralGroup.cycleOrientationSign_r, (by decide : (1 : ℤˣ) ≠ -1), ite_false]
      using hC)

include hU he hE hT a hp in
/-- A specified nodal contraction of a moved-center model with the same surviving
rays as the reference contraction gives a fiber of the original presentation.
The new boundary has the same number of components, starts at the prescribed
origin and keeps the orientation of the toric boundary. The marking pulls back
to the original Picard inclusion. -/
theorem exists_nodal_model_of_same_contracted_rays
    [PrestableFamily (E.subscheme ↘ SpecC)] (hCart : E.IsEffectiveCartier)
    (hD : D[M].IsEffectiveCartier)
    (hrays : ∀ ρ : Q.fan.Ray,
      proj (prime[d,ρ]).val ∈ E.boundaryPrimes ↔
        p.projection (prime[c,ρ]).val ∈ D[M].boundaryPrimes) :
    ∃ (P : MarkedSurface ℂ n H XTor[r])
      (q : ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[d] P),
      D[P].IsEffectiveCartier ∧ Q.HasNodalModel d P ∧
        ∃ j : P.pair ≅ Pair, q.projection ≫ j.hom.right.left = proj := by
  obtain ⟨k, hk, C, v, hv, hC⟩ := exists_descended_numbering Q hU e he hE hCart
  obtain ⟨C', hC', hz⟩ := exists_anchored_numbering Q hU e hE p hCart hD C v hv hC hrays
  exact exists_nodal_model_of_numbered_contraction Q hU e he hE p hT a hp C' v hv hC' hz hCart hrays

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation

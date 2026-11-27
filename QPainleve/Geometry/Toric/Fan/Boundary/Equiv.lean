/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Center
public import QPainleve.Geometry.Toric.Fan.Boundary.Ideal
public import QPainleve.Geometry.Toric.Fan.Scheme

public import QPainleve.Geometry.Toric.Fan.Picard.Basic
public import TauCeti.AlgebraicGeometry.CartierDivisor.Excision

import Mathlib.RingTheory.Spectrum.Prime.RingHom
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Equiv
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# Toric boundaries under fan equivalence

A fan equivalence identifies the reduced toric boundaries and carries each ray's
prime divisor to the prime divisor of the corresponding ray. These are equalities
of pulled-back ideal sheaves on the toric schemes, so they can be used to transport
boundary embeddings and centers on those boundaries.

The comparison uses Tau Ceti's `FanHom.affineToricChartι_comp_algebraicMap_of_mapsTo`
for chart naturality and `Fan.Ray.ker_binomialCenterEval` for the center equation.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Multiplicative
open TauCeti.AlgebraicGeometry (LineBundleClass)
open AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.Toric.FanEquiv

section Boundary

variable {N N' : Type u} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'} (e : FanEquiv Φ Ψ)

/-- The reduced boundary ideal pulls back to the reduced boundary ideal. -/
theorem comap_boundaryIdeal_algebraicMap (h₀ : Nonempty Φ.cones) (h₁ : Nonempty Ψ.cones) :
    (Ψ.boundaryIdeal h₁).comap e.toFanHom.algebraicMap = Φ.boundaryIdeal h₀ := by
  rw [Fan.boundaryIdeal_def, Fan.boundaryIdeal_def, comap_vanishingIdeal_of_isOpenImmersion]
  congr 1
  apply SetLike.coe_injective
  simp only [Closeds.coe_mk, Set.preimage_compl, e.preimage_range_denseTorusι h₀ h₁]

/-- The restriction of a toric isomorphism to the reduced closed boundary. -/
noncomputable def boundaryIso (h₀ : Nonempty Φ.cones) (h₁ : Nonempty Ψ.cones) :
    (Φ.boundaryIdeal h₀).subscheme ≅ (Ψ.boundaryIdeal h₁).subscheme := by
  let I := Φ.boundaryIdeal h₀
  let J := Ψ.boundaryIdeal h₁
  have hJ : J.comap e.toFanHom.algebraicMap = I := e.comap_boundaryIdeal_algebraicMap h₀ h₁
  let f := subschemeMap I J e.toFanHom.algebraicMap (le_map_iff_comap_le.mpr hJ.le)
  have hpb : IsPullback I.subschemeι f e.toFanHom.algebraicMap J.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (subschemeMap_subschemeι _ _ _ _).symm
      (by simpa only [ker_subschemeι] using hJ)
  letI := hpb.isIso_snd_of_isIso
  exact asIso f

/-- The boundary restriction intertwines the two boundary inclusions. -/
@[reassoc (attr := simp)]
theorem boundaryIso_hom_subschemeι (h₀ : Nonempty Φ.cones) (h₁ : Nonempty Ψ.cones) :
    (e.boundaryIso h₀ h₁).hom ≫ (Ψ.boundaryIdeal h₁).subschemeι =
      (Φ.boundaryIdeal h₀).subschemeι ≫ e.toFanHom.algebraicMap :=
  subschemeMap_subschemeι _ _ _
    (le_map_iff_comap_le.mpr (e.comap_boundaryIdeal_algebraicMap h₀ h₁).le)

-- In the chart of one ray, the boundary generic point belongs to that ray.
private theorem rayBoundaryPoint_specializes_of_mem_rayChart
    (hΨ : Ψ.IsRegular) (ρ : Ψ.Ray) {x : Ψ.algebraicRealization}
    (hx : x ∈ Set.range (Ψ.affineToricChartι ρ.toCone))
    (ht : x ∉ Set.range (Ψ.denseTorusι ⟨ρ.toCone⟩)) :
    (Ψ.rayBoundaryPoint hΨ ρ).val ⤳ x := by
  have h := ht
  rw [← Set.mem_compl_iff, ← Ψ.support_boundaryIdeal ⟨ρ.toCone⟩,
    Ψ.support_boundaryIdeal_eq_iUnion_closure hΨ] at h
  obtain ⟨τ, hτ⟩ := Set.mem_iUnion.mp h
  have hspec : (Ψ.rayBoundaryPoint hΨ τ).val ⤳ x := specializes_iff_mem_closure.mpr hτ
  have hm := (Ψ.affineToricChartι ρ.toCone).isOpenEmbedding.isOpen_range
    |>.stableUnderGeneralization hspec hx
  have hle := (Ψ.rayBoundaryPoint_mem_range_affineToricChartι_iff hΨ τ ρ.toCone).mp hm
  let a := (τ).toToricRay Ψ ρ.toCone hle
  let b := ρ.toToricRay Ψ ρ.toCone le_rfl
  have hab : a = b := by
    apply ToricRay.eq_of_toPointedCone_le (Ψ.isToricCone ρ.toCone.property).salient
    rw [Fan.Ray.toPointedCone_toToricRay, Fan.Ray.toPointedCone_toToricRay]
    exact hle
  have heq : τ = ρ := by
    apply Subtype.ext
    apply Subtype.ext
    simpa only [a, b, Fan.Ray.toPointedCone_toToricRay] using congrArg ToricRay.toPointedCone hab
  exact heq ▸ hspec

private theorem rayBoundaryPoint_specializes_algebraicMap (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (ρ : Φ.Ray) :
    (Ψ.rayBoundaryPoint hΨ (e.rayEquiv ρ)).val ⤳
      e.toFanHom.algebraicMap (Φ.rayBoundaryPoint hΦ ρ).val := by
  apply rayBoundaryPoint_specializes_of_mem_rayChart hΨ (e.rayEquiv ρ)
  · rw [toCone_rayEquiv]
    exact e.mapsTo_affineToricChartι ρ.toCone
      ((Φ.rayBoundaryPoint_mem_range_affineToricChartι_iff hΦ ρ ρ.toCone).mpr le_rfl)
  · have h := Φ.rayBoundaryPoint_notMem_range_denseTorusι hΦ ρ
    intro hm
    apply h
    rw [← e.preimage_range_denseTorusι ⟨ρ.toCone⟩ ⟨(e.rayEquiv ρ).toCone⟩]
    exact hm

/-- The toric morphism carries each ray divisor's generic point to the generic point
of its image ray divisor. -/
theorem algebraicMap_rayBoundaryPoint (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (ρ : Φ.Ray) :
    e.toFanHom.algebraicMap (Φ.rayBoundaryPoint hΦ ρ).val =
      (Ψ.rayBoundaryPoint hΨ (e.rayEquiv ρ)).val := by
  have h := e.rayBoundaryPoint_specializes_algebraicMap hΦ hΨ ρ
  have hinv := e.symm.rayBoundaryPoint_specializes_algebraicMap hΨ hΦ (e.rayEquiv ρ)
  rw [← rayEquiv_symm, Equiv.symm_apply_apply] at hinv
  have hcomp : e.symm.toFanHom.algebraicMap ≫ e.toFanHom.algebraicMap =
      𝟙 Ψ.algebraicRealization := by
    simpa only [symm_symm] using e.symm.algebraicMap_comp_symm
  have hinv' := hinv.map e.toFanHom.algebraicMap.continuous
  have hinv'' : e.toFanHom.algebraicMap (Φ.rayBoundaryPoint hΦ ρ).val ⤳
      (Ψ.rayBoundaryPoint hΨ (e.rayEquiv ρ)).val := by
    simpa only [← Scheme.Hom.comp_apply, hcomp, Scheme.Hom.id_base, TopCat.coe_id, id_eq]
      using hinv'
  exact (hinv''.antisymm h).eq

/-- A fan equivalence pulls the ideal of the image ray divisor back to the ideal
of the original ray divisor. -/
theorem comap_rayBoundaryIdeal_algebraicMap (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (ρ : Φ.Ray) :
    (Ψ.rayBoundaryIdeal hΨ (e.rayEquiv ρ)).comap e.toFanHom.algebraicMap =
      Φ.rayBoundaryIdeal hΦ ρ := by
  simpa only [e.algebraicMap_rayBoundaryPoint hΦ hΨ ρ, Fan.rayBoundaryIdeal_def] using
    comap_vanishingIdeal_closure_singleton_apply e.toFanHom.algebraicMap
      (Φ.rayBoundaryPoint hΦ ρ).val

/-- Pullback along a fan equivalence carries the class of the image ray divisor to the
class of the original ray divisor. -/
theorem pullback_primeDivisorClass_rayBoundaryPoint (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (ρ : Φ.Ray) :
    letI : Nonempty Φ.cones := ⟨ρ.toCone⟩
    letI : Nonempty Ψ.cones := ⟨(e.rayEquiv ρ).toCone⟩
    letI := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
    letI := Ψ.uniqueFactorizationMonoid_stalk_algebraicRealization hΨ
    LineBundleClass.pullback e.toFanHom.algebraicMap
      (LineBundleClass.primeDivisorClass (Ψ.rayBoundaryPoint hΨ (e.rayEquiv ρ))) =
      LineBundleClass.primeDivisorClass (Φ.rayBoundaryPoint hΦ ρ) := by
  let : Nonempty Φ.cones := ⟨ρ.toCone⟩
  let : Nonempty Ψ.cones := ⟨(e.rayEquiv ρ).toCone⟩
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  let := Ψ.uniqueFactorizationMonoid_stalk_algebraicRealization hΨ
  have h := LineBundleClass.pullback_primeDivisorClass_mapOfIsOpenImmersion
    e.toFanHom.algebraicMap (Φ.rayBoundaryPoint hΦ ρ)
  have he :
      AlgebraicGeometry.CodimensionOnePoint.mapOfIsOpenImmersion e.toFanHom.algebraicMap
        (Φ.rayBoundaryPoint hΦ ρ) = Ψ.rayBoundaryPoint hΨ (e.rayEquiv ρ) := by
    apply Subtype.ext
    rw [AlgebraicGeometry.CodimensionOnePoint.coe_mapOfIsOpenImmersion,
      e.algebraicMap_rayBoundaryPoint hΦ hΨ ρ]
  simpa only [he] using h

end Boundary

section Over

variable {N N' : Type} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'} (e : FanEquiv Φ Ψ)

/-- The induced boundary isomorphism respects the complex-scheme structures. -/
instance isOver_boundaryIso_hom (hΦ₀ : Nonempty Φ.cones) (hΨ₀ : Nonempty Ψ.cones) :
    (e.boundaryIso hΦ₀ hΨ₀).hom.IsOver (Spec (.of ℂ)) := ⟨by
  rw [Scheme.IdealSheafData.over_eq_subschemeι_comp, ← Category.assoc,
    boundaryIso_hom_subschemeι, Category.assoc, Ψ.algebraicRealization_over,
    e.toFanHom.algebraicMap_comp_algebraicRealizationStructureMap,
    ← Φ.algebraicRealization_over, ← Scheme.IdealSheafData.over_eq_subschemeι_comp]⟩

end Over

section Centers

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'} (e : FanEquiv Φ Ψ)
  (ρ : Φ.Ray)

private theorem mapsTo_rayCone :
    Set.MapsTo e.toFanHom.realMap
      (ρ.toCone.val : Set V) ((e.rayEquiv ρ).toCone.val : Set V') := by
  simpa only [toCone_rayEquiv] using e.mapsTo_coneEquiv ρ.toCone

local notation "F" => affineCoordinateRingMap Φ.lattice Ψ.lattice
  e.toFanHom.latticeMap e.toFanHom.realMap e.toFanHom.map_lattice (mapsTo_rayCone e ρ)

variable {m : N →+ ℤ} {m' : N' →+ ℤ}
  (hdim : Module.finrank ℤ N = 2) (hdim' : Module.finrank ℤ N' = 2)
  (hm : m ρ.primitiveGenerator = 0) (hm' : m' (e.rayEquiv ρ).primitiveGenerator = 0)
  (hprim : Function.Surjective m) (hprim' : Function.Surjective m') (c : ℂˣ)

local notation "chartEval(" P ", " ray ", " dim ", " vanishes ", " primitive ")" =>
  (AlgHom.comp (Fan.Ray.binomialCenterEval ray ℂ dim vanishes primitive c)
    (AlgEquiv.toAlgHom (AlgEquiv.symm (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ
      (dualSemigroup (Fan.lattice P) (Subtype.val (Fan.Ray.toCone P ray)))))))

private theorem binomialCenterEval_comp
    (hchar : m'.comp (e.latticeEquiv : N →+ N') = m) :
    (chartEval(Φ, ρ, hdim, hm, hprim)).comp F =
      chartEval(Ψ, e.rayEquiv ρ, hdim', hm', hprim') := by
  refine MonoidAlgebra.algHom_ext (fun x ↦ ?_) (Subsingleton.elim _ _)
  let a := x.toAdd
  have hx : ofAdd a = x := ofAdd_toAdd x
  rw [← hx]
  let a' := dualSemigroupMap Φ.lattice Ψ.lattice e.toFanHom.latticeMap
    e.toFanHom.realMap e.toFanHom.map_lattice (mapsTo_rayCone e ρ) a
  change (chartEval(Φ, ρ, hdim, hm, hprim))
      (F (MonoidAlgebra.single (ofAdd a) 1)) =
    chartEval(Ψ, e.rayEquiv ρ, hdim', hm', hprim') (MonoidAlgebra.single (ofAdd a) 1)
  rw [affineCoordinateRingMap_single]
  change (chartEval(Φ, ρ, hdim, hm, hprim)) (MonoidAlgebra.single (ofAdd a') 1) = _
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AddMonoidAlgebra.toMultiplicativeAlgEquiv_symm_single, toAdd_ofAdd]
  have hv : (a' : N →+ ℤ) ρ.primitiveGenerator =
      (a : N' →+ ℤ) (e.rayEquiv ρ).primitiveGenerator := by
    simp only [a', coe_dualSemigroupMap, AddMonoidHom.comp_apply, toFanHom_latticeMap,
      primitiveGenerator_rayEquiv]
    rfl
  by_cases ha : (a : N' →+ ℤ) (e.rayEquiv ρ).primitiveGenerator = 0
  · obtain ⟨n, hn⟩ :=
      (e.rayEquiv ρ).exists_zsmul_eq_of_apply_primitiveGenerator_eq_zero hdim' hm' hprim' ha
    have hb : (a' : N →+ ℤ) = n • m := by
      ext z
      simp only [a', coe_dualSemigroupMap, AddMonoidHom.comp_apply, toFanHom_latticeMap,
        ← hn, AddMonoidHom.zsmul_apply, ← hchar]
    have hsrc : a' = ρ.chartCharacter (m := n • m) (by simp [hm]) :=
      Subtype.ext (by simpa only [Fan.Ray.coe_chartCharacter] using hb)
    have hdst : a = (e.rayEquiv ρ).chartCharacter (m := n • m')
        (by simp only [AddMonoidHom.zsmul_apply, hm', smul_zero]) :=
      Subtype.ext (by simpa only [Fan.Ray.coe_chartCharacter] using hn.symm)
    rw [hsrc, hdst, Fan.Ray.binomialCenterEval_single_zsmul,
      Fan.Ray.binomialCenterEval_single_zsmul]
  · rw [Fan.Ray.binomialCenterEval_single_eq_zero _ _ _ _ _ _ _ _ (fun h ↦ ha (hv.symm.trans h)),
      Fan.Ray.binomialCenterEval_single_eq_zero _ _ _ _ _ _ _ _ ha]

/-- Matching primitive orbit characters give the same binomial parameter under a fan
equivalence. This is an equality of complex sections in the ambient toric scheme. -/
theorem binomialCenter_comp_algebraicMap
    (hchar : m'.comp (e.latticeEquiv : N →+ N') = m) :
    ρ.binomialCenter hdim hm hprim c ≫ e.toFanHom.algebraicMap =
      (e.rayEquiv ρ).binomialCenter hdim' hm' hprim' c := by
  have h := binomialCenterEval_comp e ρ hdim hdim' hm hm' hprim hprim' c hchar
  have hf : (chartEval(Φ, ρ, hdim, hm, hprim)).toRingHom.comp (F).toRingHom =
      (chartEval(Ψ, e.rayEquiv ρ, hdim', hm', hprim')).toRingHom :=
    congrArg AlgHom.toRingHom h
  rw [Fan.Ray.binomialCenter_def, Fan.Ray.binomialCenter_def, Category.assoc,
    e.toFanHom.affineToricChartι_comp_algebraicMap_of_mapsTo _ _ (mapsTo_rayCone e ρ),
    affineToricSchemeMap_def, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf]

/-- Under compatible orbit characters, the image binomial center pulls back to the
original center as a closed subscheme. -/
theorem comap_ker_binomialCenter_algebraicMap
    (hchar : m'.comp (e.latticeEquiv : N →+ N') = m) :
    ((e.rayEquiv ρ).binomialCenter hdim' hm' hprim' c).ker.comap e.toFanHom.algebraicMap =
      (ρ.binomialCenter hdim hm hprim c).ker := by
  rw [← e.binomialCenter_comp_algebraicMap ρ hdim hdim' hm hm' hprim hprim' c hchar,
    Scheme.Hom.comap_ker_comp_of_isClosedImmersion]

/-- The boundary restriction of a fan equivalence transports the binomial points
for matching orbit characters. -/
theorem binomialCenterOnBoundary_comp_boundaryIso
    (hchar : m'.comp (e.latticeEquiv : N →+ N') = m) :
    ρ.binomialCenterOnBoundary hdim hm hprim c ≫
        (e.boundaryIso ⟨ρ.toCone⟩ ⟨(e.rayEquiv ρ).toCone⟩).hom =
      (e.rayEquiv ρ).binomialCenterOnBoundary hdim' hm' hprim' c := by
  apply (cancel_mono (Ψ.boundaryIdeal ⟨(e.rayEquiv ρ).toCone⟩).subschemeι).mp
  rw [Category.assoc, e.boundaryIso_hom_subschemeι, ← Category.assoc,
    Fan.Ray.binomialCenterOnBoundary_comp_subschemeι,
    Fan.Ray.binomialCenterOnBoundary_comp_subschemeι]
  exact e.binomialCenter_comp_algebraicMap ρ hdim hdim' hm hm' hprim hprim' c hchar

/-- The ideal of an internal center on the image boundary pulls back to the original
center ideal under the compatibility of orbit characters. -/
theorem comap_ker_binomialCenterOnBoundary_boundaryIso
    (hchar : m'.comp (e.latticeEquiv : N →+ N') = m) :
    ((e.rayEquiv ρ).binomialCenterOnBoundary hdim' hm' hprim' c).ker.comap
        (e.boundaryIso ⟨ρ.toCone⟩ ⟨(e.rayEquiv ρ).toCone⟩).hom =
      (ρ.binomialCenterOnBoundary hdim hm hprim c).ker := by
  rw [← e.binomialCenterOnBoundary_comp_boundaryIso ρ hdim hdim' hm hm' hprim hprim' c hchar,
    Scheme.Hom.comap_ker_comp_of_isClosedImmersion]

end Centers

end TauCeti.Toric.FanEquiv

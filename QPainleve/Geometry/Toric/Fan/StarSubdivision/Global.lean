/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Affine
public import TauCeti.Geometry.Toric.Algebraic.Fan.DenseTorus
public import QPainleve.Geometry.Toric.Fan.Point
public import TauCeti.AlgebraicGeometry.Blowup.UniversalProperty
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

import QPainleve.Geometry.Toric.BaseChange.Subfan
import QPainleve.Geometry.Toric.Fan.Chart
import QPainleve.Geometry.Toric.Fan.DenseTorus
import QPainleve.Geometry.Toric.Fan.TwoDimensional
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Equiv
import TauCeti.Geometry.Toric.Algebraic.BaseChange.Complex
import TauCeti.Geometry.Toric.Algebraic.Fan.SubfanScheme
import QPainleve.AlgebraicGeometry.Blowup.Affine
import QPainleve.AlgebraicGeometry.Blowup.Point.Fiber
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import QPainleve.Geometry.Toric.Fan.Smooth
import TauCeti.AlgebraicGeometry.Blowup.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

/-!
# A star subdivision is a point blowup

The affine blowup comparison for a two-dimensional cone extends to the entire regular
surface fan. The preimage of the cone chart is its affine star subdivision, and on
the other cone charts the subdivision morphism is an isomorphism. The comparison
uses Tau Ceti's Cartesian squares for preimages of open subfans and its blowup
universal property.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Multiplicative
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

private theorem complexIso_inv_comp_subdivisionMap {A B : Fan i} (f : FanHom A B) :
    A.finiteFanSchemeComplexIso.inv ≫ f.finiteFanSchemeHom ℂ =
      f.algebraicMap ≫ B.finiteFanSchemeComplexIso.inv := by
  apply A.algebraicRealization_hom_ext
  intro σ
  let τ : B.cones := ⟨f.leastCone σ.property, f.leastCone_mem σ.property⟩
  have hm : Set.MapsTo f.realMap (σ.val : Set V) (τ.val : Set V) :=
    fun x hx ↦ f.map_le_leastCone σ.property ⟨x, hx, rfl⟩
  rw [Fan.affineToricChartι_finiteFanSchemeComplexIso_inv_assoc,
    f.affineChartι_comp_finiteFanSchemeHom ℂ σ τ hm, ← Category.assoc _ f.algebraicMap,
    f.affineToricChartι_comp_algebraicMap_of_mapsTo σ τ hm, Category.assoc,
    Fan.affineToricChartι_finiteFanSchemeComplexIso_inv]
  simp only [← Category.assoc, affineToricSchemeIsoAddMonoidAlgebraSpec_hom_left,
    affineChartMap_def, affineToricSchemeMap_def, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply CommRingCat.hom_ext
  let eσ := AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ (dualSemigroup A.lattice σ.val)
  let eτ := AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ (dualSemigroup B.lattice τ.val)
  have h :
      eσ.toAlgHom.comp
          (AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ
            (dualSemigroupMap A.lattice B.lattice f.latticeMap f.realMap f.map_lattice hm)) =
        (affineCoordinateRingMap A.lattice B.lattice f.latticeMap f.realMap f.map_lattice hm).comp
          eτ.toAlgHom := by
    apply AddMonoidAlgebra.algHom_ext
    · intro m
      simp only [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, Function.comp_apply, eσ, eτ,
        AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single,
        AddMonoidAlgebra.toMultiplicativeAlgEquiv_single,
        affineCoordinateRingMap_single]
    · exact Subsingleton.elim _ _
  exact congrArg AlgHom.toRingHom h

variable {Φ} (hΦ : Φ.IsRegular) (σ : Φ.cones)
  (hN : Module.finrank ℤ N = 2) (hc : Nat.card (ToricRay σ.val) = 2)

private theorem algebraicMap_comp_eqToIso_hom {A B C : Fan i} (h : B = C)
    (f : FanHom A B) (g : FanHom A C) (hfg : f.latticeMap = g.latticeMap) :
    f.algebraicMap ≫ (eqToIso (congrArg Fan.algebraicRealization h)).hom =
      g.algebraicMap := by
  subst C
  simpa using congrArg FanHom.algebraicMap (FanHom.ext hfg)

private theorem eqToIso_hom_comp_algebraicMap {A B C : Fan i} (h : A = B)
    (f : FanHom B C) (g : FanHom A C) (hfg : f.latticeMap = g.latticeMap) :
    (eqToIso (congrArg Fan.algebraicRealization h)).hom ≫ f.algebraicMap =
      g.algebraicMap := by
  subst B
  simpa using congrArg FanHom.algebraicMap (FanHom.ext hfg)

private theorem isPullback_subdivision_of_localFans {A B A' B' : Fan i}
    (h : A.IsSubdivision B) (h' : A'.IsSubdivision B')
    (S : Set (PointedCone ℝ V)) (hS : S ⊆ B.cones)
    (hface : ∀ ⦃κ τ⦄, κ ∈ S → τ.IsFaceOf κ → τ ∈ S)
    (ha : A'.cones = h.toFanHom.preimageCones S) (hb : B'.cones = S)
    (a : FanHom A' A) (b : FanHom B' B)
    (ha₀ : a.latticeMap = AddMonoidHom.id N) (hb₀ : b.latticeMap = AddMonoidHom.id N) :
    IsPullback a.algebraicMap h'.toFanHom.algebraicMap h.toFanHom.algebraicMap
      b.algebraicMap := by
  let f := h.toFanHom
  let ia := A.subfanInclusion (f.preimageCones S) (f.preimageCones_subset S)
    (f.preimageCones_closedUnderFaces S hface)
  let ib := B.subfanInclusion S hS hface
  have ea : f.preimageSubfan S hface = A' := Fan.ext ((Fan.subfan_cones ..).trans ha.symm)
  have eb : B.subfan S hS hface = B' := Fan.ext ((Fan.subfan_cones ..).trans hb.symm)
  have h₁ : (eqToIso (congrArg Fan.algebraicRealization ea)).hom ≫ a.algebraicMap =
      ia.algebraicMap := eqToIso_hom_comp_algebraicMap ea a ia (by
    rw [ha₀, subfanInclusion_latticeMap])
  have h₂ : (eqToIso (congrArg Fan.algebraicRealization eb)).hom ≫ b.algebraicMap =
      ib.algebraicMap := eqToIso_hom_comp_algebraicMap eb b ib (by
    rw [hb₀, subfanInclusion_latticeMap])
  have h₃ := algebraicMap_comp_eqToIso_hom eb (f.restrictToPreimage S hS hface)
    (h'.toFanHom.comp (ea.symm ▸ FanHom.id A')) (by
      rw [FanHom.restrictToPreimage_latticeMap, FanHom.comp_latticeMap,
        IsSubdivision.toFanHom_latticeMap, IsSubdivision.toFanHom_latticeMap]
      cases ea
      simp)
  have h₄ : (ea.symm ▸ FanHom.id A' : FanHom (f.preimageSubfan S hface) A').algebraicMap =
      (eqToIso (congrArg Fan.algebraicRealization ea)).hom := by
    cases ea
    simp [FanHom.algebraicMap_id]
  refine (f.isPullback_preimageSubfan_algebraicMap S hS hface).of_iso
    (eqToIso (congrArg Fan.algebraicRealization ea)) (Iso.refl _)
    (eqToIso (congrArg Fan.algebraicRealization eb)) (Iso.refl _) ?_ ?_ (by simp [f]) ?_
  · simpa using h₁.symm
  · rwa [FanHom.algebraicMap_comp, h₄] at h₃
  · simpa using h₂.symm

include hΦ hN hc in
private theorem preimageCones_starSubdivisionAlong_faces :
    let hσ := isRegular_iff.1 hΦ _ σ.property
    let A := ToricRay.faceFinset (PointedCone.IsFaceOf.refl σ.val) hσ.fg
    let hsub := Φ.starSubdivisionAlong_isSubdivision hΦ σ.property
      (ne_bot_of_card_toricRay_eq_two hc)
    hsub.toFanHom.preimageCones {τ | τ.IsFaceOf σ.val} =
      (Fan.starSubdivision Φ.lattice A hσ).cones := by
  dsimp only
  let hσ := isRegular_iff.1 hΦ _ σ.property
  let A := ToricRay.faceFinset (PointedCone.IsFaceOf.refl σ.val) hσ.fg
  let h := Φ.starSubdivisionAlong_isSubdivision hΦ σ.property (ne_bot_of_card_toricRay_eq_two hc)
  ext κ
  constructor
  · intro hκ
    have hκ' := h.toFanHom.preimageCones_subset _ hκ
    have hle := (h.le_leastCone hκ').trans ((h.toFanHom.mem_preimageCones_iff _ hκ').1 hκ).le
    rcases (Φ.mem_starSubdivisionAlong_cones hΦ σ.property).1 hκ' with
      ⟨hκΦ, hσκ⟩ | ⟨τ, hτ, hστ, hκτ⟩
    · exact mem_starSubdivision_cones_of_isFaceOf Φ.lattice A hσ
        (Φ.isFaceOf_of_le σ.property hκΦ hle)
        (ToricRay.exists_mem_faceFinset_not_le_of_not_le _ _ hσ.toIsToricCone.salient hσκ)
    · have he : σ.val = τ :=
        congrArg Subtype.val (eq_of_le_fullCone hΦ hN hc (τ := ⟨τ, hτ⟩) hστ)
      subst τ
      exact hκτ
  · intro hκ
    have hκ' := (Φ.mem_starSubdivisionAlong_cones hΦ σ.property).2
      (Or.inr ⟨σ.val, σ.property, le_rfl, hκ⟩)
    refine (h.toFanHom.mem_preimageCones_iff {τ | τ.IsFaceOf σ.val} hκ').2
      (Φ.isFaceOf_of_le σ.property (h.toFanHom.leastCone_mem hκ') ?_)
    apply h.toFanHom.leastCone_le hκ' σ.property
    rw [IsSubdivision.toFanHom_realMap, PointedCone.map_id]
    exact le_of_mem_starSubdivision_cones _ _ _ hκ

section LocalComparison

variable (h₀ : σ.val ≠ ⊥)

local notation "Ψ" => Φ.starSubdivisionAlong hΦ σ.property
local notation "F" => (Φ.starSubdivisionAlong_isSubdivision hΦ σ.property h₀)
local notation "π" => FanHom.algebraicMap (IsSubdivision.toFanHom F)
local notation "I" => Scheme.Hom.ker (Φ.distinguishedPointHom σ)
local notation "J" => RingHom.ker
  (AlgHom.toRingHom (facePointAlgebraHom Φ.lattice (⊤ : σ.val.Face) ℂ))

private def facesInclusion (τ : Φ.cones) :
    FanHom (Fan.ofCone Φ.lattice (Φ.isToricCone τ.property)) Φ :=
  FanHom.ofLatticeMap _ _ (AddMonoidHom.id N) fun κ hκ ↦ by
    rw [IsIntegralLattice.extend_id, PointedCone.map_id]
    exact ⟨τ.val, τ.property, ((Fan.mem_ofCone_cones _ _).1 hκ).le⟩

private theorem chartι_comp_facesInclusion (τ : Φ.cones) :
    (Fan.ofCone Φ.lattice (Φ.isToricCone τ.property)).affineToricChartι
        ⟨τ.val, (Fan.mem_ofCone_cones _ _).2 (.refl _)⟩ ≫
      (facesInclusion τ).algebraicMap = Φ.affineToricChartι τ := by
  have hmap : (facesInclusion τ).realMap = LinearMap.id := by
    rw [facesInclusion, FanHom.ofLatticeMap_realMap, IsIntegralLattice.extend_id]
  rw [(facesInclusion τ).affineToricChartι_comp_algebraicMap_of_mapsTo _ τ (by
    rw [hmap]
    exact Set.mapsTo_id (τ.val : Set V))]
  have hlattice : (facesInclusion τ).latticeMap = AddMonoidHom.id N :=
    FanHom.ofLatticeMap_latticeMap ..
  simp only [hmap, hlattice, affineToricSchemeMap_id, Category.id_comp]

include hΦ hN hc in
private theorem exists_isPullback_starSubdivisionAlong_rees :
    ∃ j : Proj (reesAlgebra.grade J) ⟶ (Fan.algebraicRealization Ψ),
      IsPullback j (Proj.toSpecCoeff (reesAlgebra.grade J)) π (Φ.additiveAffineToricChartι σ) := by
  let hσ := isRegular_iff.1 hΦ _ σ.property
  let A := ToricRay.faceFinset (PointedCone.IsFaceOf.refl σ.val) hσ.fg
  let P := Fan.starSubdivision Φ.lattice A hσ
  let Q := Fan.ofCone Φ.lattice hσ.toIsToricCone
  obtain ⟨hA, e, he⟩ := exists_iso_reesBlowup_starSubdivision Φ.lattice ℂ hσ hN hc
  let q : Q.cones := ⟨σ.val, (Fan.mem_ofCone_cones _ _).2 (.refl _)⟩
  let a : FanHom P Ψ := FanHom.ofLatticeMap _ _ (AddMonoidHom.id N) fun κ hκ ↦ by
    rw [IsIntegralLattice.extend_id, PointedCone.map_id]
    exact ⟨κ, (Φ.mem_starSubdivisionAlong_cones hΦ σ.property).2
      (Or.inr ⟨σ.val, σ.property, le_rfl, hκ⟩), le_rfl⟩
  let b := facesInclusion σ
  have hp := isPullback_subdivision_of_localFans F
    (Fan.starSubdivision_isSubdivision Φ.lattice A hσ hA) {τ | τ.IsFaceOf σ.val}
    (Φ.isFaceOf_subset_cones σ.property) (fun _ _ ht hr ↦ hr.trans ht)
    (preimageCones_starSubdivisionAlong_faces hΦ σ hN hc).symm
    (Set.ext fun _ ↦ Fan.mem_ofCone_cones ..) a b
    (FanHom.ofLatticeMap_latticeMap ..) (FanHom.ofLatticeMap_latticeMap ..)
  let η := Q.affineChartι ℂ q ≫ Q.finiteFanSchemeComplexIso.hom
  have : IsIso (Q.affineChartι ℂ q) :=
    Fan.isIso_affineChartι_ofCone ℂ Φ.lattice hσ.toIsToricCone
  have : IsIso η := inferInstanceAs (IsIso (Q.affineChartι ℂ q ≫ Q.finiteFanSchemeComplexIso.hom))
  let v := (Fan.starSubdivision_isSubdivision Φ.lattice A hσ hA).toFanHom
  let d := P.finiteFanSchemeComplexIso.symm ≪≫ e
  have he' : e.hom ≫ Proj.toSpecCoeff (reesAlgebra.grade J) ≫ Q.affineChartι ℂ q =
      v.finiteFanSchemeHom ℂ := by
    simpa only [toSpecCoeff_reesAlgebra, Category.assoc, v] using he
  have hd : d.hom ≫ Proj.toSpecCoeff (reesAlgebra.grade J) ≫ η = v.algebraicMap := by
    calc
      _ = P.finiteFanSchemeComplexIso.inv ≫
          (e.hom ≫ Proj.toSpecCoeff (reesAlgebra.grade J) ≫ Q.affineChartι ℂ q) ≫
          Q.finiteFanSchemeComplexIso.hom := by
          simp only [d, Iso.trans_hom, Iso.symm_hom, η, Category.assoc]
      _ = _ := by
        rw [he', ← Category.assoc, complexIso_inv_comp_subdivisionMap, Category.assoc,
          Iso.inv_hom_id, Category.comp_id]
  refine ⟨d.inv ≫ a.algebraicMap, hp.of_iso d (Iso.refl _) (asIso η).symm
    (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]) ?_
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]) ?_⟩
  · apply (cancel_mono η).mp
    simpa only [Category.assoc, Iso.symm_hom, asIso_inv, IsIso.inv_hom_id, Category.comp_id]
      using hd.symm
  · apply (cancel_epi η).mp
    rw [Category.assoc, Iso.symm_hom, asIso_inv, IsIso.hom_inv_id_assoc]
    rw [Iso.refl_hom, Category.comp_id]
    change (Q.affineChartι ℂ q ≫ Q.finiteFanSchemeComplexIso.hom) ≫
      (facesInclusion σ).algebraicMap = Φ.additiveAffineToricChartι σ
    rw [Category.assoc, Q.affineChartι_finiteFanSchemeComplexIso_hom_assoc,
      affineToricSchemeIsoAddMonoidAlgebraSpec_inv_left, chartι_comp_facesInclusion,
      Φ.additiveAffineToricChartι_def]

private theorem exists_isPullback_starSubdivisionAlong_otherChart
    (τ : Φ.cones) (hστ : ¬ σ ≤ τ) :
    ∃ j : Φ.affineToricChart τ ⟶ (Fan.algebraicRealization Ψ),
      IsPullback j (𝟙 _) π (Φ.affineToricChartι τ) := by
  have hτ : τ.val ∈ Fan.cones Ψ :=
    Φ.mem_starSubdivisionAlong_cones_of_not_le hΦ σ.property τ.property hστ
  exact ⟨_, (F).isPullback_affineToricChartι hτ τ.property⟩

private theorem comap_ker_distinguishedPointHom :
    (I).comap (Φ.additiveAffineToricChartι σ) =
      ofIdealTop ((J).map
        (Scheme.ΓSpecIso (.of (affineChartRing ℂ Φ.lattice σ.val))).inv.hom) := by
  let p := Spec.map
    (CommRingCat.ofHom (facePointAlgebraHom Φ.lattice (⊤ : σ.val.Face) ℂ).toRingHom)
  let j := Φ.additiveAffineToricChartι σ
  have hcomp : p ≫ j = Φ.distinguishedPointHom σ := by
    dsimp only [p, j]
    rw [Φ.additiveAffineToricChartι_def, ← Spec.map_comp_assoc, Φ.distinguishedPointHom_def,
      ← CommRingCat.ofHom_comp]
    congr 2
    apply CommRingCat.hom_ext
    let e := AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ (dualSemigroup Φ.lattice σ.val)
    change ((facePointAlgebraHom Φ.lattice (⊤ : σ.val.Face) ℂ).comp e.symm.toAlgHom).toRingHom =
      (distinguishedPoint Φ.lattice (⊤ : σ.val.Face)).toRingHom
    apply congrArg AlgHom.toRingHom
    apply MonoidAlgebra.algHom_ext
    · intro m
      obtain ⟨m, rfl⟩ := Multiplicative.ofAdd.surjective m
      simp only [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, Function.comp_apply, e,
        AddMonoidAlgebra.toMultiplicativeAlgEquiv_symm_single, toAdd_ofAdd,
        facePointAlgebraHom_single, distinguishedPoint_apply_single]
    · exact Subsingleton.elim _ _
  have hrange : Set.range (Φ.distinguishedPointHom σ) ⊆ Set.range j := by
    rw [← hcomp, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact Set.range_comp_subset_range _ _
  have hp : IsPullback p (𝟙 _) j (Φ.distinguishedPointHom σ) := by
    rw [IsOpenImmersion.lift_uniq j _ hrange p hcomp]
    exact IsOpenImmersion.isPullback_lift_id _ j hrange
  have hclosed := Φ.isClosedImmersion_distinguishedPointHom σ
  rw [← ker_eq_comap_of_isPullback _ hp, Scheme.Hom.ker_Spec_map]
  rfl

private theorem comap_ker_distinguishedPointHom_otherChart (τ : Φ.cones)
    (hστ : ¬ σ ≤ τ) :
    (I).comap (Φ.affineToricChartι τ) = ⊤ := by
  have hclosed := Φ.isClosedImmersion_distinguishedPointHom σ
  rw [← support_eq_bot_iff]
  apply SetLike.coe_injective
  rw [support_comap, TopologicalSpace.Closeds.coe_preimage,
    (Φ.distinguishedPointHom σ).support_ker,
    (Φ.distinguishedPointHom σ).isClosedEmbedding.isClosed_range.closure_eq]
  exact Set.eq_empty_iff_forall_notMem.mpr fun x ⟨y, hy⟩ ↦
    hστ ((Φ.distinguishedPointHom_mem_range_affineToricChartι_iff σ τ y).1 ⟨x, hy.symm⟩)

include hΦ hN hc in
private theorem exists_starSubdivisionAlong_localComparison (τ : Φ.cones) :
    ∃ (W : Scheme) (a : W ⟶ Fan.algebraicRealization Ψ) (b : W ⟶ (I).blowup)
      (q : W ⟶ Φ.affineToricChart τ), IsPullback a q π (Φ.affineToricChartι τ) ∧
        IsPullback b q (I).blowupToBase (Φ.affineToricChartι τ) := by
  by_cases ht : σ = τ
  · subst τ
    obtain ⟨a, ha⟩ := exists_isPullback_starSubdivisionAlong_rees hΦ σ hN hc h₀
    obtain ⟨b, hb⟩ := (I).exists_isPullback_toSpecCoeff_reesAlgebra
      (Φ.additiveAffineToricChartι σ) (J) (comap_ker_distinguishedPointHom σ)
    let η : affineChart ℂ Φ.lattice σ.val ≅ Φ.affineToricChart σ :=
      Scheme.Spec.mapIso
        (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ
          (dualSemigroup Φ.lattice σ.val)).symm.toRingEquiv.toCommRingCatIso.op
    let f := Proj.toSpecCoeff (reesAlgebra.grade J) ≫ η.hom
    have hj : Φ.additiveAffineToricChartι σ = η.hom ≫ Φ.affineToricChartι σ := by
      rw [Φ.additiveAffineToricChartι_def]
      rfl
    refine ⟨_, a, b, f, ?_, ?_⟩
    · exact ha.of_iso (Iso.refl _) (Iso.refl _) η (Iso.refl _)
        (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]) (by simp [f])
        (by simp) (by simp [hj])
    · exact hb.of_iso (Iso.refl _) (Iso.refl _) η (Iso.refl _)
        (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]) (by simp [f])
        (by simp) (by simp [hj])
  · have hστ : ¬ σ ≤ τ := fun h ↦ ht (eq_of_le_fullCone hΦ hN hc h)
    obtain ⟨a, ha⟩ := exists_isPullback_starSubdivisionAlong_otherChart hΦ σ h₀ τ hστ
    let j := Φ.affineToricChartι τ
    have : IsOpenImmersion j := Fan.isOpenImmersion_affineToricChartι τ
    have hjtop : (I).comap j = ⊤ := comap_ker_distinguishedPointHom_otherChart σ τ hστ
    have hj : ((I).comap j).IsEffectiveCartier := by
      rw [hjtop]
      exact isEffectiveCartier_top _
    have := (isIso_blowupToBase_iff _).2 hj
    let e := asIso ((I).comap j).blowupToBase
    have hb := ((I).isPullback_blowupMap_of_flat j).flip
    refine ⟨_, a, e.inv ≫ (I).blowupMap j, 𝟙 _, ha,
      hb.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp [e]) (by simp)
        (by simp [j])⟩

include hΦ hN hc in
private theorem exists_iso_blowup_starSubdivisionAlong_over :
    ∃ e : Fan.algebraicRealization Ψ ≅ (I).blowup, e.hom ≫ (I).blowupToBase = π := by
  choose W a b q ha hb using exists_starSubdivisionAlong_localComparison hΦ σ hN hc h₀
  have haOpen (τ) : IsOpenImmersion (a τ) :=
    MorphismProperty.of_isPullback (ha τ).flip inferInstance
  have hbOpen (τ) : IsOpenImmersion (b τ) :=
    MorphismProperty.of_isPullback (hb τ).flip inferInstance
  have hrange {Z : Scheme} (g : Z ⟶ Φ.algebraicRealization)
      {j : ∀ τ, W τ ⟶ Z} (hj : ∀ τ, IsPullback (j τ) (q τ) g (Φ.affineToricChartι τ))
      (z : Z) : ∃ τ, z ∈ Set.range (j τ) := by
    obtain ⟨τ, x, hx⟩ := Φ.exists_affineToricChartι_apply_eq (g z)
    refine ⟨τ, ?_⟩
    have hz : z ∈ Set.range (pullback.fst g (Φ.affineToricChartι τ)) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨x, hx⟩
    obtain ⟨y, hy⟩ := hz
    exact ⟨(hj τ).isoPullback.inv y, by
      rw [← Scheme.Hom.comp_apply, (hj τ).isoPullback_inv_fst, hy]⟩
  have hcartier : ((I).comap π).IsEffectiveCartier := by
    refine isEffectiveCartier_of_forall_exists_isOpenImmersion _ fun z ↦ ?_
    obtain ⟨τ, hz⟩ := hrange π ha z
    refine ⟨W τ, a τ, haOpen τ, hz, ?_⟩
    rw [← comap_comp, (ha τ).w, ← (hb τ).w, comap_comp]
    exact (I).isEffectiveCartier_comap_blowupToBase.comap _
  let g := (I).blowupLift π hcartier
  have hg : g ≫ (I).blowupToBase = π := (I).blowupLift_blowupToBase _ _
  have hlocal (τ) : a τ ≫ g = b τ := by
    apply (I).blowup_hom_ext
    · rw [Category.assoc, hg, (ha τ).w, (hb τ).w]
    · rw [Category.assoc, hg, comap_comp]
      exact hcartier.comap _
  let 𝒰 : (I).blowup.OpenCover := Scheme.Cover.mkOfCovers Φ.cones W b
    (hrange (I).blowupToBase hb) hbOpen
  have hgIso := (IsZariskiLocalAtTarget.iff_of_openCover (f := g)
    (P := MorphismProperty.isomorphisms Scheme) 𝒰).2 (fun τ ↦ by
      have h := (IsPullback.of_bot (by simpa only [Category.id_comp, hg] using ha τ)
        (by simpa only [Category.id_comp] using hlocal τ) (hb τ) :
          IsPullback (a τ) (𝟙 _) g (b τ))
      have he : IsIso (h.isoPullback.hom ≫ pullback.snd g (b τ)) := by
        rw [h.isoPullback_hom_snd]
        infer_instance
      apply (MorphismProperty.isomorphisms.iff _).2
      -- The cover consists of the second pullback projections `b τ`.
      change IsIso (pullback.snd g (b τ))
      exact IsIso.of_isIso_comp_left h.isoPullback.hom _)
  have := (MorphismProperty.isomorphisms.iff g).1 hgIso
  exact ⟨asIso g, hg⟩

include hc in
private theorem isEffectiveCartier_comap_distinguishedPointHom_denseTorusι :
    ((I).comap (Φ.denseTorusι ⟨σ⟩)).IsEffectiveCartier := by
  let τ : Φ.cones := ⟨⊥, Φ.bot_mem σ.property⟩
  have hστ : ¬ σ ≤ τ := fun h ↦ ne_bot_of_card_toricRay_eq_two hc (le_bot_iff.mp h)
  have hcomap := comap_ker_distinguishedPointHom_otherChart σ τ hστ
  rw [Φ.denseTorusι_eq_affineToricChartι _ τ.property, hcomap]
  exact isEffectiveCartier_top _

include hΦ hN hc in
/-- The star subdivision of a regular rank-two fan at a two-dimensional cone is
isomorphic to the blowup at the reduced distinguished point of that cone, over
the original toric scheme. The isomorphism identifies the dense torus with its
canonical lift to the blowup. -/
theorem exists_iso_blowup_starSubdivisionAlong :
    let t := Φ.denseTorusι ⟨σ⟩
    ∃ (h₀ : σ.val ≠ ⊥)
      (e : (Φ.starSubdivisionAlong hΦ σ.property).algebraicRealization ≅
        (Φ.distinguishedPointHom σ).ker.blowup)
      (ht : ((Φ.distinguishedPointHom σ).ker.comap t).IsEffectiveCartier),
      e.hom ≫ (Φ.distinguishedPointHom σ).ker.blowupToBase =
        (Φ.starSubdivisionAlong_isSubdivision hΦ σ.property h₀).toFanHom.algebraicMap ∧
      ∀ hn : Nonempty (Φ.starSubdivisionAlong hΦ σ.property).cones,
        (Φ.starSubdivisionAlong hΦ σ.property).denseTorusι hn ≫ e.hom =
          (Φ.distinguishedPointHom σ).ker.blowupLift t ht := by
  let h₀ := ne_bot_of_card_toricRay_eq_two hc
  obtain ⟨e, he⟩ := exists_iso_blowup_starSubdivisionAlong_over hΦ σ hN hc h₀
  have ht := isEffectiveCartier_comap_distinguishedPointHom_denseTorusι σ hc
  refine ⟨h₀, e, ht, he, fun hn ↦ (I).eq_blowupLift ht ?_⟩
  rw [Category.assoc, he, IsSubdivision.denseTorusι_comp_algebraicMap]

end LocalComparison

local notation "pt" => IsLocalRing.closedPoint ℂ

/-- The complement of the isomorphism locus of a blowup at a distinguished point
of a regular toric surface is that point. -/
theorem centre_eq_singleton_distinguishedPoint_of_blowup (Φ : Fan i)
    (hΦ : Φ.IsRegular) (hN : Module.finrank ℤ N = 2) (σ : Φ.cones)
    {Y : Scheme} (f : Y ⟶ Φ.algebraicRealization) (w : Y ≅ (Φ.distinguishedPointHom σ).ker.blowup)
    (hw : w.hom ≫ (Φ.distinguishedPointHom σ).ker.blowupToBase = f) :
    f.centre = {Φ.distinguishedPointHom σ pt} := by
  let s := Φ.algebraicRealizationStructureMap
  let : SmoothOfRelativeDimension 2 s :=
    hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  have : Smooth s := Φ.smooth_algebraicRealizationStructureMap hΦ
  have : IsLocallyNoetherian Φ.algebraicRealization := LocallyOfFiniteType.isLocallyNoetherian s
  have hclosed := Φ.isClosed_singleton_distinguishedPoint σ
  have := isRegularLocalRing_stalk_of_smooth s (Φ.distinguishedPointHom σ pt)
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq s 2).mp
    inferInstance).2 _ hclosed
  rw [← hw, Scheme.Hom.centre_def, Scheme.Hom.isoLocus_comp_of_isIso, ← Scheme.Hom.centre_def,
    (Φ.distinguishedPointHom σ).ker_eq_ker_fromSpecResidueField,
    Scheme.ker_fromSpecResidueField_eq_vanishingIdeal]
  exact centre_blowupToBase_closed_point hclosed hdim

/-- The center of a blowup at the distinguished point of a regular toric surface
lies outside the isomorphism locus of the blowup projection. -/
theorem notMem_isoLocus_distinguishedPoint_of_blowup (Φ : Fan i)
    (hΦ : Φ.IsRegular) (hN : Module.finrank ℤ N = 2) (σ : Φ.cones)
    {Y : Scheme} (f : Y ⟶ Φ.algebraicRealization) (w : Y ≅ (Φ.distinguishedPointHom σ).ker.blowup)
    (hw : w.hom ≫ (Φ.distinguishedPointHom σ).ker.blowupToBase = f) :
    Φ.distinguishedPointHom σ pt ∉ f.isoLocus := by
  have hcentre := Φ.centre_eq_singleton_distinguishedPoint_of_blowup hΦ hN σ f w hw
  have hmem : Φ.distinguishedPointHom σ pt ∈ f.centre := by
    rw [hcentre]
    exact Set.mem_singleton _
  simpa only [Scheme.Hom.centre_def, Set.mem_compl_iff, SetLike.mem_coe] using hmem

end TauCeti.Toric.Fan

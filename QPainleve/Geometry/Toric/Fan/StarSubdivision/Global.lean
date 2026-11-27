/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Affine
public import TauCeti.AlgebraicGeometry.Blowup.UniversalProperty
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

import QPainleve.AlgebraicGeometry.Blowup.Affine
import QPainleve.AlgebraicGeometry.Blowup.Point.Fiber
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import QPainleve.Geometry.Toric.BaseChange.FiniteType
import QPainleve.Geometry.Toric.BaseChange.Subfan
import QPainleve.Geometry.Toric.Fan.TwoDimensional
import TauCeti.AlgebraicGeometry.Blowup.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

/-!
# Star subdivisions and blowups of distinguished sections

The affine comparison at a two-dimensional cone extends to the entire regular
surface fan by taking pullbacks along its cone charts. The subdivision is unchanged
over the other charts. Over a field the center is the distinguished point of the
chosen cone.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

universe u

variable (k : Type u) [CommRing k] {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

variable {Φ} (hΦ : Φ.IsRegular) (σ : Φ.cones)
  (hN : Module.finrank ℤ N = 2) (hc : Nat.card (ToricRay σ.val) = 2)

private theorem finiteFanSchemeHom_comp_eqToIso_hom {A B C : Fan i} (h : B = C)
    (f : FanHom A B) (g : FanHom A C) (hfg : f.latticeMap = g.latticeMap) :
    f.finiteFanSchemeHom k ≫ (eqToIso (congrArg (Fan.finiteFanScheme k) h)).hom =
      g.finiteFanSchemeHom k := by
  subst C
  simpa using congrArg (FanHom.finiteFanSchemeHom k) (FanHom.ext hfg)

private theorem eqToIso_hom_comp_finiteFanSchemeHom {A B C : Fan i} (h : A = B)
    (f : FanHom B C) (g : FanHom A C) (hfg : f.latticeMap = g.latticeMap) :
    (eqToIso (congrArg (Fan.finiteFanScheme k) h)).hom ≫ f.finiteFanSchemeHom k =
      g.finiteFanSchemeHom k := by
  subst B
  simpa using congrArg (FanHom.finiteFanSchemeHom k) (FanHom.ext hfg)

private theorem isPullback_subdivision_of_localFans {A B A' B' : Fan i}
    (h : A.IsSubdivision B) (h' : A'.IsSubdivision B')
    (S : Set (PointedCone ℝ V)) (hS : S ⊆ B.cones)
    (hface : ∀ ⦃κ τ⦄, κ ∈ S → τ.IsFaceOf κ → τ ∈ S)
    (ha : A'.cones = h.toFanHom.preimageCones S) (hb : B'.cones = S)
    (a : FanHom A' A) (b : FanHom B' B)
    (ha₀ : a.latticeMap = AddMonoidHom.id N) (hb₀ : b.latticeMap = AddMonoidHom.id N) :
    IsPullback (a.finiteFanSchemeHom k) (h'.toFanHom.finiteFanSchemeHom k)
      (h.toFanHom.finiteFanSchemeHom k) (b.finiteFanSchemeHom k) := by
  let f := h.toFanHom
  let ia := A.subfanInclusion (f.preimageCones S) (f.preimageCones_subset S)
    (f.preimageCones_closedUnderFaces S hface)
  let ib := B.subfanInclusion S hS hface
  have ea : f.preimageSubfan S hface = A' := Fan.ext ((Fan.subfan_cones ..).trans ha.symm)
  have eb : B.subfan S hS hface = B' := Fan.ext ((Fan.subfan_cones ..).trans hb.symm)
  have h₁ : (eqToIso (congrArg (Fan.finiteFanScheme k) ea)).hom ≫ a.finiteFanSchemeHom k =
      ia.finiteFanSchemeHom k := eqToIso_hom_comp_finiteFanSchemeHom k ea a ia (by
    rw [ha₀, subfanInclusion_latticeMap])
  have h₂ : (eqToIso (congrArg (Fan.finiteFanScheme k) eb)).hom ≫ b.finiteFanSchemeHom k =
      ib.finiteFanSchemeHom k := eqToIso_hom_comp_finiteFanSchemeHom k eb b ib (by
    rw [hb₀, subfanInclusion_latticeMap])
  have h₃ := finiteFanSchemeHom_comp_eqToIso_hom k eb (f.restrictToPreimage S hS hface)
    (h'.toFanHom.comp (ea.symm ▸ FanHom.id A')) (by
      rw [FanHom.restrictToPreimage_latticeMap, FanHom.comp_latticeMap,
        IsSubdivision.toFanHom_latticeMap, IsSubdivision.toFanHom_latticeMap]
      cases ea
      simp)
  have h₄ : (ea.symm ▸ FanHom.id A' : FanHom (f.preimageSubfan S hface) A').finiteFanSchemeHom k =
      (eqToIso (congrArg (Fan.finiteFanScheme k) ea)).hom := by
    cases ea
    simp [FanHom.finiteFanSchemeHom_id]
  refine (f.isPullback_preimageSubfan_finiteFanSchemeHom k S hS hface).of_iso
    (eqToIso (congrArg (Fan.finiteFanScheme k) ea)) (Iso.refl _)
    (eqToIso (congrArg (Fan.finiteFanScheme k) eb)) (Iso.refl _) ?_ ?_ (by simp [f]) ?_
  · simpa using h₁.symm
  · rwa [FanHom.finiteFanSchemeHom_comp k, h₄] at h₃
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
local notation "π" => FanHom.finiteFanSchemeHom k (IsSubdivision.toFanHom F)
local notation "I" => Scheme.Hom.ker (Φ.distinguishedSection (R := k) σ)
local notation "J" => RingHom.ker
  (AlgHom.toRingHom (facePointAlgebraHom Φ.lattice (⊤ : σ.val.Face) k))

private def facesInclusion (τ : Φ.cones) :
    FanHom (Fan.ofCone Φ.lattice (Φ.isToricCone τ.property)) Φ :=
  FanHom.ofLatticeMap _ _ (AddMonoidHom.id N) fun κ hκ ↦ by
    rw [IsIntegralLattice.extend_id, PointedCone.map_id]
    exact ⟨τ.val, τ.property, ((Fan.mem_ofCone_cones _ _).1 hκ).le⟩

private theorem chartι_comp_facesInclusion (τ : Φ.cones) :
    (Fan.ofCone Φ.lattice (Φ.isToricCone τ.property)).affineChartι k
        ⟨τ.val, (Fan.mem_ofCone_cones _ _).2 (.refl _)⟩ ≫
      (facesInclusion τ).finiteFanSchemeHom k = Φ.affineChartι k τ := by
  have hmap : (facesInclusion τ).realMap = LinearMap.id := by
    rw [facesInclusion, FanHom.ofLatticeMap_realMap, IsIntegralLattice.extend_id]
  rw [(facesInclusion τ).affineChartι_comp_finiteFanSchemeHom k _ τ (by
    rw [hmap]
    exact Set.mapsTo_id (τ.val : Set V))]
  have hlattice : (facesInclusion τ).latticeMap = AddMonoidHom.id N :=
    FanHom.ofLatticeMap_latticeMap ..
  simp only [hmap, hlattice, affineChartMap_id, Category.id_comp]

include hΦ hN hc in
private theorem exists_isPullback_starSubdivisionAlong_rees :
    ∃ j : Proj (reesAlgebra.grade J) ⟶ (Fan.finiteFanScheme k Ψ),
      IsPullback j (Proj.toSpecCoeff (reesAlgebra.grade J)) π (Φ.affineChartι k σ) := by
  let hσ := isRegular_iff.1 hΦ _ σ.property
  let A := ToricRay.faceFinset (PointedCone.IsFaceOf.refl σ.val) hσ.fg
  let P := Fan.starSubdivision Φ.lattice A hσ
  let Q := Fan.ofCone Φ.lattice hσ.toIsToricCone
  obtain ⟨hA, e, he⟩ := exists_iso_reesBlowup_starSubdivision Φ.lattice k hσ hN hc
  let q : Q.cones := ⟨σ.val, (Fan.mem_ofCone_cones _ _).2 (.refl _)⟩
  let a : FanHom P Ψ := FanHom.ofLatticeMap _ _ (AddMonoidHom.id N) fun κ hκ ↦ by
    rw [IsIntegralLattice.extend_id, PointedCone.map_id]
    exact ⟨κ, (Φ.mem_starSubdivisionAlong_cones hΦ σ.property).2
      (Or.inr ⟨σ.val, σ.property, le_rfl, hκ⟩), le_rfl⟩
  let b := facesInclusion σ
  have hp := isPullback_subdivision_of_localFans k F
    (Fan.starSubdivision_isSubdivision Φ.lattice A hσ hA) {τ | τ.IsFaceOf σ.val}
    (Φ.isFaceOf_subset_cones σ.property) (fun _ _ ht hr ↦ hr.trans ht)
    (preimageCones_starSubdivisionAlong_faces hΦ σ hN hc).symm
    (Set.ext fun _ ↦ Fan.mem_ofCone_cones ..) a b
    (FanHom.ofLatticeMap_latticeMap ..) (FanHom.ofLatticeMap_latticeMap ..)
  have he' : e.hom ≫ Proj.toSpecCoeff (reesAlgebra.grade J) ≫ Q.affineChartι k q =
      (Fan.starSubdivision_isSubdivision Φ.lattice A hσ hA).toFanHom.finiteFanSchemeHom k := by
    simpa only [toSpecCoeff_reesAlgebra, Category.assoc] using he
  have hq : IsIso (Q.affineChartι k q) := isIso_affineChartι_ofCone k _ _
  refine ⟨e.inv ≫ a.finiteFanSchemeHom k, hp.of_iso e (Iso.refl _) (asIso (Q.affineChartι k q)).symm
    (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]) ?_
    (by simp) ?_⟩
  · apply (cancel_mono (Q.affineChartι k q)).mp
    simpa only [Category.assoc, Iso.symm_hom, asIso_inv, IsIso.inv_hom_id, Category.comp_id]
      using he'.symm
  · have hb := chartι_comp_facesInclusion k σ
    apply (cancel_epi (Q.affineChartι k q)).mp
    simpa only [Category.comp_id, Iso.refl_hom, Category.assoc, Iso.symm_hom, asIso_inv,
      IsIso.hom_inv_id_assoc, b, Q, q] using hb

private theorem exists_isPullback_starSubdivisionAlong_otherChart
    (τ : Φ.cones) (hστ : ¬ σ ≤ τ) :
    ∃ j : affineChart k Φ.lattice τ.val ⟶ (Fan.finiteFanScheme k Ψ),
      IsPullback j (𝟙 _) π (Φ.affineChartι k τ) := by
  have hτ : τ.val ∈ Fan.cones Ψ :=
    Φ.mem_starSubdivisionAlong_cones_of_not_le hΦ σ.property τ.property hστ
  exact ⟨_, (F).isPullback_affineChartι k hτ τ.property⟩

private theorem comap_ker_distinguishedSection :
    (I).comap (Φ.affineChartι k σ) =
      ofIdealTop ((J).map
        (Scheme.ΓSpecIso (.of (affineChartRing k Φ.lattice σ.val))).inv.hom) := by
  let p := Spec.map
    (CommRingCat.ofHom (facePointAlgebraHom Φ.lattice (⊤ : σ.val.Face) k).toRingHom)
  have hclosed := Φ.isClosedImmersion_distinguishedSection (R := k) σ
  have hp : IsPullback p (𝟙 _) (Φ.affineChartι k σ) (Φ.distinguishedSection (R := k) σ) :=
    IsPullback.of_vert_isIso_mono ⟨by simp [p, distinguishedSection_def]⟩
  rw [← ker_eq_comap_of_isPullback _ hp, Scheme.Hom.ker_Spec_map]
  rfl

private theorem comap_ker_distinguishedSection_otherChart (τ : Φ.cones)
    (hστ : ¬ σ ≤ τ) :
    (I).comap (Φ.affineChartι k τ) = ⊤ := by
  have hclosed := Φ.isClosedImmersion_distinguishedSection (R := k) σ
  rw [← support_eq_bot_iff]
  apply SetLike.coe_injective
  rw [support_comap, TopologicalSpace.Closeds.coe_preimage,
    (Φ.distinguishedSection (R := k) σ).support_ker,
    (Φ.distinguishedSection (R := k) σ).isClosedEmbedding.isClosed_range.closure_eq]
  exact Set.eq_empty_iff_forall_notMem.mpr fun x ⟨y, hy⟩ ↦
    hστ ((Φ.distinguishedSection_mem_range_affineChartι_iff σ τ y).1 ⟨x, hy.symm⟩)

include hΦ hN hc in
private theorem exists_starSubdivisionAlong_localComparison (τ : Φ.cones) :
    ∃ (W : Scheme) (a : W ⟶ Fan.finiteFanScheme k Ψ) (b : W ⟶ (I).blowup)
      (q : W ⟶ affineChart k Φ.lattice τ.val), IsPullback a q π (Φ.affineChartι k τ) ∧
        IsPullback b q (I).blowupToBase (Φ.affineChartι k τ) := by
  by_cases ht : σ = τ
  · subst τ
    obtain ⟨a, ha⟩ := exists_isPullback_starSubdivisionAlong_rees k hΦ σ hN hc h₀
    obtain ⟨b, hb⟩ := (I).exists_isPullback_toSpecCoeff_reesAlgebra
      (Φ.affineChartι k σ) (J) (comap_ker_distinguishedSection k σ)
    exact ⟨_, a, b, _, ha, hb⟩
  · have hστ : ¬ σ ≤ τ := fun h ↦ ht (eq_of_le_fullCone hΦ hN hc h)
    obtain ⟨a, ha⟩ := exists_isPullback_starSubdivisionAlong_otherChart k hΦ σ h₀ τ hστ
    let j := Φ.affineChartι k τ
    have : IsOpenImmersion j := Fan.isOpenImmersion_affineChartι k τ
    have hjtop : (I).comap j = ⊤ := comap_ker_distinguishedSection_otherChart k σ τ hστ
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
    ∃ e : Fan.finiteFanScheme k Ψ ≅ (I).blowup, e.hom ≫ (I).blowupToBase = π := by
  choose W a b q ha hb using exists_starSubdivisionAlong_localComparison k hΦ σ hN hc h₀
  have haOpen (τ) : IsOpenImmersion (a τ) :=
    MorphismProperty.of_isPullback (ha τ).flip inferInstance
  have hbOpen (τ) : IsOpenImmersion (b τ) :=
    MorphismProperty.of_isPullback (hb τ).flip inferInstance
  have hrange {Z : Scheme} (g : Z ⟶ (Φ.finiteFanScheme k))
      {j : ∀ τ, W τ ⟶ Z} (hj : ∀ τ, IsPullback (j τ) (q τ) g (Φ.affineChartι k τ))
      (z : Z) : ∃ τ, z ∈ Set.range (j τ) := by
    obtain ⟨τ, x, hx⟩ := Φ.exists_affineChartι_apply_eq k (g z)
    refine ⟨τ, ?_⟩
    have hz : z ∈ Set.range (pullback.fst g (Φ.affineChartι k τ)) := by
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
private theorem isEffectiveCartier_comap_distinguishedSection_zeroChart :
    ((I).comap (Φ.affineChartι k ⟨⊥, Φ.bot_mem σ.property⟩)).IsEffectiveCartier := by
  let τ : Φ.cones := ⟨⊥, Φ.bot_mem σ.property⟩
  have hστ : ¬ σ ≤ τ := fun h ↦ ne_bot_of_card_toricRay_eq_two hc (le_bot_iff.mp h)
  have hcomap := comap_ker_distinguishedSection_otherChart k σ τ hστ
  rw [hcomap]
  exact isEffectiveCartier_top _

include hΦ hN hc in
/-- The star subdivision of a regular rank-two fan at a two-dimensional cone is
isomorphic to the blowup at the distinguished section of that cone over
the original toric scheme. The isomorphism identifies the zero-cone chart with its
canonical lift to the blowup. -/
theorem exists_iso_blowup_starSubdivisionAlong :
    let t := Φ.affineChartι k ⟨⊥, Φ.bot_mem σ.property⟩
    ∃ (h₀ : σ.val ≠ ⊥)
      (e : (Φ.starSubdivisionAlong hΦ σ.property).finiteFanScheme k ≅
        (Φ.distinguishedSection (R := k) σ).ker.blowup)
      (ht : ((Φ.distinguishedSection (R := k) σ).ker.comap t).IsEffectiveCartier),
      e.hom ≫ (Φ.distinguishedSection (R := k) σ).ker.blowupToBase =
        (Φ.starSubdivisionAlong_isSubdivision hΦ σ.property h₀).toFanHom.finiteFanSchemeHom k ∧
      ∀ hn : Nonempty (Φ.starSubdivisionAlong hΦ σ.property).cones,
        (Φ.starSubdivisionAlong hΦ σ.property).affineChartι k
          ⟨⊥, (Φ.starSubdivisionAlong hΦ σ.property).bot_mem hn.some.property⟩ ≫ e.hom =
          (Φ.distinguishedSection (R := k) σ).ker.blowupLift t ht := by
  let h₀ := ne_bot_of_card_toricRay_eq_two hc
  obtain ⟨e, he⟩ := exists_iso_blowup_starSubdivisionAlong_over k hΦ σ hN hc h₀
  have ht := isEffectiveCartier_comap_distinguishedSection_zeroChart k σ hc
  refine ⟨h₀, e, ht, he, fun hn ↦ (I).eq_blowupLift ht ?_⟩
  rw [Category.assoc, he, IsSubdivision.affineChartι_comp_finiteFanSchemeHom k]

end LocalComparison

section ClosedPoint

variable (k : Type u) [Field k] {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

local notation "pt" => IsLocalRing.closedPoint k

/-- The blowup at the distinguished point of a regular toric surface has that point as center. -/
theorem centre_eq_singleton_distinguishedSection_of_blowup
    (hΦ : Φ.IsRegular) (hN : Module.finrank ℤ N = 2) (σ : Φ.cones)
    {Y : Scheme.{u}} (f : Y ⟶ Φ.finiteFanScheme k)
    (w : Y ≅ (Φ.distinguishedSection (R := k) σ).ker.blowup)
    (hw : w.hom ≫ (Φ.distinguishedSection (R := k) σ).ker.blowupToBase = f) :
    f.centre = {Φ.distinguishedSection (R := k) σ pt} := by
  let s := Φ.finiteFanSchemeToSpec k
  let q := Φ.distinguishedSection (R := k) σ
  let : SmoothOfRelativeDimension 2 s :=
    hN ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec (R := k) hΦ
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 s
  have hr : Set.range q = {q pt} :=
    Set.range_eq_singleton fun x ↦ congrArg q (Subsingleton.elim x _)
  have hclosed : IsClosed ({q pt} : Set (Φ.finiteFanScheme k)) :=
    hr ▸ q.isClosedEmbedding.isClosed_range
  have := isRegularLocalRing_stalk_of_smooth s (q pt)
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq s 2).mp
    inferInstance).2 _ hclosed
  rw [← hw, Scheme.Hom.centre_def, Scheme.Hom.isoLocus_comp_of_isIso, ← Scheme.Hom.centre_def,
    (Φ.distinguishedSection (R := k) σ).ker_eq_ker_fromSpecResidueField,
    Scheme.ker_fromSpecResidueField_eq_vanishingIdeal]
  exact centre_blowupToBase_closed_point hclosed hdim

/-- The blowup at the distinguished point fails to be an isomorphism at that point. -/
theorem notMem_isoLocus_distinguishedSection_of_blowup
    (hΦ : Φ.IsRegular) (hN : Module.finrank ℤ N = 2) (σ : Φ.cones)
    {Y : Scheme.{u}} (f : Y ⟶ Φ.finiteFanScheme k)
    (w : Y ≅ (Φ.distinguishedSection (R := k) σ).ker.blowup)
    (hw : w.hom ≫ (Φ.distinguishedSection (R := k) σ).ker.blowupToBase = f) :
    Φ.distinguishedSection (R := k) σ pt ∉ f.isoLocus := by
  have hcentre := Φ.centre_eq_singleton_distinguishedSection_of_blowup k hΦ hN σ f w hw
  have hmem : Φ.distinguishedSection (R := k) σ pt ∈ f.centre := by
    rw [hcentre]
    exact Set.mem_singleton _
  simpa only [Scheme.Hom.centre_def, Set.mem_compl_iff, SetLike.mem_coe] using hmem

end ClosedPoint

end TauCeti.Toric.Fan

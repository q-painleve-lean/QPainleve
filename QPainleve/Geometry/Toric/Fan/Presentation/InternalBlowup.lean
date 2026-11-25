/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Presentation.Basic

import QPainleve.AlgebraicGeometry.Blowup.Pullback
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Basic
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.AlongBoundary
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.CurvePoint
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import QPainleve.Geometry.Toric.Fan.Boundary.SmoothPoint
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

/-!
# Internal blowups of pairs with toric presentations

Blowing up a smooth closed point of the boundary lifts the original nodal tower.
The lifted center is a smooth point of the strict boundary of the ordered toric
model and determines one additional binomial center on the same fan. The comparison
is cartesian and identifies the strict boundary ideals.

The construction implements the first observation in the proof of
[Gross, Hacking and Keel, Proposition 1.3][GHK]. It also applies in reverse along
a ruled elementary transformation that blows up a node and contracts the old fiber.

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public section

open AlgebraicGeometry CategoryTheory Limits
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  (b : Module.Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  {m : ℕ} (ρ : Fin m → Φ.Ray) (c : Fin m → ℂˣ)
  {X : Scheme} {s : X ⟶ Spec (.of ℂ)} {D : X.IdealSheafData}
  {p : D.subscheme}

local notation "A" => internalBlowupTower b ρ c
local notation "B" => Φ.boundaryIdeal h₀
local notation "j" => WithBoundary.boundaryι (Sigma.snd A)
local notation "J" =>
  Scheme.Hom.ker (Scheme.fromSpecResidueField (Scheme.IdealSheafData.subscheme D) p)
local notation "I" => Scheme.IdealSheafData.map J (Scheme.IdealSheafData.subschemeι D)
local notation "E" =>
  Scheme.Hom.ker (Scheme.IdealSheafData.blowupMap I (Scheme.IdealSheafData.subschemeι D))
local notation "sΦ" => Φ.algebraicRealizationStructureMap

include hΦ hc in
private theorem exists_center_of_internalBlowup
    [IsReduced D.subscheme]
    (f : (A).1 ⟶ X) (hf : f ≫ s = (A).2.toTower.toBase ≫ sΦ)
    (hD : (D.comap f).radical = (j).ker)
    (hp : IsClosed ({p} : Set D.subscheme))
    (hs : ((D.subschemeι ≫ s).stalkMap p).hom.FormallySmooth)
    (hiso : D.subschemeι p ∈ f.isoLocus) :
    ∃ (r : Φ.Ray) (a : ℂˣ) (d : (B).subscheme ⟶ D.subscheme),
      d ≫ D.subschemeι = (j) ≫ f ∧
      (r.internalCenter b a).val.map (j) = (I).comap f := by
  let P := (D.comap f).radical
  let g := subschemeMap P D f (le_map_iff_comap_le.mpr (le_radical _))
  obtain ⟨e, he⟩ := P.exists_iso_of_comap_eq_ker (Iso.refl _) (j) (by simpa using hD)
  simp only [Iso.refl_hom, Category.comp_id] at he
  let d := e.hom ≫ g
  have hd : d ≫ D.subschemeι = (j) ≫ f := by
    rw [Category.assoc, subschemeMap_subschemeι, ← Category.assoc, he]
  have hp' : p ∈ g.isoLocus := D.preimage_isoLocus_le_subschemeMap_radical f hiso
  obtain ⟨q, hq, hqd, _⟩ :=
    g.exists_comap_ker_fromSpecResidueField_of_isIso_morphismRestrict p hp g.isoLocus hp'
  let z := e.inv q
  have hz : d z = p := by simp [d, z, hqd]
  have hzclosed : IsClosed ({z} : Set (B).subscheme) := by
    simpa only [Set.image_singleton] using e.inv.isClosedMap _ hq
  have hdloc : IsIso (d.stalkMap z) := by
    rw [Scheme.Hom.stalkMap_comp]
    have hq' : e.hom z = q := by simp [z, ← Scheme.Hom.comp_apply]
    have hgIso : IsIso (g.stalkMap (e.hom z)) := g.isIso_stalkMap_of_mem_isoLocus
      (by rwa [hq', hqd])
    have heIso : IsIso (e.hom.stalkMap z) :=
      (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion e.hom)).2 z
    exact IsIso.comp_isIso' hgIso heIso
  have hstruct : d ≫ D.subschemeι ≫ s = (B).subschemeι ≫ sΦ := by
    rw [← Category.assoc, hd, Category.assoc, hf, WithBoundary.boundaryι_toBase_assoc]
  have hzs : (((B).subschemeι ≫ sΦ).stalkMap z).hom.FormallySmooth := by
    rw [← hstruct, Scheme.Hom.stalkMap_comp]
    exact (RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ _).mpr (hz.symm ▸ hs)
  obtain ⟨r, a, ha⟩ := exists_internalCenter_eq_ker_fromSpecResidueField b hΦ hc z hzclosed hzs
  have hclosed : IsClosed ({D.subschemeι p} : Set X) := by
    simpa only [Set.image_singleton] using D.subschemeι.isClosedEmbedding.isClosedMap _ hp
  refine ⟨r, a, d, hd, ?_⟩
  rw [ha, (j).map_ker_fromSpecResidueField, D.subschemeι.map_ker_fromSpecResidueField]
  have hpoint : f ((j) z) = D.subschemeι p := by
    rw [← Scheme.Hom.comp_apply, ← hd, Scheme.Hom.comp_apply, hz]
  rw [← hpoint]
  exact (f.comap_ker_fromSpecResidueField_of_mem_isoLocus
    (q := (j) z) (hpoint.symm ▸ hclosed) (hpoint.symm ▸ hiso)).symm

include hΦ hc in
private theorem exists_isPullback_snoc_internalBlowupTower [IsReduced D.subscheme]
    (f : (A).1 ⟶ X) (hf : f ≫ s = (A).2.toTower.toBase ≫ sΦ)
    (hD : (D.comap f).radical = (j).ker)
    (hp : IsClosed ({p} : Set D.subscheme))
    (hs : ((D.subschemeι ≫ s).stalkMap p).hom.FormallySmooth)
    (hJ : (J).IsEffectiveCartier) (hiso : D.subschemeι p ∈ f.isoLocus) :
    ∃ (r : Φ.Ray) (a : ℂˣ),
      let A' := internalBlowupTower b (Fin.snoc ρ r) (Fin.snoc c a)
      ∃ (l : A'.1 ⟶ (A).1) (g : A'.1 ⟶ (I).blowup),
        IsPullback l g f (I).blowupToBase ∧
        l ≫ (A).2.toTower.toBase = A'.2.toTower.toBase ∧
        ((E).comap g).radical = A'.2.boundaryι.ker := by
  obtain ⟨r, a, d, hd, hcenter⟩ := exists_center_of_internalBlowup b hΦ hc ρ c f hf hD hp hs hiso
  refine ⟨r, a, ?_⟩
  have hρ : Fin.snoc ρ r ∘ Fin.castSucc = ρ := by funext k; simp
  have hc' : Fin.snoc c a ∘ Fin.castSucc = c := by funext k; simp
  rw [internalBlowupTower_succ b, Fin.snoc_last, Fin.snoc_last, hρ, hc']
  let C := (r.internalCenter b a).val
  let U := (A).2.snoc C (r.internalCenter b a).property
  let e : (C.map (j)).blowup ≅ ((I).comap f).blowup :=
    blowupIso (Iso.refl _) (hcenter.trans (comap_id _).symm)
  let l := (C.map (j)).blowupToBase
  let g := e.hom ≫ (I).blowupMap f
  have hsupport : ((I).support : Set X) ⊆ f.isoLocus := by
    rw [D.subschemeι.map_ker_fromSpecResidueField,
      Scheme.support_ker_fromSpecResidueField_of_isClosed
        (by simpa only [Set.image_singleton] using D.subschemeι.isClosedEmbedding.isClosedMap _ hp)]
    exact Set.singleton_subset_iff.mpr hiso
  have hpb : IsPullback l g f (I).blowupToBase :=
    ((I).isPullback_blowupMap_of_support_subset_isoLocus f hsupport).of_iso'
      e (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [e, l]) (by simp [g]) (by simp) (by simp)
  have hcart : ((I).comap D.subschemeι).IsEffectiveCartier := by simpa using hJ
  let j' := (I).blowupLift D.subschemeι hcart
  have : IsClosedImmersion j' := (I).isClosedImmersion_blowupLift _ _
  have hj' : j' ≫ (I).blowupToBase = D.subschemeι := blowupLift_blowupToBase _ _ _
  have hj'l : U.boundaryι ≫ l = (j) := WithBoundary.boundaryι_snoc_blowupToBase _ _ _
  -- The two embeddings of the strict boundary agree by the blowup universal property.
  have hcomm : U.boundaryι ≫ g = d ≫ j' := by
    apply (I).blowup_hom_ext
    · rw [Category.assoc, hpb.w.symm, ← Category.assoc, hj'l, ← hd, Category.assoc, hj']
    · rw [Category.assoc, hpb.w.symm, ← Category.assoc, hj'l, comap_comp, ← hcenter,
        comap_map_of_isClosedImmersion]
      exact (r.internalCenter b a).property
  have hker : j'.ker = (E) := by
    rw [ker_blowupLift, ker_blowupMap]
  have : IsClosedImmersion (j' ≫ (I).blowupToBase) := hj'.symm ▸ inferInstance
  have : IsClosedImmersion (U.boundaryι ≫ l) := hj'l.symm ▸ inferInstance
  have : IsReduced (B).subscheme := by
    rw [Φ.boundaryIdeal_def]
    infer_instance
  refine ⟨l, g, hpb, ?_, ?_⟩
  · rw [WithBoundary.toTower_snoc, toBase_snoc]
  · rw [← hker]
    exact radical_comap_ker_eq_of_isPullback hpb.flip j' U.boundaryι d hcomm
      (by simpa only [hj', hj'l, ker_subschemeι] using hD)

variable [IsLocallyNoetherian X] {Y : Scheme} {n : ℕ} {T : BlowupTower X n Y}

include hΦ hc in
/-- An internal blowup of a pair with a specified toric presentation has a
presentation on the same fan. Its nodal tower is the pullback of the given
nodal tower, and its ordered internal tower appends one binomial center to
the given list. The isomorphism is over the ground field and identifies the
reduced total transform of the new boundary with the strict toric boundary. -/
theorem exists_toric_presentation_of_internal_blowup
    (hT : IsNodalBoundaryTower D s (𝟙 X) T)
    (e : (A).1 ≅ Y)
    (he : e.hom ≫ T.toBase ≫ s = (A).2.toTower.toBase ≫ sΦ)
    (hD : ((D.comap T.toBase).comap e.hom).radical = (j).ker)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s))
    (hp : IsClosed ({p} : Set D.subscheme))
    (hs : ((D.subschemeι ≫ s).stalkMap p).hom.FormallySmooth) :
    ∃ (r : Φ.Ray) (a : ℂˣ) (Z : Scheme) (R : BlowupTower (I).blowup n Z)
      (g : Z ⟶ Y),
      IsNodalBoundaryTower E ((I).blowupToBase ≫ s) (𝟙 (I).blowup) R ∧
      IsPullback g R.toBase T.toBase (I).blowupToBase ∧
      let A' := internalBlowupTower b (Fin.snoc ρ r) (Fin.snoc c a)
      ∃ d : A'.1 ≅ Z,
        d.hom ≫ g ≫ e.inv ≫ (A).2.toTower.toBase = A'.2.toTower.toBase ∧
        d.hom ≫ R.toBase ≫ (I).blowupToBase ≫ s = A'.2.toTower.toBase ≫ sΦ ∧
        (((E).comap R.toBase).radical).comap d.hom = A'.2.boundaryι.ker := by
  let : IsReduced D.subscheme := hN.isReduced
  let := hN.syntomic
  have hJ := (D.subschemeι ≫ s).isEffectiveCartier_ker_fromSpecResidueField_of_mem_smoothLocus hp
    (Scheme.Hom.mem_smoothLocus.mpr hs)
  have hclosed : IsClosed ({D.subschemeι p} : Set X) := by
    simpa only [Set.image_singleton] using D.subschemeι.isClosedEmbedding.isClosedMap _ hp
  have hnot : ¬ D.IsNodeOfReducedBoundary s (D.subschemeι p) := by
    rw [D.isNodeOfReducedBoundary_iff_of_isReduced]
    rintro ⟨z, hz, hn⟩
    have hz' := D.subschemeι.isClosedEmbedding.injective hz
    exact hn.not_formallySmooth_stalkMap (hz'.symm ▸ hs)
  have hI : ∀ x ∈ ((I).support : Set X), ¬ D.IsNodeOfReducedBoundary s x := by
    rw [D.subschemeι.map_ker_fromSpecResidueField,
      Scheme.support_ker_fromSpecResidueField_of_isClosed hclosed]
    exact fun x hx ↦ (Set.mem_singleton_iff.mp hx).symm ▸ hnot
  have hpiso : D.subschemeι p ∈ T.toBase.isoLocus := by
    by_contra h
    apply hnot
    exact hT.centre_subset_nodes (by simpa only [Scheme.Hom.centre_def, Set.mem_compl_iff,
      SetLike.mem_coe] using h)
  let f := e.hom ≫ T.toBase
  have hfiso : D.subschemeι p ∈ f.isoLocus := by
    simpa only [f, Scheme.Hom.isoLocus_comp_of_isIso] using hpiso
  obtain ⟨r, a, l, v, hv, hl, hvB⟩ := exists_isPullback_snoc_internalBlowupTower b hΦ hc ρ c f
    (by simpa only [Category.assoc, f] using he) (by simpa only [f, comap_comp] using hD)
    hp hs hJ hfiso
  obtain ⟨Z, R, g, hR, hg⟩ := hT.exists_isPullback_blowup_of_avoids_nodes I hI E
    (comap_ker_blowupMap_subschemeι_exceptionalCompl I D)
  -- Both the appended toric model and the lifted nodal model realize this fiber product.
  have hpb : IsPullback (l ≫ e.hom) v T.toBase (I).blowupToBase :=
    hv.of_iso' (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp [f]) (by simp)
  let d := hpb.isoIsPullback _ _ hg
  have hd : d.hom ≫ R.toBase = v := hpb.isoIsPullback_hom_snd _ _ hg
  have hdg : d.hom ≫ g = l ≫ e.hom := hpb.isoIsPullback_hom_fst _ _ hg
  refine ⟨r, a, Z, R, g, hR, hg, d, ?_, ?_, ?_⟩
  · rw [reassoc_of% hdg, Iso.hom_inv_id_assoc, hl]
  · rw [reassoc_of% hd, ← Category.assoc v, ← hv.w, Category.assoc, ← hl]
    have hf : f ≫ s = (A).2.toTower.toBase ≫ sΦ := by simpa only [f, Category.assoc] using he
    exact (Category.assoc _ _ _).trans (congrArg (l ≫ ·) hf)
  · rwa [← radical_comap_of_isOpenImmersion, ← comap_comp, hd]

include hΦ hc in
/-- Transport a toric presentation back across a nodal tower followed by an
internal contraction. In particular, for a one-step nodal tower this transports
a presentation back across a ruled elementary transformation at a boundary node.
The new nodal tower concatenates the given one with the lifted tower from the
target presentation, and the ordered internal tower retains the original centers
and appends one. -/
theorem exists_toric_presentation_of_nodalTower_and_internal_blowdown
    (hT : IsNodalBoundaryTower D s (𝟙 X) T)
    (e : (A).1 ≅ Y)
    (he : e.hom ≫ T.toBase ≫ s = (A).2.toTower.toBase ≫ sΦ)
    (hD : ((D.comap T.toBase).comap e.hom).radical = (j).ker)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s))
    (hp : IsClosed ({p} : Set D.subscheme))
    (hs : ((D.subschemeι ≫ s).stalkMap p).hom.FormallySmooth)
    {X₀ Y₀ : Scheme} {s₀ : X₀ ⟶ Spec (.of ℂ)} {D₀ : X₀.IdealSheafData}
    {k : ℕ} {U : BlowupTower X₀ k Y₀}
    (hU : IsNodalBoundaryTower D₀ s₀ (𝟙 X₀) U)
    (u : Y₀ ≅ (I).blowup)
    (hu : u.hom ≫ (I).blowupToBase ≫ s = U.toBase ≫ s₀)
    (hD₀ : ((E).comap u.hom).support = (D₀.comap U.toBase).support) :
    ∃ (r : Φ.Ray) (a : ℂˣ) (W : Scheme) (V : BlowupTower X₀ (k + n) W),
      IsNodalBoundaryTower D₀ s₀ (𝟙 X₀) V ∧
      let A' := internalBlowupTower b (Fin.snoc ρ r) (Fin.snoc c a)
      ∃ d : A'.1 ≅ W,
        d.hom ≫ V.toBase ≫ s₀ = A'.2.toTower.toBase ≫ sΦ ∧
        ((D₀.comap V.toBase).comap d.hom).radical = A'.2.boundaryι.ker := by
  obtain ⟨r, a, Z, R, _, hR, _, d, _, hd, hdB⟩ :=
    exists_toric_presentation_of_internal_blowup b hΦ hc ρ c hT e he hD hN hp hs
  obtain ⟨W, V, v, hV, hv, hvB⟩ := hU.exists_append_of_iso hR u hu hD₀
  have hu' : u.inv ≫ U.toBase ≫ s₀ = (I).blowupToBase ≫ s := by
    rw [← hu, Iso.inv_hom_id_assoc]
  refine ⟨r, a, W, V, hV, d ≪≫ v.symm, ?_, ?_⟩
  · simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hv, Iso.inv_hom_id_assoc, hu']
      using hd
  · rw [radical_comap_of_isOpenImmersion, hvB, ← comap_comp]
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      using hdB

end TauCeti.Toric.Fan

open TopologicalSpace TauCeti.Toric

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X : Scheme} {b : Module.Basis (Fin 2) ℤ N}
  {D : X.IdealSheafData} {s : X ⟶ Spec (CommRingCat.of ℂ)} {p : X}

local notation "I" => vanishingIdeal (Closeds.mk (closure (Singleton.singleton p)) isClosed_closure)
local notation "π" => blowupToBase I

/-- A toric presentation extends to the strict boundary after blowing up a closed smooth point
of the nodal boundary. -/
theorem HasToricPresentation.internalBlowup [IsLocallyNoetherian X]
    (h : D.HasToricPresentation s b i) (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s))
    (hp : IsClosed ({p} : Set X)) {q : D.subscheme} (hq : D.subschemeι q = p)
    (hs : ((D.subschemeι ≫ s).stalkMap q).hom.FormallySmooth) :
    ((I).blowupMap D.subschemeι).ker.HasToricPresentation (π ≫ s) b i := by
  have hqclosed : IsClosed ({q} : Set D.subscheme) :=
    D.subschemeι.isClosedEmbedding.isClosed_iff_image_isClosed.mpr (by
      rw [Set.image_singleton, hq]
      exact hp)
  have hI : ((D.subscheme.fromSpecResidueField q).ker).map D.subschemeι = I := by
    rw [D.subschemeι.map_ker_fromSpecResidueField, hq,
      Scheme.ker_fromSpecResidueField_eq_vanishingIdeal]
  obtain ⟨Φ, hΦ, hc, m, r, c, n, Z, T, hT, e, he, hD⟩ := (hasToricPresentation_iff ..).mp h
  let := hc.nonempty_cones
  obtain ⟨r', a, W, U, _, hU, _, d, _, hd, hB⟩ :=
    Fan.exists_toric_presentation_of_internal_blowup b hΦ hc r c hT e he
      ((radical_comap_of_isOpenImmersion _ _).trans hD) hN hqclosed hs
  rw [← hI]
  exact (hasToricPresentation_iff ..).mpr
    ⟨Φ, hΦ, hc, m + 1, Fin.snoc r r', Fin.snoc c a, n, W, U, hU, d, hd, hB⟩

end AlgebraicGeometry.Scheme.IdealSheafData

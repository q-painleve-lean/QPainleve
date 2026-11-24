/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Automorphism
public import QPainleve.Geometry.Toric.Fan.TorusAction.Automorphism

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import QPainleve.Geometry.Toric.Fan.Boundary.Automorphism
import QPainleve.Geometry.Toric.Fan.Boundary.Intersection
import QPainleve.Geometry.Toric.Fan.Boundary.Node
import QPainleve.Geometry.Toric.Fan.Boundary.Normalization
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

/-!
# Torus translations on the branches of the boundary

A torus translation fixes the individual branches of the reduced boundary of a
complete regular toric surface. Its restriction fixes each node as the intersection
of two ray divisors. Over a node, the normalized ray component distinguishes its
branch. This supplies the branch comparison for the toric automorphisms in
[Gross, Hacking and Keel, Proposition 2.6](https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative TopologicalSpace
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData QPainleve.BlowupTower

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]

local notation "X" => Φ.algebraicRealization
local notation "D" => Φ.boundaryIdeal h₀
local notation "C" => Scheme.IdealSheafData.subscheme D
local notation "base" => Spec (CommRingCat.of ℂ)
local notation "I" => Scheme.singularLocus ℂ C
local notation "ν" => Scheme.IdealSheafData.blowupToBase I
local notation "W" => Scheme.IdealSheafData.blowup I
local notation "j" => Scheme.branchSchemeToBlowup ℂ C

omit h₀ in
private theorem fixes_distinguishedPointHom_of_comap_rayBoundaryIdeal_eq
    (hΦ : Φ.IsRegular) (hdim : Module.finrank ℤ N = 2)
    (e : X ≅ X) (he : ∀ ρ, (Φ.rayBoundaryIdeal hΦ ρ).comap e.hom = Φ.rayBoundaryIdeal hΦ ρ)
    (σ : Φ.cones) (hσ : Nat.card (ToricRay σ.val) = 2) (p : base) :
    e.hom (Φ.distinguishedPointHom σ p) = Φ.distinguishedPointHom σ p := by
  obtain ⟨r, t, hrt, -⟩ := Nat.card_eq_two_iff.mp hσ
  let ρ := (Φ.rayEquiv σ).symm r
  let τ := (Φ.rayEquiv σ).symm t
  have hne : ρ.val ≠ τ.val := fun h ↦ hrt ((Φ.rayEquiv σ).symm.injective (Subtype.ext h))
  have hker : (Φ.distinguishedPointHom σ).ker.comap e.hom =
      (Φ.distinguishedPointHom σ).ker := by
    rw [Φ.distinguishedPointHom_def,
      ← Φ.sup_rayBoundaryIdeal_eq_ker_distinguishedPoint hΦ hdim hne σ ρ.property τ.property,
      comap_sup, he, he]
  let f := Φ.distinguishedPointHom σ
  have : IsClosedImmersion f := Φ.isClosedImmersion_distinguishedPointHom σ
  have hs : (f.ker.support : Set X) = {f p} := by
    rw [Scheme.Hom.support_ker, f.isClosedEmbedding.isClosed_range.closure_eq,
      Set.range_eq_singleton (fun q ↦ congrArg f (Subsingleton.elim q p))]
  have hp : e.hom (f p) ∈ ({f p} : Set X) := by
    have h := congrArg (fun J : Scheme.IdealSheafData X ↦ (J.support : Set X)) hker
    rw [support_comap, Closeds.coe_preimage, hs] at h
    exact (Set.ext_iff.mp h (f p)).mpr (Set.mem_singleton _)
  exact Set.mem_singleton_iff.mp hp

variable [PrestableFamily ((Φ.boundaryIdeal h₀).subscheme ↘ Spec (.of ℂ))]
  (hΦ : Φ.IsRegular) (e : Φ.algebraicRealization ≅ Φ.algebraicRealization)
  (d : (Φ.boundaryIdeal h₀).subscheme ≅ (Φ.boundaryIdeal h₀).subscheme)
  [d.hom.IsOver (Spec (.of ℂ))]
  (hd : d.hom ≫ (Φ.boundaryIdeal h₀).subschemeι = (Φ.boundaryIdeal h₀).subschemeι ≫ e.hom)
  (he : ∀ ρ, (Φ.rayBoundaryIdeal hΦ ρ).comap e.hom = Φ.rayBoundaryIdeal hΦ ρ)

local notation "l" => Iso.hom (d.singularLocusBlowupIso (R := ℂ))

include hd he in
private theorem mapsTo_normalizedRay_of_comap_rayBoundaryIdeal_eq (ρ : Φ.Ray) :
    Set.MapsTo l (Φ.boundaryNormalizationComponentEquiv hΦ ρ : Set W)
      (Φ.boundaryNormalizationComponentEquiv hΦ ρ : Set W) := by
  let v := Φ.boundaryNormalizationComponentEquiv hΦ ρ
  let x := (genericPoints.ofComponent v : W)
  let p := (Φ.rayBoundaryPoint hΦ ρ).val
  have hx : (D).subschemeι (ν x) = p := by
    refine IsGenericPoint.eq (S := closure {p}) ?_ isGenericPoint_closure
    rw [IsGenericPoint,
      ← (C).range_blowupComponent_comp (k := ℂ) v (D).subschemeι (D).subschemeι.isClosedMap,
      ← ρ.boundaryNormalizationComponentIso_hom_boundaryComponentι_assoc,
      ρ.boundaryComponentι_subschemeι, Scheme.Hom.comp_base, TopCat.coe_comp,
      (ρ.boundaryNormalizationComponentIso hΦ).hom.surjective.range_comp,
      range_subschemeι, Φ.coe_support_rayBoundaryIdeal]
  have hcomm : l ≫ ν ≫ (D).subschemeι = ν ≫ (D).subschemeι ≫ e.hom := by
    rw [Iso.singularLocusBlowupIso_hom_blowupToBase_assoc, hd]
  have hfix : l x = x := by
    have hp : ν (l x) = ν x := by
      apply (D).subschemeι.injective
      have h := congrArg (fun f : W ⟶ X ↦ f x) hcomm
      simp only [Scheme.Hom.comp_apply, hx] at h ⊢
      exact h.trans ((Φ.comap_rayBoundaryIdeal_eq_iff hΦ e ρ).mp (he ρ))
    have hy := (C).blowupComponentGeneric_mem_isoLocus (k := ℂ) v
    exact (ν).injOn_preimage_isoLocus (Set.mem_preimage.mpr (hp.symm ▸ hy)) hy hp
  rw [← (genericPoints.isGenericPoint_ofComponent v).def]
  have hxmap : Set.MapsTo l ({x} : Set W) {x} := Set.mapsTo_singleton.mpr (by simp [hfix])
  exact hxmap.closure (l).continuous

include hd he in
private theorem branchSchemeIso_apply_eq_self_of_comap_rayBoundaryIdeal_eq
    (hc : Φ.IsComplete) (hdim : Module.finrank ℤ N = 2) (q : Scheme.branchScheme ℂ C) :
    (d.branchSchemeIso (R := ℂ)).hom q = q := by
  let x := j q
  let z := ν x
  have hnodal := PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := C ↘ base)
  have hz : z ∈ (I).support := by
    have h := congrArg (fun f : Scheme.branchScheme ℂ C ⟶ C ↦ f q)
      ((C).branchSchemeToSingularLocus_subschemeι ℂ)
    simp only [Scheme.Hom.comp_apply] at h
    rw [← SetLike.mem_coe]
    simpa only [z, x, ← h] using
      (I).range_subschemeι.le (Set.mem_range_self ((C).branchSchemeToSingularLocus ℂ q))
  have hznode :
      (D).IsNodeOfReducedBoundary Φ.algebraicRealizationStructureMap ((D).subschemeι z) := by
    have hred : IsReduced C := hnodal.isReduced
    apply (D).isNodeOfReducedBoundary_iff_of_isReduced _ _ |>.mpr
    refine ⟨z, rfl, ?_⟩
    rw [← Φ.algebraicRealization_over, ← over_eq_subschemeι_comp]
    exact ((C ↘ base).isNodeAt_iff_notMem_smoothLocus hnodal z).mpr
      (((C).mem_support_singularLocus_iff_notMem_smoothLocus z).mp hz)
  obtain ⟨σ, ⟨hσ, hpoint⟩, -⟩ :=
    (Φ.isNodeOfReducedBoundary_iff_existsUnique_twoRayCone hΦ hc hdim).mp hznode
  have hfix : d.hom z = z := by
    apply (D).subschemeι.injective
    rw [← Scheme.Hom.comp_apply, hd, Scheme.Hom.comp_apply, ← hpoint]
    exact fixes_distinguishedPointHom_of_comap_rayBoundaryIdeal_eq hΦ hdim e he σ hσ _
  obtain ⟨ρ, hρ⟩ := (Φ.boundaryNormalizationComponentEquiv hΦ).surjective (irreducibleComponentOf x)
  have hx : x ∈ (Φ.boundaryNormalizationComponentEquiv hΦ ρ : Set W) :=
    hρ.symm ▸ mem_irreducibleComponentOf x
  have hxl := mapsTo_normalizedRay_of_comap_rayBoundaryIdeal_eq hΦ e d hd he ρ hx
  have hl : l x = x := by
    apply ρ.injOn_blowupToBase_boundaryNormalizationComponent hΦ hxl hx
    rw [← Scheme.Hom.comp_apply, Iso.singularLocusBlowupIso_hom_blowupToBase,
      Scheme.Hom.comp_apply]
    exact hfix
  have : IsClosedImmersion (j) := MorphismProperty.of_isPullback ((C).isPullback_branchScheme ℂ)
    inferInstance
  apply (j).isClosedEmbedding.injective
  rw [← Scheme.Hom.comp_apply, Iso.branchSchemeIso_hom_branchSchemeToBlowup, Scheme.Hom.comp_apply]
  exact hl

include hd he in
/-- An isomorphism of a complete regular toric surface fixing each ray divisor acts
as the identity on the branch scheme of the reduced boundary. -/
theorem branchSchemeIso_eq_refl_of_comap_rayBoundaryIdeal_eq
    (hc : Φ.IsComplete) (hdim : Module.finrank ℤ N = 2) :
    d.branchSchemeIso (R := ℂ) = Iso.refl (Scheme.branchScheme ℂ C) :=
  (d.branchSchemeIso_eq_refl_iff PrestableFamily.atWorstNodalOfRelativeDimensionOne).mpr
    (branchSchemeIso_apply_eq_self_of_comap_rayBoundaryIdeal_eq hΦ e d hd he hc hdim)

local notation "Chars" => (Multiplicative (N →+ ℤ) →* ℂˣ)

/-- The boundary translation is an isomorphism over the ground field. -/
instance isOver_boundaryTranslation_hom (χ : Chars) :
    (boundaryTranslation (Φ := Φ) χ).hom.IsOver base := ⟨by
  rw [(D).over_eq_subschemeι_comp, boundaryTranslation_hom_subschemeι_assoc, comp_over]⟩

/-- Every torus translation acts as the identity on the actual branch scheme of the
reduced boundary of a complete regular toric surface. -/
theorem branchSchemeIso_boundaryTranslation (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hdim : Module.finrank ℤ N = 2) (χ : Chars) :
    (boundaryTranslation (Φ := Φ) χ).branchSchemeIso (R := ℂ) =
      Iso.refl (Scheme.branchScheme ℂ C) :=
  branchSchemeIso_eq_refl_of_comap_rayBoundaryIdeal_eq hΦ (Φ.torusTranslation χ)
    (boundaryTranslation χ) (boundaryTranslation_hom_subschemeι χ)
    (Φ.comap_rayBoundaryIdeal_torusTranslation_hom hΦ χ) hc hdim

variable {n : ℕ} (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray) {c c' : Fin n → ℂˣ}

local notation "Y" a:arg => Sigma.fst (internalBlowupTower b s a)
local notation "T" a:arg => WithBoundary.toTower (Sigma.snd (internalBlowupTower b s a))
local notation "ι" a:arg => WithBoundary.boundaryι (Sigma.snd (internalBlowupTower b s a))

/-- A torus translation lifted through ordered internal blowups acts trivially on the
branches under the canonical identifications of the two strict boundaries with the
original toric boundary. This holds for repeated and infinitely near centers. -/
theorem branchSchemeIso_eq_refl_of_isLift_internalBlowupTower_torusTranslation
    (hreg : Φ.IsRegular) (hc : Φ.IsComplete) (χ : Chars) {g : Y c ≅ Y c'}
    (hg : IsLift (Φ.torusTranslation χ) (T c) (T c') g)
    {a : C ≅ C} [a.hom.IsOver base] (ha : ι c ≫ g.hom = a.hom ≫ ι c') :
    a.branchSchemeIso (R := ℂ) = Iso.refl (Scheme.branchScheme ℂ C) := by
  have h := boundaryι_comp_of_isLift_internalBlowupTower_torusTranslation b s c c' χ hg
  have hEq : a = boundaryTranslation χ :=
    Iso.ext ((cancel_mono (ι c')).mp (ha.symm.trans h))
  subst a
  exact branchSchemeIso_boundaryTranslation hreg hc
    ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)) χ

/-- A Picard-trivial automorphism fixing the strict boundary divisors of an
ordered internal model restricts to a unique boundary automorphism over the base
field, and its induced isomorphism of the branch scheme is the identity. -/
theorem existsUnique_boundaryIso_of_internalBlowupPicardBoundaryAut
    (hreg : Φ.IsRegular) (hc : Φ.IsComplete)
    (g : internalBlowupPicardBoundaryAut b s c hreg) :
    ∃! a : C ≅ C, ∃ ha : a.hom.IsOver base,
      ι c ≫ (g.val.asIso).hom = a.hom ≫ ι c ∧
        (letI := ha; a.branchSchemeIso (R := ℂ) = Iso.refl (Scheme.branchScheme ℂ C)) := by
  obtain ⟨z, rfl⟩ := (internalBlowupPicardBoundaryAutMulEquiv b s c hreg hc).surjective g
  have h := internalBlowupPicardBoundaryAutMulEquiv_isLift b s c hreg hc z
  have hcomm := boundaryι_comp_of_isLift_internalBlowupTower_torusTranslation b s c c _ h
  refine ⟨_, ⟨inferInstance, hcomm, ?_⟩, ?_⟩
  · exact branchSchemeIso_eq_refl_of_isLift_internalBlowupTower_torusTranslation
      b s hreg hc _ h hcomm
  · rintro a ⟨_, ha, -⟩
    exact Iso.ext ((cancel_mono (ι c)).mp (ha.symm.trans hcomm))

end TauCeti.Toric.Fan

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Boundary
public import QPainleve.Geometry.Toric.Fan.Subdivision
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic

import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.Boundary.Node
import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision
import QPainleve.Geometry.Toric.Fan.Smooth
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Factorization
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

/-!
# Nodal blowup towers from toric subdivisions

A subdivision between regular surface fans factors as point blowups of boundary
nodes. The comparison is over the specified toric projection. The ordered
exceptional classes are the total pullbacks of the new ray divisors from the
steps where they first appear.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.IdealSheafData
open QPainleve.BlowupTower TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i}

private theorem IsSubdivision.isNodalBoundaryTower_snoc (h : Ψ.IsSubdivision Φ)
    (hΦ : Nonempty Φ.cones) (hΨ : Ψ.IsRegular) (σ : Ψ.cones)
    (hN : Module.finrank ℤ N = 2) (hc : Nat.card (ToricRay σ.val) = 2)
    {n : ℕ} {Y : Scheme} {T : QPainleve.BlowupTower Φ.algebraicRealization n Y}
    (e : Ψ.algebraicRealization ≅ Y) (he : e.hom ≫ T.toBase = h.toFanHom.algebraicMap)
    (hT : IsNodalBoundaryTower (Φ.boundaryIdeal hΦ) Φ.algebraicRealizationStructureMap (𝟙 _) T) :
    IsNodalBoundaryTower (Φ.boundaryIdeal hΦ) Φ.algebraicRealizationStructureMap (𝟙 _)
      (T.snoc ((Ψ.distinguishedPointHom σ ≫ e.hom).ker)) := by
  let D := (Φ.boundaryIdeal hΦ).comap T.toBase
  let s := Φ.algebraicRealizationStructureMap
  let q := Ψ.distinguishedPointHom σ
  let p := q ≫ e.hom
  let x : Spec (.of ℂ) := IsLocalRing.closedPoint ℂ
  have : IsClosedImmersion q := Ψ.isClosedImmersion_distinguishedPointHom σ
  have : IsClosedImmersion p := inferInstanceAs (IsClosedImmersion (q ≫ e.hom))
  have hp : IsClosed ({p x} : Set Y) :=
    (Set.range_eq_singleton (f := p) (fun y ↦ congrArg p (Subsingleton.elim y x))) ▸
      p.isClosedEmbedding.isClosed_range
  have hn : D.IsNodeOfReducedBoundary (T.toBase ≫ s) (e.hom (q x)) := by
    have hD : (D.comap e.hom).radical = Ψ.boundaryIdeal ⟨σ⟩ := by
      rw [radical_comap_of_isOpenImmersion]
      exact h.radical_comap_boundaryIdeal_of_iso ⟨σ⟩ hΦ T.toBase e he
    have hs : e.hom ≫ T.toBase ≫ s = Ψ.algebraicRealizationStructureMap := by
      rw [← Category.assoc, he, h.toFanHom.algebraicMap_comp_algebraicRealizationStructureMap]
    apply (D.isNodeOfReducedBoundary_comap_iff_of_isOpenImmersion (T.toBase ≫ s) e.hom _).mp
    rw [← isNodeOfReducedBoundary_radical, hD, hs]
    exact Ψ.isNodeOfReducedBoundary_distinguishedPointHom hΨ σ hN hc
  exact hT.snoc (p x) hp p.ker_eq_ker_fromSpecResidueField (by
    simpa only [Category.comp_id, p, Scheme.Hom.comp_apply] using hn)

/-- The toric projection of a subdivision of regular surface fans is an ordered tower
of blowups of boundary nodes. The isomorphism to the tower identifies the final
reduced boundary. Each exceptional class is pulled back from the new ray divisor
of a star subdivision between the base and final fans. -/
theorem IsSubdivision.exists_toric_subdivision_blowup_tower
    (h : Ψ.IsSubdivision Φ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (hΦ₀ : Nonempty Φ.cones) (hN : Module.finrank ℤ N = 2) :
    ∃ (n : ℕ) (Y : Scheme) (T : QPainleve.BlowupTower Φ.algebraicRealization n Y)
      (e : Ψ.algebraicRealization ≅ Y),
      IsNodalBoundaryTower (Φ.boundaryIdeal hΦ₀) Φ.algebraicRealizationStructureMap
        (𝟙 _) T ∧
      e.hom ≫ T.toBase = h.toFanHom.algebraicMap ∧
      ((Φ.boundaryIdeal hΦ₀).comap T.toBase).radical.comap e.hom =
        Ψ.boundaryIdeal (h.nonempty_cones_of_nonempty hΦ₀) ∧
      ∀ j : Fin n, ∃ (Δ : Fan i) (hΔ : Δ.IsRegular) (σ : Δ.cones) (h₀ : σ.val ≠ ⊥),
        let Ω := Δ.starSubdivisionAlong hΔ σ.property
        let hΩ := Δ.isRegular_starSubdivisionAlong hΔ σ.property
        let ρ := Δ.starSubdivisionAlongRay hΔ σ.property h₀
        ∃ (_ : Δ.IsSubdivision Φ) (hstep : Ψ.IsSubdivision Ω),
          Nat.card (ToricRay σ.val) = 2 ∧
          LineBundleClass.pullback e.hom (T.exceptionalClass j) =
            LineBundleClass.pullback hstep.toFanHom.algebraicMap
              (LineBundleClass.mk
                (Ω.isEffectiveCartier_rayBoundaryIdeal hΩ ρ).toInvertibleSheaf)⁻¹ := by
  have hchain := h.exists_starSubdivision_factorization hΦ hΨ hN
  clear hΦ hΨ
  revert h
  induction hchain with
  | refl =>
    intro h
    have he : (Iso.refl Φ.algebraicRealization).hom ≫ (nil (X := Φ.algebraicRealization)).toBase =
        h.toFanHom.algebraicMap := by simp
    exact ⟨0, _, .nil, Iso.refl _, .nil, he,
      h.radical_comap_boundaryIdeal_of_iso _ hΦ₀ _ _ he, fun j ↦ j.elim0⟩
  | @tail Δ Ψ hpre hstep ih =>
    intro h
    have hΔΦ := isSubdivision_of_starSubdivision_chain hpre
    obtain ⟨hΔ, σ, hc⟩ := hstep
    obtain ⟨n, Y, T, e, hT, he, -, hclasses⟩ := ih hΔΦ
    obtain ⟨h₀, d, _, hd, _⟩ := exists_iso_blowup_starSubdivisionAlong hΔ σ hN hc
    let s := Δ.distinguishedPointHom σ
    let p := s ≫ e.hom
    let J := p.ker
    let F := Δ.starSubdivisionAlong_isSubdivision hΔ σ.property h₀
    have hJ : J.comap e.hom = s.ker := s.comap_ker_comp_of_isClosedImmersion e.hom
    let g := d ≪≫ blowupIso e hJ.symm
    have hg : g.hom ≫ J.blowupToBase = F.toFanHom.algebraicMap ≫ e.hom := by
      rw [Iso.trans_hom, Category.assoc, blowupIso_hom_blowupToBase, ← Category.assoc, hd]
    have hbase : g.hom ≫ (T.snoc J).toBase = h.toFanHom.algebraicMap := by
      rw [toBase_snoc, ← Category.assoc, hg, Category.assoc, he,
        ← FanHom.algebraicMap_comp, ← IsSubdivision.toFanHom_trans F hΔΦ]
    have hnodal := hΔΦ.isNodalBoundaryTower_snoc hΦ₀ hΔ σ hN hc e he hT
    refine ⟨n + 1, _, T.snoc J, g, hnodal, hbase,
      h.radical_comap_boundaryIdeal_of_iso _ hΦ₀ _ g hbase, ?_⟩
    intro j
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · refine ⟨Δ, hΔ, σ, h₀, hΔΦ, IsSubdivision.refl _, hc, ?_⟩
      rw [exceptionalClass_snoc_last, ← blowupExceptionalClass_def, Iso.trans_hom,
        ← LineBundleClass.pullback_comp, J.pullback_blowupExceptionalClass e hJ,
        IsSubdivision.toFanHom_refl, FanHom.algebraicMap_id, LineBundleClass.pullback_id]
      exact pullback_blowupExceptionalClass_starSubdivisionAlong hΔ σ h₀ hN hc d hd
    · obtain ⟨Γ, hΓ, τ, hτ, hΓΦ, hΔΩ, htwo, hclass⟩ := hclasses j
      refine ⟨Γ, hΓ, τ, hτ, hΓΦ, F.trans hΔΩ, htwo, ?_⟩
      rw [exceptionalClass_snoc_castSucc, LineBundleClass.pullback_comp, hg,
        ← LineBundleClass.pullback_comp, hclass, LineBundleClass.pullback_comp,
        IsSubdivision.toFanHom_trans F hΔΩ, FanHom.algebraicMap_comp]

/-- The morphism induced by a subdivision of nonempty regular surface fans
is proper and birational, since it factors into blowups of boundary nodes. -/
theorem IsSubdivision.isModification_algebraicMap (h : Ψ.IsSubdivision Φ)
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hΦ₀ : Nonempty Φ.cones)
    (hN : Module.finrank ℤ N = 2) : IsModification h.toFanHom.algebraicMap := by
  let : Nonempty Φ.cones := hΦ₀
  obtain ⟨_, _, T, e, hT, he, -, -⟩ :=
    h.exists_toric_subdivision_blowup_tower hΦ hΨ hΦ₀ hN
  let s := Φ.algebraicRealizationStructureMap
  let : SmoothOfRelativeDimension 2 s :=
    hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  have : IsModification T.toBase :=
    hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two s
  rw [← he]
  infer_instance

end TauCeti.Toric.Fan

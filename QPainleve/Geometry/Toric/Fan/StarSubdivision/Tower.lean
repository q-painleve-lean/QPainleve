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
import QPainleve.Geometry.Toric.BaseChange.FiniteType
import QPainleve.Geometry.Toric.BaseChange.Point
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

universe u

variable (k : Type u) [Field k] {N V : Type u}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i}

private theorem IsSubdivision.isNodalBoundaryTower_snoc (h : Ψ.IsSubdivision Φ)
    (hΦ : Nonempty Φ.cones) (hΨ : Ψ.IsRegular) (σ : Ψ.cones)
    (hN : Module.finrank ℤ N = 2) (hc : Nat.card (ToricRay σ.val) = 2)
    {n : ℕ} {Y : Scheme} {T : QPainleve.BlowupTower (Φ.finiteFanScheme k) n Y}
    (e : (Ψ.finiteFanScheme k) ≅ Y) (he : e.hom ≫ T.toBase = h.toFanHom.finiteFanSchemeHom k)
    (hT : IsNodalBoundaryTower (Φ.toricBoundaryIdeal k hΦ) (Φ.finiteFanSchemeToSpec k) (𝟙 _) T) :
    IsNodalBoundaryTower (Φ.toricBoundaryIdeal k hΦ) (Φ.finiteFanSchemeToSpec k) (𝟙 _)
      (T.snoc ((Ψ.distinguishedSection (R := k) σ ≫ e.hom).ker)) := by
  let D := (Φ.toricBoundaryIdeal k hΦ).comap T.toBase
  let s := (Φ.finiteFanSchemeToSpec k)
  let q := Ψ.distinguishedSection (R := k) σ
  let p := q ≫ e.hom
  let x : Spec (.of k) := IsLocalRing.closedPoint k
  have : IsClosedImmersion q := Ψ.isClosedImmersion_distinguishedSection (R := k) σ
  have : IsClosedImmersion p := inferInstanceAs (IsClosedImmersion (q ≫ e.hom))
  have hp : IsClosed ({p x} : Set Y) :=
    (Set.range_eq_singleton (f := p) (fun y ↦ congrArg p (Subsingleton.elim y x))) ▸
      p.isClosedEmbedding.isClosed_range
  have hn : D.IsNodeOfReducedBoundary (T.toBase ≫ s) (e.hom (q x)) := by
    have hD : (D.comap e.hom).radical = Ψ.toricBoundaryIdeal k ⟨σ⟩ := by
      change (((Φ.toricBoundaryIdeal k hΦ).comap T.toBase).comap e.hom).radical = _
      rw [← comap_comp, he]
      exact h.radical_comap_toricBoundaryIdeal k ⟨σ⟩ hΦ
    have hs : e.hom ≫ T.toBase ≫ s = (Ψ.finiteFanSchemeToSpec k) := by
      rw [← Category.assoc, he, h.toFanHom.finiteFanSchemeHom_comp_finiteFanSchemeToSpec k]
    apply (D.isNodeOfReducedBoundary_comap_iff_of_isOpenImmersion (T.toBase ≫ s) e.hom _).mp
    rw [← isNodeOfReducedBoundary_radical, hD, hs]
    exact Ψ.isNodeOfReducedBoundary_distinguishedSection k hΨ σ hN hc
  exact hT.snoc (p x) hp p.ker_eq_ker_fromSpecResidueField (by
    simpa only [Category.comp_id, p, Scheme.Hom.comp_apply] using hn)

/-- The toric projection of a subdivision of regular surface fans is an ordered tower
of blowups of boundary nodes. The isomorphism to the tower identifies the final
reduced boundary. Each exceptional class is pulled back from the new ray divisor
of a star subdivision between the base and final fans. -/
theorem IsSubdivision.exists_toric_subdivision_blowup_tower
    (h : Ψ.IsSubdivision Φ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (hΦ₀ : Nonempty Φ.cones) (hN : Module.finrank ℤ N = 2) :
    ∃ (n : ℕ) (Y : Scheme) (T : QPainleve.BlowupTower (Φ.finiteFanScheme k) n Y)
      (e : (Ψ.finiteFanScheme k) ≅ Y),
      IsNodalBoundaryTower (Φ.toricBoundaryIdeal k hΦ₀) (Φ.finiteFanSchemeToSpec k)
        (𝟙 _) T ∧
      e.hom ≫ T.toBase = h.toFanHom.finiteFanSchemeHom k ∧
      ((Φ.toricBoundaryIdeal k hΦ₀).comap T.toBase).radical.comap e.hom =
        Ψ.toricBoundaryIdeal k (h.nonempty_cones_of_nonempty hΦ₀) ∧
      ∀ j : Fin n, ∃ (Δ : Fan i) (hΔ : Δ.IsRegular) (σ : Δ.cones) (h₀ : σ.val ≠ ⊥),
        let Ω := Δ.starSubdivisionAlong hΔ σ.property
        let hΩ := Δ.isRegular_starSubdivisionAlong hΔ σ.property
        let ρ := Δ.starSubdivisionAlongRay hΔ σ.property h₀
        ∃ (_ : Δ.IsSubdivision Φ) (hstep : Ψ.IsSubdivision Ω),
          Nat.card (ToricRay σ.val) = 2 ∧
          LineBundleClass.pullback e.hom (T.exceptionalClass j) =
            LineBundleClass.pullback (hstep.toFanHom.finiteFanSchemeHom k)
              (LineBundleClass.mk
                (Ω.isEffectiveCartier_rayDivisorIdeal k hΩ ρ).toInvertibleSheaf)⁻¹ := by
  have hchain := h.exists_starSubdivision_factorization hΦ hΨ hN
  clear hΦ hΨ
  revert h
  induction hchain with
  | refl =>
    intro h
    have he : (Iso.refl (Φ.finiteFanScheme k)).hom ≫ (nil (X := (Φ.finiteFanScheme k))).toBase =
        h.toFanHom.finiteFanSchemeHom k := by simp
    refine ⟨0, _, .nil, Iso.refl _, .nil, he, ?_, fun j ↦ j.elim0⟩
    rw [← radical_comap_of_isOpenImmersion, ← comap_comp, he]
    exact h.radical_comap_toricBoundaryIdeal k _ hΦ₀
  | @tail Δ Ψ hpre hstep ih =>
    intro h
    have hΔΦ := isSubdivision_of_starSubdivision_chain hpre
    obtain ⟨hΔ, σ, hc⟩ := hstep
    obtain ⟨n, Y, T, e, hT, he, -, hclasses⟩ := ih hΔΦ
    obtain ⟨h₀, d, _, hd, _⟩ := exists_iso_blowup_starSubdivisionAlong k hΔ σ hN hc
    let s := Δ.distinguishedSection (R := k) σ
    let p := s ≫ e.hom
    let J := p.ker
    let F := Δ.starSubdivisionAlong_isSubdivision hΔ σ.property h₀
    have hJ : J.comap e.hom = s.ker := s.comap_ker_comp_of_isClosedImmersion e.hom
    let g := d ≪≫ blowupIso e hJ.symm
    have hg : g.hom ≫ J.blowupToBase = F.toFanHom.finiteFanSchemeHom k ≫ e.hom := by
      rw [Iso.trans_hom, Category.assoc, blowupIso_hom_blowupToBase, ← Category.assoc, hd]
    have hbase : g.hom ≫ (T.snoc J).toBase = h.toFanHom.finiteFanSchemeHom k := by
      rw [toBase_snoc, ← Category.assoc, hg, Category.assoc, he,
        ← FanHom.finiteFanSchemeHom_comp, ← IsSubdivision.toFanHom_trans F hΔΦ]
    have hnodal := hΔΦ.isNodalBoundaryTower_snoc k hΦ₀ hΔ σ hN hc e he hT
    refine ⟨n + 1, _, T.snoc J, g, hnodal, hbase, ?_, ?_⟩
    · rw [← radical_comap_of_isOpenImmersion, ← comap_comp, hbase]
      exact h.radical_comap_toricBoundaryIdeal k _ hΦ₀
    · intro j
      refine Fin.lastCases ?_ (fun j ↦ ?_) j
      · refine ⟨Δ, hΔ, σ, h₀, hΔΦ, IsSubdivision.refl _, hc, ?_⟩
        rw [exceptionalClass_snoc_last, ← blowupExceptionalClass_def, Iso.trans_hom,
          ← LineBundleClass.pullback_comp, J.pullback_blowupExceptionalClass e hJ,
          IsSubdivision.toFanHom_refl, FanHom.finiteFanSchemeHom_id, LineBundleClass.pullback_id]
        exact pullback_blowupExceptionalClass_starSubdivisionAlong k hΔ σ h₀ hN hc d hd
      · obtain ⟨Γ, hΓ, τ, hτ, hΓΦ, hΔΩ, htwo, hclass⟩ := hclasses j
        refine ⟨Γ, hΓ, τ, hτ, hΓΦ, F.trans hΔΩ, htwo, ?_⟩
        rw [exceptionalClass_snoc_castSucc, LineBundleClass.pullback_comp, hg,
          ← LineBundleClass.pullback_comp, hclass, LineBundleClass.pullback_comp,
          IsSubdivision.toFanHom_trans F hΔΩ, FanHom.finiteFanSchemeHom_comp]

/-- The morphism induced by a subdivision of nonempty regular surface fans
is proper and birational, since it factors into blowups of boundary nodes. -/
theorem IsSubdivision.isModification_finiteFanSchemeHom (h : Ψ.IsSubdivision Φ)
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hΦ₀ : Nonempty Φ.cones)
    (hN : Module.finrank ℤ N = 2) : IsModification (h.toFanHom.finiteFanSchemeHom k) := by
  let : Nonempty Φ.cones := hΦ₀
  obtain ⟨_, _, T, e, hT, he, -, -⟩ :=
    h.exists_toric_subdivision_blowup_tower k hΦ hΨ hΦ₀ hN
  let s := (Φ.finiteFanSchemeToSpec k)
  let : SmoothOfRelativeDimension 2 s :=
    hN ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec (R := k) hΦ
  have : IsModification T.toBase :=
    hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two s
  rw [← he]
  infer_instance

end TauCeti.Toric.Fan

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Boundary
public import QPainleve.Geometry.Toric.Fan.Subdivision

import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision

/-!
# Toric subdivisions from specified nodal blowup towers

Each center in a nodal blowup tower over a complete regular toric surface determines
the two-dimensional cone to subdivide at that step. The resulting toric projection
agrees with the projection of the specified tower, and the comparison identifies its
reduced boundary and ordered total exceptional classes. This is the toric part of the
normalization of logarithmic morphisms used in Lutz's appendix to Hacking and Keating,
[*Homological mirror symmetry for log Calabi–Yau surfaces*][HKL], Theorem 8.4.

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i}

local notation "X[" Δ "]" => algebraicRealization Δ
local notation "s[" Δ "]" => algebraicRealizationStructureMap Δ
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

/-- Realize a specified nodal tower over a complete regular toric surface by a
subdivision of its fan. The isomorphism to the tower commutes with the original
projection and identifies the reduced boundary. Each exceptional marking is the
total pullback of the new ray divisor at the corresponding star subdivision. -/
theorem exists_toric_subdivision_of_nodal_boundary_tower
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (hN : Module.finrank ℤ N = 2)
    {n : ℕ} {Y : Scheme} {T : QPainleve.BlowupTower X[Φ] n Y}
    (hT : IsNodalBoundaryTower (Φ.boundaryIdeal hc.nonempty_cones) s[Φ] (𝟙 _) T) :
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (h : Ψ.IsSubdivision Φ) (e : X[Ψ] ≅ Y),
      e.hom ≫ T.toBase = h.toFanHom.algebraicMap ∧
      (((Φ.boundaryIdeal hc.nonempty_cones).comap T.toBase).radical).comap e.hom =
        Ψ.boundaryIdeal (h.nonempty_cones_of_nonempty hc.nonempty_cones) ∧
      ∀ j : Fin n, ∃ (Δ : Fan i) (hΔ : Δ.IsRegular) (σ : Δ.cones)
        (hσ : Nat.card (ToricRay σ.val) = 2),
        let Ω := Δ.starSubdivisionAlong hΔ σ.property
        let hΩ := Δ.isRegular_starSubdivisionAlong hΔ σ.property
        let ρ := Δ.starSubdivisionAlongRay hΔ σ.property (ne_bot_of_card_toricRay_eq_two hσ)
        ∃ (_ : Δ.IsSubdivision Φ) (hstep : Ψ.IsSubdivision Ω),
          LineBundleClass.pullback e.hom (T.exceptionalClass j) =
            LineBundleClass.pullback hstep.toFanHom.algebraicMap
              classOf(Ω.isEffectiveCartier_rayBoundaryIdeal hΩ ρ) := by
  induction hT with
  | nil =>
    let h := IsSubdivision.refl Φ
    have he : (Iso.refl X[Φ]).hom ≫ (nil (X := X[Φ])).toBase = h.toFanHom.algebraicMap := by
      simp
    exact ⟨Φ, hΦ, h, Iso.refl _, he,
      h.radical_comap_boundaryIdeal_of_iso _ _ _ _ he, fun j ↦ j.elim0⟩
  | @snoc n Y T I hT p hp hI hnode ih =>
    obtain ⟨Δ, hΔ, H, e, he, -, hclasses⟩ := ih
    have hnode' : ((Φ.boundaryIdeal hc.nonempty_cones).comap T.toBase).IsNodeOfReducedBoundary
        (T.toBase ≫ s[Φ]) p := by
      simpa only [Category.comp_id] using hnode
    obtain ⟨σ, hσ, -, g, hg, hlast⟩ :=
      H.exists_iso_starSubdivision_of_isNodeOfReducedBoundary hc hΔ hN T.toBase e he hI hnode'
    let Ω := Δ.starSubdivisionAlong hΔ σ.property
    let F := Δ.starSubdivisionAlong_isSubdivision hΔ σ.property (ne_bot_of_card_toricRay_eq_two hσ)
    let h := F.trans H
    have hbase : g.hom ≫ (T.snoc I).toBase = h.toFanHom.algebraicMap := by
      rw [toBase_snoc, ← Category.assoc, hg, Category.assoc, he,
        ← FanHom.algebraicMap_comp, ← IsSubdivision.toFanHom_trans F H]
    refine ⟨Ω, Δ.isRegular_starSubdivisionAlong hΔ σ.property, h, g, hbase,
      h.radical_comap_boundaryIdeal_of_iso _ _ _ _ hbase, ?_⟩
    intro j
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · refine ⟨Δ, hΔ, σ, hσ, H, IsSubdivision.refl _, ?_⟩
      rw [exceptionalClass_snoc_last, ← blowupExceptionalClass_def, IsSubdivision.toFanHom_refl,
        FanHom.algebraicMap_id, LineBundleClass.pullback_id]
      exact hlast
    · obtain ⟨Γ, hΓ, τ, hτ, hΓΦ, hΔΩ, hclass⟩ := hclasses j
      refine ⟨Γ, hΓ, τ, hτ, hΓΦ, F.trans hΔΩ, ?_⟩
      rw [exceptionalClass_snoc_castSucc, LineBundleClass.pullback_comp, hg,
        ← LineBundleClass.pullback_comp, hclass, LineBundleClass.pullback_comp,
        IsSubdivision.toFanHom_trans F hΔΩ, FanHom.algebraicMap_comp]

end TauCeti.Toric.Fan

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Boundary
public import QPainleve.Geometry.Toric.Fan.Subdivision

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import QPainleve.Geometry.Toric.Fan.Boundary.Node
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

/-- A closed node of the reduced boundary on a model of a subdivision determines a
two-ray cone on that subdivision. Blowing up the actual center ideal is the star
subdivision at this cone, with the new ray class equal to the exceptional class. -/
theorem IsSubdivision.exists_iso_starSubdivision_of_isNodeOfReducedBoundary
    (h : Ψ.IsSubdivision Φ) (hc : Φ.IsComplete)
    (hΨ : Ψ.IsRegular) (hN : Module.finrank ℤ N = 2) {Y : Scheme}
    (f : Y ⟶ X[Φ]) (e : X[Ψ] ≅ Y) (he : e.hom ≫ f = h.toFanHom.algebraicMap)
    {p : Y} {I : Y.IdealSheafData} (hI : I = (Y.fromSpecResidueField p).ker)
    (hp : ((Φ.boundaryIdeal hc.nonempty_cones).comap f).IsNodeOfReducedBoundary (f ≫ s[Φ]) p) :
    ∃ (σ : Ψ.cones) (hσ : Nat.card (ToricRay σ.val) = 2),
      let Ω := Ψ.starSubdivisionAlong hΨ σ.property
      let hΩ := Ψ.isRegular_starSubdivisionAlong hΨ σ.property
      let h₀ := ne_bot_of_card_toricRay_eq_two hσ
      let F := Ψ.starSubdivisionAlong_isSubdivision hΨ σ.property h₀
      let ρ := Ψ.starSubdivisionAlongRay hΨ σ.property h₀
      I.comap e.hom = (Ψ.distinguishedPointHom σ).ker ∧
      ∃ g : X[Ω] ≅ I.blowup,
        g.hom ≫ I.blowupToBase = F.toFanHom.algebraicMap ≫ e.hom ∧
        LineBundleClass.pullback g.hom I.blowupExceptionalClass =
          classOf(Ω.isEffectiveCartier_rayBoundaryIdeal hΩ ρ) := by
  let D := (Φ.boundaryIdeal hc.nonempty_cones).comap f
  let x := e.inv p
  have hx : e.hom x = p := by simp [x, ← Scheme.Hom.comp_apply]
  have hs : e.hom ≫ f ≫ s[Φ] = s[Ψ] := by
    rw [← Category.assoc, he, h.toFanHom.algebraicMap_comp_algebraicRealizationStructureMap]
  let : Nonempty Ψ.cones := h.nonempty_cones_of_nonempty hc.nonempty_cones
  have hrad : (D.comap e.hom).radical = Ψ.boundaryIdeal inferInstance := by
    rw [radical_comap_of_isOpenImmersion]
    exact h.radical_comap_boundaryIdeal_of_iso _ hc.nonempty_cones f e he
  have hnode : (Ψ.boundaryIdeal inferInstance).IsNodeOfReducedBoundary s[Ψ] x := by
    have hp' : D.IsNodeOfReducedBoundary (f ≫ s[Φ]) (e.hom x) := by simpa only [hx] using hp
    have hn := (D.isNodeOfReducedBoundary_comap_iff_of_isOpenImmersion (f ≫ s[Φ]) e.hom x).mpr
      hp'
    rwa [← isNodeOfReducedBoundary_radical (D.comap e.hom), hrad, hs] at hn
  obtain ⟨σ, ⟨hσ, hpoint⟩, -⟩ :=
    (Ψ.isNodeOfReducedBoundary_iff_existsUnique_twoRayCone hΨ (h.isComplete_iff.mpr hc) hN).mp hnode
  let q := Ψ.distinguishedPointHom σ
  have hcenter : I.comap e.hom = q.ker := by
    rw [hI, ← hx, e.hom.comap_ker_fromSpecResidueField_apply,
      q.ker_eq_ker_fromSpecResidueField, hpoint]
  obtain ⟨_, d, _, hd, _⟩ := exists_iso_blowup_starSubdivisionAlong hΨ σ hN hσ
  let g := d ≪≫ I.blowupIso e hcenter
  refine ⟨σ, hσ, hcenter, g, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, blowupIso_hom_blowupToBase, ← Category.assoc, hd]
  · rw [Iso.trans_hom, ← LineBundleClass.pullback_comp,
      I.pullback_blowupExceptionalClass e hcenter]
    exact pullback_blowupExceptionalClass_starSubdivisionAlong hΨ σ _ hN hσ d hd

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

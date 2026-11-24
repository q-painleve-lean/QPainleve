/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
public import QPainleve.Geometry.Toric.Fan.Boundary.NodalPullback
public import QPainleve.Geometry.Toric.Fan.Subdivision.InternalBlowup

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Tower
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Common nodal refinements of internal toric blowup models

Two regular surface fans with the same support and matching ordered binomial centers
can be compared on a common internal model. Both projections are nodal blowup towers
up to isomorphism, and their reduced total boundaries are identified with the strict
boundary of the internal model over the subdividing fan.

For toric models with infinitely near centers and blowups of boundary nodes, see
[Gross, Hacking and Keel, Definition 1.2 and the paragraph following it][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S1
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve QPainleve.BlowupTower
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i}
  [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones]
  (b : Module.Basis (Fin 2) ℤ N) {n : ℕ}

local notation "model" => internalBlowupTower b

/-- A regular subdivision induces a nodal blowup projection of the ordered internal
model. Its reduced total boundary is the strict boundary of the refined internal model,
and the square of projections to the fan schemes is cartesian. -/
theorem IsSubdivision.exists_nodal_refinement_internalBlowupTower
    (h : Φ.IsSubdivision Ψ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (ρ : Fin n → Ψ.Ray) (c : Fin n → ℂˣ) :
    let A := model (h.liftRay ∘ ρ) c
    let B := model ρ c
    ∃ (m : ℕ) (Z : Scheme) (T : BlowupTower B.1 m Z) (e : A.1 ≅ Z),
      IsNodalBoundaryTower B.2.boundaryι.ker
        (B.2.toTower.toBase ≫ Ψ.algebraicRealizationStructureMap) (𝟙 B.1) T ∧
      IsPullback (e.hom ≫ T.toBase) A.2.toTower.toBase
        B.2.toTower.toBase h.toFanHom.algebraicMap ∧
      ((B.2.boundaryι.ker.comap T.toBase).radical).comap e.hom = A.2.boundaryι.ker := by
  dsimp only
  let A := model (h.liftRay ∘ ρ) c
  let B := model ρ c
  have hrank := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  obtain ⟨m, Y, R, a, hR, ha, -, -⟩ :=
    h.exists_toric_subdivision_blowup_tower hΨ hΦ hΨ₀ hrank
  obtain ⟨Z, T, g, hT, hg⟩ :=
    Ψ.exists_isPullback_nodalBoundaryTower_internalBlowupTower hR b ρ c
  obtain ⟨g', hg', hb, -⟩ := h.exists_isPullback_internalBlowupTower b ρ c
  have hpb : IsPullback T.toBase (g ≫ a.inv) B.2.toTower.toBase
      h.toFanHom.algebraicMap := by
    refine hg.flip.of_iso' (Iso.refl _) (Iso.refl _) a (Iso.refl _)
      (by simp) (by simp) (by simp [B]) (by simpa using ha)
  let e := hg'.isoIsPullback _ _ hpb
  have he : e.hom ≫ T.toBase = g' := hg'.isoIsPullback_hom_fst _ _ hpb
  refine ⟨m, Z, T, e, hT, he.symm ▸ hg', ?_⟩
  have hred : IsReduced (Φ.boundaryIdeal hΦ₀).subscheme := by
    rw [Fan.boundaryIdeal_def]
    infer_instance
  have hbase :
      (((B.2.boundaryι ≫ B.2.toTower.toBase).ker).comap h.toFanHom.algebraicMap).radical =
        (A.2.boundaryι ≫ A.2.toTower.toBase).ker := by
    simpa only [WithBoundary.boundaryι_toBase, ker_subschemeι] using
      h.radical_comap_boundaryIdeal hΦ₀ hΨ₀
  have : IsClosedImmersion (B.2.boundaryι ≫ B.2.toTower.toBase) := by
    rw [WithBoundary.boundaryι_toBase]
    infer_instance
  have : IsClosedImmersion (A.2.boundaryι ≫ A.2.toTower.toBase) := by
    rw [WithBoundary.boundaryι_toBase]
    infer_instance
  have hcart : IsPullback g' A.2.toTower.toBase B.2.toTower.toBase
      h.toFanHom.algebraicMap := hg'
  have hboundary := radical_comap_ker_eq_of_isPullback hcart B.2.boundaryι A.2.boundaryι
    (h.boundaryMap hΦ₀ hΨ₀) hb hbase
  rw [← radical_comap_of_isOpenImmersion, ← comap_comp, he]
  exact hboundary

/-- For matching labelled generators and center parameters, the ordered model on a
specified common regular subdivision projects to both original internal models by
nodal blowup towers. Each projection is cartesian over the corresponding fan
subdivision and identifies the reduced total boundary with the strict boundary. -/
theorem exists_common_nodal_refinement_internalBlowupTower
    {Ω : Fan i} [hΩ₀ : Nonempty Ω.cones]
    (hΩΦ : Ω.IsSubdivision Φ) (hΩΨ : Ω.IsSubdivision Ψ)
    (hΩ : Ω.IsRegular) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (ρ : Fin n → Φ.Ray) (τ : Fin n → Ψ.Ray) (c : Fin n → ℂˣ)
    (hρτ : ∀ j, (ρ j).primitiveGenerator = (τ j).primitiveGenerator) :
    let B := model ρ c
    let C := model τ c
    let A := internalBlowupTower (h₀ := hΩ₀) b (hΩΦ.liftRay ∘ ρ) c
    ∃ (m l : ℕ) (Y Z : Scheme) (T : BlowupTower B.1 m Y) (U : BlowupTower C.1 l Z)
      (e : A.1 ≅ Y) (f : A.1 ≅ Z),
      IsNodalBoundaryTower B.2.boundaryι.ker
        (B.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap) (𝟙 B.1) T ∧
      IsNodalBoundaryTower C.2.boundaryι.ker
        (C.2.toTower.toBase ≫ Ψ.algebraicRealizationStructureMap) (𝟙 C.1) U ∧
      IsPullback (e.hom ≫ T.toBase) A.2.toTower.toBase
        B.2.toTower.toBase hΩΦ.toFanHom.algebraicMap ∧
      IsPullback (f.hom ≫ U.toBase) A.2.toTower.toBase
        C.2.toTower.toBase hΩΨ.toFanHom.algebraicMap ∧
      ((B.2.boundaryι.ker.comap T.toBase).radical).comap e.hom = A.2.boundaryι.ker ∧
      ((C.2.boundaryι.ker.comap U.toBase).radical).comap f.hom = A.2.boundaryι.ker := by
  dsimp only
  have hmatch := hΩΦ.liftRay_comp_eq_of_primitiveGenerator_eq hΩΨ ρ τ hρτ
  obtain ⟨m, Y, T, e, hT, he, hD⟩ :=
    hΩΦ.exists_nodal_refinement_internalBlowupTower b hΩ hΦ ρ c
  have hright := hΩΨ.exists_nodal_refinement_internalBlowupTower b hΩ hΨ τ c
  dsimp only at hright
  rw [← hmatch] at hright
  obtain ⟨l, Z, U, f, hU, hf, hE⟩ := hright
  exact ⟨m, l, Y, Z, T, U, e, f, hT, hU, he, hf, hD, hE⟩

end TauCeti.Toric.Fan

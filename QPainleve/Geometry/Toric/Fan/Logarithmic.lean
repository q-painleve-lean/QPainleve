/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Logarithmic.Factorization
public import QPainleve.Geometry.Toric.Fan.InternalBlowup
public import QPainleve.Geometry.Toric.Fan.Subdivision

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.Boundary.SmoothPoint
import QPainleve.Geometry.Toric.Fan.StarSubdivision.NodalTower
import TauCeti.AlgebraicGeometry.Morphisms.StalkMap

/-!
# Toric factorization of logarithmic blowup towers

A specified logarithmic point blowup tower over a complete regular toric surface
is an ordered internal blowup tower over a subdivision. Its projection to the original
surface and its final boundary come from this toric model, and the original ordered
center schemes retain their maps to the base.

The factorization into corner and internal operations follows Lutz's appendix to
Hacking and Keating, [*Homological mirror symmetry for log Calabi–Yau surfaces*][HKL],
Definition 8.1 and Theorem 8.4.

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} {S Y : Scheme} {n m : ℕ}

local notation "X[" Δ "]" => algebraicRealization Δ
local notation "s[" Δ "]" => algebraicRealizationStructureMap Δ

private theorem exists_coordinates_of_orderedFactorization (b : Module.Basis (Fin 2) ℤ N)
    (hΨ : Ψ.IsRegular) (hc : Ψ.IsComplete)
    {X : Scheme} {D : X.IdealSheafData} {s : X ⟶ Spec (.of ℂ)}
    {T : BlowupTower X n Y} {P : Y.IdealSheafData} {c : Fin m → Over X}
    (h : IsLogarithmicBoundaryTower D s T P c)
    (F : IsLogarithmicBoundaryTower.OrderedFactorization D s T P c)
    (d : (Ψ.boundaryIdeal hc.nonempty_cones).subscheme ≅ F.boundary.subscheme)
    (hd : d.hom ≫ F.boundary.subschemeι ≫ F.tower.toBase ≫ s =
      (Ψ.boundaryIdeal hc.nonempty_cones).subschemeι ≫ s[Ψ]) :
    let := hc.nonempty_cones
    ∃ (ρ : Fin m → Ψ.Ray) (u : Fin m → ℂˣ),
      ∀ j, ((ρ j).internalCenter b (u j)).val = (F.center j ≫ d.inv).ker := by
  let := hc.nonempty_cones
  let a (j : Fin m) := F.center j ≫ d.inv
  have H (j : Fin m) : ∃ (ρ : Ψ.Ray) (u : ℂˣ), (ρ.internalCenter b u).val = (a j).ker := by
    obtain ⟨hred, ⟨y⟩, hsingle⟩ := h.center_is_reduced_point j
    have := F.isClosedImmersion_center j
    have : IsClosedImmersion (a j) := inferInstanceAs (IsClosedImmersion (F.center j ≫ d.inv))
    have : Nonempty (c j).left := ⟨y⟩
    let p := a j y
    have hy : d.hom p = F.center j y := by
      have he := congrArg (fun f : (c j).left ⟶ F.boundary.subscheme ↦ f y)
        (by simp [a] : a j ≫ d.hom = F.center j)
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans he
    have hs : (((Ψ.boundaryIdeal hc.nonempty_cones).subschemeι ≫ s[Ψ]).stalkMap
        p).hom.FormallySmooth := by
      rw [← hd]
      exact (RingHom.FormallySmooth.respectsIso.stalkMap_comp_isOpenImmersion_iff _ _ _).mpr
        (hy.symm ▸ F.formallySmooth_stalkMap_center j y)
    have hrange : Set.range (a j) = {p} :=
      Set.range_eq_singleton fun x ↦ congrArg (a j) (hsingle.elim x y)
    have hp : IsClosed ({p} : Set _) := hrange ▸ (a j).isClosedEmbedding.isClosed_range
    obtain ⟨ρ, u, hu⟩ :=
      Ψ.exists_internalCenter_eq_ker_fromSpecResidueField b hΨ hc p hp hs
    refine ⟨ρ, u, hu.trans ?_⟩
    rw [(a j).ker_eq_vanishingIdeal_support, Scheme.ker_fromSpecResidueField_eq_vanishingIdeal]
    apply congrArg vanishingIdeal
    apply SetLike.coe_injective
    rw [(a j).support_ker, hrange]
    rfl
  choose ρ u hu using H
  exact ⟨ρ, u, hu⟩

/-- A logarithmic point blowup tower over a complete regular toric surface factors as
the ordered internal blowups of a regular toric subdivision. The comparison is over the
specified projection and identifies the strict boundary. Each original center scheme
maps into the subdivided boundary with its binomial ideal and its original map to the
base. Repeated centers keep their indices and so retain the infinitely near blowups. -/
theorem exists_toric_internal_factorization (b : Module.Basis (Fin 2) ℤ N)
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) {T : BlowupTower X[Φ] n Y}
    {P : Y.IdealSheafData} {c : Fin m → Over X[Φ]}
    (h : IsLogarithmicBoundaryTower (Φ.boundaryIdeal hc.nonempty_cones) s[Φ] T P c) :
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (H : Ψ.IsSubdivision Φ),
      let := H.nonempty_cones_of_nonempty hc.nonempty_cones
      ∃ (ρ : Fin m → Ψ.Ray) (u : Fin m → ℂˣ),
        let A := Ψ.internalBlowupTower b ρ u
        ∃ (e : A.1 ≅ Y)
          (a : ∀ j, (c j).left ⟶ (Ψ.boundaryIdeal inferInstance).subscheme),
          e.hom ≫ T.toBase = A.2.toTower.toBase ≫ H.toFanHom.algebraicMap ∧
          P.comap e.hom = A.2.boundaryι.ker ∧
          (∀ j, IsClosedImmersion (a j)) ∧
          ∀ j, (a j).ker = ((ρ j).internalCenter b (u j)).val ∧
            a j ≫ (Ψ.boundaryIdeal inferInstance).subschemeι ≫ H.toFanHom.algebraicMap =
              (c j).hom := by
  have : IsReduced (Φ.boundaryIdeal hc.nonempty_cones).subscheme := by
    rw [Φ.boundaryIdeal_def]
    infer_instance
  obtain ⟨F⟩ := h.nonempty_orderedFactorization
  obtain ⟨Ψ, hΨ, H, g, hg, hB, -⟩ := Φ.exists_toric_subdivision_of_nodal_boundary_tower hΦ hc
    ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)) F.isNodal
  have hc' := H.isComplete_iff.mpr hc
  let := hc'.nonempty_cones
  let B := Ψ.boundaryIdeal hc'.nonempty_cones
  have hB' : F.boundary.comap g.hom = B := F.boundary_eq ▸ hB
  let fD := subschemeMap B F.boundary g.hom (le_map_iff_comap_le.mpr hB'.le)
  have hd : fD ≫ F.boundary.subschemeι = B.subschemeι ≫ g.hom :=
    subschemeMap_subschemeι _ _ _ _
  have hpb := isPullback_of_isClosedImmersion B.subschemeι F.boundary.subschemeι
    fD g.hom hd.symm (by simpa only [ker_subschemeι] using hB')
  have := hpb.isIso_snd_of_isIso
  let d := asIso fD
  have hdBase : d.hom ≫ F.boundary.subschemeι ≫ F.tower.toBase =
      B.subschemeι ≫ H.toFanHom.algebraicMap := by
    have hd' : d.hom ≫ F.boundary.subschemeι = B.subschemeι ≫ g.hom := hd
    rw [← Category.assoc, hd', Category.assoc, hg]
  let a (j : Fin m) := F.center j ≫ d.inv
  have ha (j : Fin m) : IsClosedImmersion (a j) := by
    have := F.isClosedImmersion_center j
    exact inferInstanceAs (IsClosedImmersion (F.center j ≫ d.inv))
  obtain ⟨ρ, u, hu⟩ := exists_coordinates_of_orderedFactorization b hΨ hc' h F d (by
    rw [reassoc_of% hdBase, FanHom.algebraicMap_comp_algebraicRealizationStructureMap])
  let Matches (L : Σ W, WithBoundary B.subschemeι m W) :=
    ∃ f : L.1 ≅ F.internalTower.1, IsLift g L.2.toTower F.internalTower.2.toTower f ∧
      L.2.boundaryι ≫ f.hom = d.hom ≫ F.internalTower.2.boundaryι
  have hlift : Matches (Ψ.internalBlowupTower b ρ u) := by
    rw [Ψ.internalBlowupTower_eq_alongBoundary]
    exact exists_isLift_alongBoundary g d hd.symm _ _ (by
      intro j
      rw [hu, ← Scheme.Hom.comap_ker_comp_of_isClosedImmersion (a j) d.hom]
      simp [a])
  obtain ⟨f, hf, hbound⟩ := hlift
  refine ⟨Ψ, hΨ, H, ρ, u, f ≪≫ F.iso, a, ?_, ?_, ha, fun j ↦ ⟨(hu j).symm, ?_⟩⟩
  · simp only [Iso.trans_hom, Category.assoc, F.iso_hom_toBase,
      ← Category.assoc f.hom, hf.hom_toBase, Category.assoc, hg]
  · rw [Iso.trans_hom, comap_comp, F.comap_boundary_iso_hom,
      ← Scheme.Hom.comap_ker_comp_of_isClosedImmersion
        (Ψ.internalBlowupTower b ρ u).2.boundaryι f.hom,
      hbound, Scheme.Hom.ker_comp_of_isIso]
  · rw [← hdBase]
    simpa only [a, Category.assoc, Iso.inv_hom_id_assoc] using F.center_toBase j

end TauCeti.Toric.Fan

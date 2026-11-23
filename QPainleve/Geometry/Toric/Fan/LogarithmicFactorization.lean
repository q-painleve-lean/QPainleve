/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Logarithmic.Factorization
public import QPainleve.Geometry.Toric.Fan.InternalBlowup
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.NodalTower

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.Geometry.Toric.Fan.Smooth

/-!
# Toric factorization of logarithmic blowup towers

The corner prefix of a logarithmic point tower over a complete regular toric surface
is a toric subdivision. The internal suffix is the native ordered blowup of
binomial centers on that subdivision. The comparison identifies the specified projection
and the strict boundary, and recovers the ordered center schemes over the original surface.
This is the toric normalization used in Lutz's appendix to Hacking and Keating,
[*Homological mirror symmetry for log Calabi–Yau surfaces*](https://arxiv.org/abs/2005.05010v3),
Theorem 8.4.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Δ "]" => algebraicRealization Δ
local notation "f[" Δ "]" => algebraicRealizationStructureMap Δ
local notation "rk(" b ")" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))

variable {n m : ℕ} {Y : Scheme} {T : QPainleve.BlowupTower X[Φ] n Y}
  {P : Y.IdealSheafData} {c : Fin m → Over X[Φ]} {D : X[Φ].IdealSheafData}
  (F : IsLogarithmicBoundaryTower.OrderedFactorization D f[Φ] T P c)

private theorem exists_binomial_center_of_orderedFactorization [hΨ₀ : Nonempty Ψ.cones]
    (b : Module.Basis (Fin 2) ℤ N) (hΨ : Ψ.IsRegular) (hc : Ψ.IsComplete)
    (d : (Ψ.boundaryIdeal hΨ₀).subscheme ≅ F.boundary.subscheme)
    (hd : d.hom ≫ F.boundary.subschemeι ≫ F.tower.toBase ≫ f[Φ] =
      (Ψ.boundaryIdeal hΨ₀).subschemeι ≫ f[Ψ])
    (j : Fin m) (a : S ≅ (c j).left) (ha : a.hom ≫ (c j).hom ≫ f[Φ] = 𝟙 _) :
    ∃ (ρ : Ψ.Ray) (z : ℂˣ),
      (ρ.binomialCenterOnBoundary rk(b) (b.detDualEquiv_self _)
        (ρ.surjective_detCharacter b) z) ≫ d.hom = a.hom ≫ F.center j := by
  let E := Ψ.boundaryIdeal hΨ₀
  let s := E.subschemeι ≫ f[Ψ]
  let t := F.boundary.subschemeι ≫ F.tower.toBase ≫ f[Φ]
  let p := a.hom ≫ F.center j ≫ d.inv
  have hpd : p ≫ d.hom = a.hom ≫ F.center j := by simp [p]
  have hp : p ≫ s = 𝟙 S := by
    dsimp only [s, E]
    rw [← hd, ← Category.assoc p d.hom, hpd, Category.assoc,
      reassoc_of% (F.center_toBase j), ha]
  let pt : S := IsLocalRing.closedPoint ℂ
  let x := p pt
  have hdx : d.hom x = F.center j (a.hom pt) := by
    simpa only [x, Scheme.Hom.comp_apply] using
      congrArg (fun g : S ⟶ F.boundary.subscheme ↦ g pt) hpd
  have hn : ¬ s.IsNodeAt x := by
    intro hn
    have h := (t.isNodeAt_comp_iff_of_isOpenImmersion d.hom x).mp (hd.symm ▸ hn)
    rw [hdx] at h
    exact h.not_formallySmooth_stalkMap
      (F.formallySmooth_stalkMap_center j (a.hom pt))
  have : IsReduced (Ψ.boundaryIdeal hΨ₀).subscheme := by
    rw [boundaryIdeal_def]
    infer_instance
  have hnot : ¬ E.IsNodeOfReducedBoundary f[Ψ] (E.subschemeι x) := by
    rw [E.isNodeOfReducedBoundary_iff_of_isReduced]
    rintro ⟨y, hy, h⟩
    exact hn (E.subschemeι.isClosedEmbedding.injective hy ▸ h)
  obtain ⟨ρ, hρ⟩ := Ψ.exists_rayChart_of_not_isNodeOfReducedBoundary hΨ hc rk(b) hnot
  obtain ⟨z, hz⟩ := ρ.exists_binomialCenterOnBoundary_eq_of_mem_rayChart rk(b)
    (b.detDualEquiv_self _) (ρ.surjective_detCharacter b) p hp hρ
  exact ⟨ρ, z, hz ▸ hpd⟩

/-- A specified logarithmic point blowup tower over a complete regular toric surface
factors as a native toric subdivision followed by ordered internal binomial blowups.
The projection and the final boundary agree as schemes, and each binomial center has the
same morphism to the original surface as its labeled residue scheme. The construction
allows repeated centers and uses the given lattice basis for the binomial coordinates. -/
theorem exists_toric_internal_factorization
    (b : Module.Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hT : IsLogarithmicBoundaryTower (Φ.boundaryIdeal hc.nonempty_cones) f[Φ] T P c) :
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (u : Ψ.IsSubdivision Φ)
      (ρ : Fin m → Ψ.Ray) (z : Fin m → ℂˣ),
      letI : Nonempty Ψ.cones := u.nonempty_cones_of_nonempty hc.nonempty_cones
      let A := Ψ.internalBlowupTower b ρ z
      ∃ e : A.1 ≅ Y, e.hom ≫ T.toBase = A.2.toTower.toBase ≫ u.toFanHom.algebraicMap ∧
        P.comap e.hom = A.2.boundaryι.ker ∧
        ∀ j, ∃ a : S ≅ (c j).left,
          (ρ j).binomialCenterOnBoundary rk(b) (b.detDualEquiv_self _)
              ((ρ j).surjective_detCharacter b) (z j) ≫
              (Ψ.boundaryIdeal inferInstance).subschemeι ≫ u.toFanHom.algebraicMap =
            a.hom ≫ (c j).hom := by
  have : IsReduced (Φ.boundaryIdeal hc.nonempty_cones).subscheme := by
    rw [boundaryIdeal_def]
    infer_instance
  have : Smooth f[Φ] := Φ.smooth_algebraicRealizationStructureMap hΦ
  obtain ⟨F⟩ := hT.nonempty_orderedFactorization
  obtain ⟨Ψ, hΨ, u, e, he, hb, -⟩ :=
    Φ.exists_toric_subdivision_of_nodal_boundary_tower hΦ hc rk(b) F.isNodal
  let : Nonempty Ψ.cones := u.nonempty_cones_of_nonempty hc.nonempty_cones
  let E := Ψ.boundaryIdeal inferInstance
  have hE : F.boundary.comap e.hom = E := F.boundary_eq ▸ hb
  let d₀ := subschemeMap E F.boundary e.hom (le_map_iff_comap_le.mpr hE.le)
  have hd₀ : d₀ ≫ F.boundary.subschemeι = E.subschemeι ≫ e.hom :=
    subschemeMap_subschemeι _ _ _ _
  have hpb : IsPullback E.subschemeι d₀ e.hom F.boundary.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ hd₀.symm (by simpa only [ker_subschemeι] using hE)
  have : IsIso d₀ := hpb.isIso_snd_of_isIso
  let d := asIso d₀
  have hdι : d.hom ≫ F.boundary.subschemeι = E.subschemeι ≫ e.hom := hd₀
  have hd : d.hom ≫ F.boundary.subschemeι ≫ F.tower.toBase ≫ f[Φ] =
      E.subschemeι ≫ f[Ψ] := by
    simp only [reassoc_of% hdι, reassoc_of% he,
      FanHom.algebraicMap_comp_algebraicRealizationStructureMap]
  have (j : Fin m) : IsIso ((c j).hom ≫ f[Φ]) := hT.isIso_center_comp_structureMap j
  let a (j : Fin m) := (asIso ((c j).hom ≫ f[Φ])).symm
  choose ρ z hz using fun j ↦ exists_binomial_center_of_orderedFactorization F b hΨ
    (u.isComplete_iff.mpr hc) d hd j (a j) (Iso.inv_hom_id _)
  have hJ (j : Fin m) :
      (F.center j).ker.comap d.hom = ((ρ j).internalCenter b (z j)).val := by
    rw [Ray.internalCenter_val, ← Scheme.Hom.ker_comp_of_isIso (a j).hom,
      ← hz j, Scheme.Hom.comap_ker_comp_of_isClosedImmersion]
  let A := Ψ.internalBlowupTower b ρ z
  obtain ⟨g, hg, hgb⟩ : ∃ g : A.1 ≅ F.internalTower.1,
      IsLift e A.2.toTower F.internalTower.2.toTower g ∧
      A.2.boundaryι ≫ g.hom = d.hom ≫ F.internalTower.2.boundaryι := by
    dsimp only [A]
    rw [Fan.internalBlowupTower_eq_alongBoundary]
    exact exists_isLift_alongBoundary e d hdι.symm
      (fun j ↦ (ρ j).internalCenter b (z j))
      (fun j ↦ ⟨(F.center j).ker, F.isEffectiveCartier_center j⟩) hJ
  have hboundary : F.internalTower.2.boundaryι.ker.comap g.hom = A.2.boundaryι.ker := by
    have hk : (A.2.boundaryι ≫ g.hom).ker = F.internalTower.2.boundaryι.ker := by
      rw [hgb, Scheme.Hom.ker_comp_of_isIso]
    rw [← hk, Scheme.Hom.comap_ker_comp_of_isClosedImmersion]
  refine ⟨Ψ, hΨ, u, ρ, z, g ≪≫ F.iso, ?_, ?_, fun j ↦ ⟨a j, ?_⟩⟩
  · simp only [Iso.trans_hom, Category.assoc, F.iso_hom_toBase, hg.hom_toBase_assoc, he, A]
  · simpa only [Iso.trans_hom, comap_comp, F.comap_boundary_iso_hom, A] using hboundary
  · rw [← he, reassoc_of% hdι.symm, reassoc_of% (hz j), F.center_toBase]

end TauCeti.Toric.Fan

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
public import QPainleve.Geometry.Toric.Fan.Boundary.NodalPullback
public import QPainleve.Geometry.Toric.Fan.Subdivision
public import QPainleve.Geometry.Toric.Fan.Subdivision.InternalBlowup

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Blowup.Pullback
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import QPainleve.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Tower
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# Common nodal refinements of internal toric blowup models

Two regular surface fans with the same support and matching ordered binomial centers
can be compared on a common internal model. Both projections are nodal blowup towers
up to isomorphism, and their reduced total boundaries are identified with the strict
boundary of the internal model over the subdividing fan. Conversely, any
specified nodal tower on an ordered internal model arises from such a subdivision.

For toric models with infinitely near centers and blowups of boundary nodes, see
[Gross, Hacking and Keel, Definition 1.2 and the paragraph following it][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S1
-/

public section

open AlgebraicGeometry CategoryTheory Limits Multiplicative QPainleve QPainleve.BlowupTower
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} (b : Module.Basis (Fin 2) ℤ N) {n : ℕ}

section Subdivision

variable [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones]

local notation "model" => internalBlowupTower b

/-- A regular subdivision induces a nodal blowup projection of the ordered internal
model. Its reduced total boundary is the strict boundary of the refined internal model,
its restriction to the strict boundaries is the toric subdivision map, and the square
of projections to the fan schemes is cartesian. -/
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
      ((B.2.boundaryι.ker.comap T.toBase).radical).comap e.hom = A.2.boundaryι.ker ∧
      A.2.boundaryι ≫ e.hom ≫ T.toBase = h.boundaryMap hΦ₀ hΨ₀ ≫ B.2.boundaryι := by
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
  refine ⟨m, Z, T, e, hT, he.symm ▸ hg', ?_, by rw [he, hb]⟩
  rw [← radical_comap_of_isOpenImmersion, ← comap_comp, he]
  exact h.radical_comap_internalBlowupTower_boundary b ρ c g' hg' hb

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
      ((C.2.boundaryι.ker.comap U.toBase).radical).comap f.hom = A.2.boundaryι.ker ∧
      A.2.boundaryι ≫ e.hom ≫ T.toBase = hΩΦ.boundaryMap hΩ₀ hΦ₀ ≫ B.2.boundaryι ∧
      A.2.boundaryι ≫ f.hom ≫ U.toBase = hΩΨ.boundaryMap hΩ₀ hΨ₀ ≫ C.2.boundaryι := by
  dsimp only
  have hmatch := hΩΦ.liftRay_comp_eq_of_primitiveGenerator_eq hΩΨ ρ τ hρτ
  obtain ⟨m, Y, T, e, hT, he, hD, hboundary⟩ :=
    hΩΦ.exists_nodal_refinement_internalBlowupTower b hΩ hΦ ρ c
  have hright := hΩΨ.exists_nodal_refinement_internalBlowupTower b hΩ hΨ τ c
  dsimp only at hright
  rw [← hmatch] at hright
  obtain ⟨l, Z, U, f, hU, hf, hE, hboundary'⟩ := hright
  exact ⟨m, l, Y, Z, T, U, e, f, hT, hU, he, hf, hD, hE, hboundary, hboundary'⟩

end Subdivision

section OrderedModel

variable (ρ : Fin n → Φ.Ray) (c : Fin n → ℂˣ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)

local notation "s[" Δ "]" => Fan.algebraicRealizationStructureMap Δ
local notation "π[" A "]" => toBase (WithBoundary.toTower (Sigma.snd A))
local notation "I[" A "]" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd A))
local notation "A" => internalBlowupTower (h₀ := hc.nonempty_cones) b ρ c
local notation "D" => Φ.boundaryIdeal hc.nonempty_cones
local notation "map[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)

include hΦ in
private theorem exists_pointBlowup_internalBlowupTower_of_node
    {p : (A).1} {J : (A).1.IdealSheafData} (hJ : J = ((A).1.fromSpecResidueField p).ker)
    (hp : I[A].IsNodeOfReducedBoundary (π[A] ≫ s[Φ]) p) :
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (H : Ψ.IsSubdivision Φ),
      let B := internalBlowupTower (h₀ := H.nonempty_cones_of_nonempty hc.nonempty_cones)
        b (H.liftRay ∘ ρ) c
      ∃ e : B.1 ≅ J.blowup,
        IsPullback (e.hom ≫ J.blowupToBase) π[B] π[A] map[H] ∧
        ((I[A].comap J.blowupToBase).radical).comap e.hom = I[B] := by
  let : Nonempty Φ.cones := hc.nonempty_cones
  have : IsReduced (D).subscheme := by rw [Φ.boundaryIdeal_def]; infer_instance
  obtain ⟨q, rfl, hq⟩ :=
    ((A).2.boundaryι.isNodeOfReducedBoundary_ker_iff _ _).mp hp
  rw [← Category.assoc, WithBoundary.boundaryι_toBase] at hq
  have hnode : (D).IsNodeOfReducedBoundary s[Φ] ((D).subschemeι q) :=
    (isNodeOfReducedBoundary_iff_of_isReduced _ _ _).mpr ⟨q, rfl, hq⟩
  have hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  obtain ⟨σ, ⟨hσ, hx⟩, -⟩ :=
    (Φ.isNodeOfReducedBoundary_iff_existsUnique_twoRayCone hΦ hc hdim).mp hnode
  let v := Φ.distinguishedPointHom σ
  let K := v.ker
  have hv : IsClosedImmersion v := Φ.isClosedImmersion_distinguishedPointHom σ
  have hcq := hx ▸ Φ.isClosed_singleton_distinguishedPoint σ
  have hiso := Φ.mem_isoLocus_internalBlowupTower_toBase_of_isNodeAt b ρ c hq
  have hproj : π[A] ((A).2.boundaryι q) = (D).subschemeι q := by
    rw [← Scheme.Hom.comp_apply, WithBoundary.boundaryι_toBase]
  have hcenter : K.comap π[A] = J := by
    dsimp only [K]
    rw [hJ, v.ker_eq_ker_fromSpecResidueField, hx, ← hproj]
    exact (π[A]).comap_ker_fromSpecResidueField_of_mem_isoLocus
      (hproj.symm ▸ hcq) (hproj.symm ▸ hiso)
  have hsupp : (K.support : Set Φ.algebraicRealization) ⊆ (π[A]).isoLocus := by
    dsimp only [K]
    rw [v.ker_eq_ker_fromSpecResidueField, hx,
      Scheme.support_ker_fromSpecResidueField_of_isClosed hcq]
    exact Set.singleton_subset_iff.mpr hiso
  obtain ⟨h₀, d, -, hd, -⟩ := Φ.exists_iso_blowup_starSubdivisionAlong hΦ σ hdim hσ
  let Ψ := Φ.starSubdivisionAlong hΦ σ.property
  let H := Φ.starSubdivisionAlong_isSubdivision hΦ σ.property h₀
  let : Nonempty Ψ.cones := H.nonempty_cones_of_nonempty hc.nonempty_cones
  let B := internalBlowupTower (h₀ := H.nonempty_cones_of_nonempty hc.nonempty_cones)
    b (H.liftRay ∘ ρ) c
  obtain ⟨g, hg, hb, -⟩ := H.exists_isPullback_internalBlowupTower b ρ c
  have hpb : ∃ t : J.blowup ⟶ Ψ.algebraicRealization,
      IsPullback J.blowupToBase t π[A] map[H] := by
    rw [← hcenter]
    let t := K.blowupMap π[A] ≫ d.inv
    refine ⟨t, (K.isPullback_blowupMap_of_support_subset_isoLocus π[A] hsupp).of_iso'
      (Iso.refl _) (Iso.refl _) d (Iso.refl _) (by simp) (by simp [t]) (by simp) ?_⟩
    simpa only [Iso.refl_hom, Category.comp_id] using hd
  obtain ⟨t, ht⟩ := hpb
  let e : B.1 ≅ J.blowup := hg.isoIsPullback _ _ ht
  have he := hg.isoIsPullback_hom_fst _ _ ht
  refine ⟨Ψ, Φ.isRegular_starSubdivisionAlong hΦ σ.property, H, e, he.symm ▸ hg, ?_⟩
  rw [← radical_comap_of_isOpenImmersion, ← comap_comp, he]
  exact H.radical_comap_internalBlowupTower_boundary b ρ c g hg hb

include hΦ in
/-- Every specified nodal blowup tower on an ordered internal model is the
pullback of a regular fan subdivision. The refined model uses the same ordered
parameters on the lifted rays, and its strict boundary is the reduced total
transform of the original strict boundary. -/
theorem exists_subdivision_of_nodalBoundaryTower_internalBlowupTower
    {n : ℕ} {Z : Scheme} {T : BlowupTower (A).1 n Z}
    (hT : IsNodalBoundaryTower I[A] (π[A] ≫ s[Φ]) (𝟙 _) T) :
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (H : Ψ.IsSubdivision Φ),
      let B := internalBlowupTower (h₀ := H.nonempty_cones_of_nonempty hc.nonempty_cones)
        b (H.liftRay ∘ ρ) c
      ∃ e : B.1 ≅ Z,
        IsPullback (e.hom ≫ T.toBase) π[B] π[A] map[H] ∧
        ((I[A].comap T.toBase).radical).comap e.hom = I[B] := by
  induction hT with
  | nil =>
    have hρ : (IsSubdivision.refl Φ).liftRay ∘ ρ = ρ :=
      funext fun j ↦ IsSubdivision.liftRay_refl (ρ j)
    refine ⟨Φ, hΦ, IsSubdivision.refl Φ, ?_⟩
    dsimp only
    rw [hρ, toBase_nil, IsSubdivision.toFanHom_refl, FanHom.algebraicMap_id]
    have : IsReduced (D).subscheme := by rw [Φ.boundaryIdeal_def]; infer_instance
    have : IsReduced (I[A]).subscheme := Scheme.Hom.isReduced_image (A).2.boundaryι
    exact ⟨Iso.refl _, by simpa using IsPullback.of_horiz_isIso (f := π[A]) ⟨by simp⟩,
      by simp [(I[A]).isReduced_subscheme_iff_radical_eq.mp inferInstance]⟩
  | @snoc n Y T J hT p hp hJ hnode ih =>
    obtain ⟨Ψ, hΨ, H, e, hpb, hboundary⟩ := ih
    let hB := H.nonempty_cones_of_nonempty hc.nonempty_cones
    let B := internalBlowupTower (h₀ := hB) b (H.liftRay ∘ ρ) c
    let J' := J.comap e.hom
    have hpoint : e.hom (e.inv p) = p := by simp
    have hJ' : J' = (B.1.fromSpecResidueField (e.inv p)).ker := by
      dsimp only [J']
      rw [hJ, ← e.hom.comap_ker_fromSpecResidueField_apply (e.inv p), hpoint]
    have hover : e.hom ≫ T.toBase ≫ π[A] ≫ s[Φ] = π[B] ≫ s[Ψ] := by
      rw [← Category.assoc e.hom, ← Category.assoc, hpb.w, Category.assoc,
        FanHom.algebraicMap_comp_algebraicRealizationStructureMap]
    have hnode' : I[B].IsNodeOfReducedBoundary (π[B] ≫ s[Ψ]) (e.inv p) := by
      have hn := ((I[A]).comap T.toBase).isNodeOfReducedBoundary_comap_iff_of_isOpenImmersion
        (T.toBase ≫ π[A] ≫ s[Φ]) e.hom (e.inv p)
      rw [hpoint, hover, ← isNodeOfReducedBoundary_radical, radical_comap_of_isOpenImmersion,
        hboundary] at hn
      exact hn.mpr (by simpa only [Category.comp_id, Category.assoc] using hnode)
    obtain ⟨Ω, hΩ, F, g, hgb, hg⟩ :=
      exists_pointBlowup_internalBlowupTower_of_node b (H.liftRay ∘ ρ) c hΨ
        (H.isComplete_iff.mpr hc) hJ' hnode'
    let a := blowupIso e (rfl : J.comap e.hom = J')
    have ha : (g ≪≫ a).hom ≫ (T.snoc J).toBase =
        (g.hom ≫ J'.blowupToBase) ≫ e.hom ≫ T.toBase := by
      simp only [Iso.trans_hom, toBase_snoc, Category.assoc, a,
        blowupIso_hom_blowupToBase_assoc, J']
    have hρ : (F.trans H).liftRay ∘ ρ = F.liftRay ∘ (H.liftRay ∘ ρ) :=
      funext fun j ↦ F.liftRay_trans H (ρ j)
    refine ⟨Ω, hΩ, F.trans H, ?_⟩
    dsimp only
    rw [hρ]
    refine ⟨g ≪≫ a, ?_, ?_⟩
    · rw [ha, IsSubdivision.toFanHom_trans F H, FanHom.algebraicMap_comp]
      exact hgb.paste_horiz hpb
    · rwa [← radical_comap_of_isOpenImmersion, ← comap_comp, ha, comap_comp,
        comap_comp (I[A]) e.hom T.toBase,
        ← radical_comap_radical _ (g.hom ≫ J'.blowupToBase),
        radical_comap_of_isOpenImmersion ((I[A]).comap T.toBase) e.hom, hboundary,
        comap_comp, radical_comap_of_isOpenImmersion]

end OrderedModel

end TauCeti.Toric.Fan

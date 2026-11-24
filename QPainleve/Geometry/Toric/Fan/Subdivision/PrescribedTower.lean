/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Subdivision
public import QPainleve.Geometry.Toric.Fan.Subdivision.NodalRefinement

import QPainleve.AlgebraicGeometry.Blowup.Pullback
import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Pullback
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Boundary
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Specified nodal refinements of ordered toric models

A nodal tower on an ordered internal blowup model is induced by a subdivision of the
model's toric fan. Each successive center lies above a node of the current toric boundary,
where the internal blowdown is a local isomorphism. The cartesian comparison preserves the
ordered internal centers and their total exceptional classes, including at repeated centers.

For the use of nodal refinements in comparing toric presentations, see
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*, §1][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S1
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [hΦ₀ : Nonempty Φ.cones]
  (b : Module.Basis (Fin 2) ℤ N) {m : ℕ} (r : Fin m → Φ.Ray) (c : Fin m → ℂˣ)

local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "s[" Δ "]" => Fan.algebraicRealizationStructureMap Δ
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)
local notation "base[" A "]" => toBase (WithBoundary.toTower (Sigma.snd A))
local notation "boundary[" A "]" => WithBoundary.boundaryι (Sigma.snd A)
local notation "model" => internalBlowupTower b
local notation "M" => model r c

private theorem node_image_and_mem_isoLocus {p : M.1}
    (hp : (boundary[M]).ker.IsNodeOfReducedBoundary (base[M] ≫ s[Φ]) p) :
    (Φ.boundaryIdeal hΦ₀).IsNodeOfReducedBoundary s[Φ] (base[M] p) ∧
      base[M] p ∈ base[M].isoLocus := by
  let D := Φ.boundaryIdeal hΦ₀
  have : IsReduced D.subscheme := by
    dsimp only [D]
    rw [Fan.boundaryIdeal_def]
    infer_instance
  obtain ⟨q, rfl, hq⟩ := ((boundary[M]).isNodeOfReducedBoundary_ker_iff _ p).mp hp
  have hnode : (D.subschemeι ≫ s[Φ]).IsNodeAt q := by
    simpa only [← Category.assoc, WithBoundary.boundaryι_toBase] using hq
  have hpoint : base[M] (boundary[M] q) = D.subschemeι q := by
    rw [← Scheme.Hom.comp_apply, WithBoundary.boundaryι_toBase]
  refine ⟨(D.isNodeOfReducedBoundary_iff_of_isReduced _ _).mpr ⟨q, hpoint.symm, hnode⟩, ?_⟩
  rw [hpoint, internalBlowupTower_eq_alongBoundary]
  apply mem_isoLocus_toBase_alongBoundary
  rintro j ⟨z, hz, hzq⟩
  have he := D.subschemeι.isClosedEmbedding.injective hzq
  subst z
  exact (r j).not_isNodeAt_mem_support_internalCenter b (c j) hz hnode

private theorem exists_cartesian_blowup_of_internal_model_node
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) {p : M.1}
    (hp : (boundary[M]).ker.IsNodeOfReducedBoundary (base[M] ≫ s[Φ]) p) :
    let I := (M.1.fromSpecResidueField p).ker
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (H : Ψ.IsSubdivision Φ),
      ∃ g : I.blowup ⟶ X[Ψ], IsPullback I.blowupToBase g base[M] π[H] := by
  intro I
  have hrank := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  obtain ⟨hn, hlocal⟩ := node_image_and_mem_isoLocus b r c hp
  obtain ⟨σ, ⟨hσ, hpoint⟩, -⟩ :=
    (Φ.isNodeOfReducedBoundary_iff_existsUnique_twoRayCone hΦ hc hrank).mp hn
  obtain ⟨h₀, d, -, hd, -⟩ := Φ.exists_iso_blowup_starSubdivisionAlong hΦ σ hrank hσ
  let Ψ := Φ.starSubdivisionAlong hΦ σ.property
  let H := Φ.starSubdivisionAlong_isSubdivision hΦ σ.property h₀
  let J := (Φ.distinguishedPointHom σ).ker
  have hJ : J = (X[Φ].fromSpecResidueField (base[M] p)).ker := by
    rw [← hpoint]
    exact (Φ.distinguishedPointHom σ).ker_eq_ker_fromSpecResidueField
  have hclosed := hpoint ▸ Φ.isClosed_singleton_distinguishedPoint σ
  have hI : I = J.comap base[M] :=
    ((congrArg (·.comap base[M]) hJ).trans
      ((base[M]).comap_ker_fromSpecResidueField_of_mem_isoLocus hclosed hlocal)).symm
  have hsupport : (J.support : Set X[Φ]) ⊆ base[M].isoLocus := by
    rw [hJ, Scheme.support_ker_fromSpecResidueField_of_isClosed hclosed]
    exact Set.singleton_subset_iff.mpr hlocal
  have hk : I = (J.comap base[M]).comap (Iso.refl M.1).hom := by
    simpa only [Iso.refl_hom, comap_id] using hI
  let k := blowupIso (Iso.refl M.1) hk
  refine ⟨Ψ, Φ.isRegular_starSubdivisionAlong hΦ σ.property, H,
    k.hom ≫ J.blowupMap base[M] ≫ d.inv, ?_⟩
  refine (J.isPullback_blowupMap_of_support_subset_isoLocus base[M] hsupport).of_iso'
    k (Iso.refl _) d (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa only [Iso.refl_hom, Category.comp_id] using blowupIso_hom_blowupToBase (Iso.refl M.1) hk
  · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simpa only [Iso.refl_hom, Category.comp_id] using hd

private theorem exists_starSubdivision_of_internal_model_node
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) {p : M.1}
    (hp : (boundary[M]).ker.IsNodeOfReducedBoundary (base[M] ≫ s[Φ]) p) :
    let I := (M.1.fromSpecResidueField p).ker
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (H : Ψ.IsSubdivision Φ),
      letI := H.nonempty_cones_of_nonempty hΦ₀
      let L := model (H.liftRay ∘ r) c
      ∃ e : L.1 ≅ I.blowup,
        IsPullback (e.hom ≫ I.blowupToBase) base[L] base[M] π[H] ∧
        (((boundary[M]).ker.comap I.blowupToBase).radical).comap e.hom =
          (boundary[L]).ker ∧
        ∀ j, LineBundleClass.pullback (e.hom ≫ I.blowupToBase)
          (M.2.toTower.exceptionalClass j) = L.2.toTower.exceptionalClass j := by
  intro I
  obtain ⟨Ψ, hΨ, H, g', hcart⟩ := exists_cartesian_blowup_of_internal_model_node b r c hΦ hc hp
  let : Nonempty Ψ.cones := H.nonempty_cones_of_nonempty hΦ₀
  let L := model (H.liftRay ∘ r) c
  obtain ⟨g, hg, hb, hclasses⟩ := H.exists_isPullback_internalBlowupTower b r c
  let e := hg.isoIsPullback _ _ hcart
  have he : e.hom ≫ I.blowupToBase = g := hg.isoIsPullback_hom_fst _ _ hcart
  refine ⟨Ψ, hΨ, H, e, he.symm ▸ hg, ?_, ?_⟩
  · rw [← radical_comap_of_isOpenImmersion, ← comap_comp, he]
    exact H.radical_comap_internalBlowupTower_boundary b r c hg hb
  · simpa only [he] using hclasses

/-- A specified nodal blowup tower on an ordered internal model is cartesian
over a regular fan subdivision. The refined model uses the same ordered binomial
parameters and the lifts of the same rays. Its identification with the given
tower respects the reduced boundary and pulls back every total internal
exceptional class in the original order. -/
theorem exists_subdivision_of_nodal_tower_on_internal_model
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    {n : ℕ} {Y : Scheme} {T : QPainleve.BlowupTower M.1 n Y}
    (hT : IsNodalBoundaryTower (boundary[M]).ker (base[M] ≫ s[Φ]) (𝟙 _) T) :
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (H : Ψ.IsSubdivision Φ),
      letI := H.nonempty_cones_of_nonempty hΦ₀
      let L := model (H.liftRay ∘ r) c
      ∃ e : L.1 ≅ Y, IsPullback (e.hom ≫ T.toBase) base[L] base[M] π[H] ∧
        (((boundary[M]).ker.comap T.toBase).radical).comap e.hom = (boundary[L]).ker ∧
        ∀ j, LineBundleClass.pullback (e.hom ≫ T.toBase)
          (M.2.toTower.exceptionalClass j) = L.2.toTower.exceptionalClass j := by
  induction hT with
  | nil =>
    let H := IsSubdivision.refl Φ
    have hr : H.liftRay ∘ r = r := (rfl)
    refine ⟨Φ, hΦ, H, ?_⟩
    dsimp only
    rw [hr, toBase_nil]
    refine ⟨Iso.refl _, ?_, ?_, ?_⟩
    · rw [IsSubdivision.toFanHom_refl, FanHom.algebraicMap_id]
      simpa only [Iso.refl_hom, Category.comp_id] using
        (IsPullback.of_horiz_isIso (fst := 𝟙 M.1) (snd := base[M]) (f := base[M])
          (g := 𝟙 X[Φ]) ⟨by simp⟩)
    · have : IsReduced (Φ.boundaryIdeal hΦ₀).subscheme := by
        rw [Fan.boundaryIdeal_def]
        infer_instance
      have : IsReduced (boundary[M]).ker.subscheme :=
        isReduced_of_isOpenImmersion (asIso (boundary[M]).toImage).inv
      simpa only [Iso.refl_hom, comap_id] using
        (isReduced_subscheme_iff_radical_eq (boundary[M]).ker).mp inferInstance
    · intro j
      simp only [Iso.refl_hom, Category.comp_id, LineBundleClass.pullback_id]
  | @snoc n Y T I hT p hp hI hnode ih =>
    -- Move the next node to the current ordered model, then paste its
    -- cartesian blowup square with the comparison for the preceding tower.
    obtain ⟨Δ, hΔ, H, e, he, hB, hE⟩ := ih
    let : Nonempty Δ.cones := H.nonempty_cones_of_nonempty hΦ₀
    let L := model (H.liftRay ∘ r) c
    have hs : e.hom ≫ (T.toBase ≫ base[M] ≫ s[Φ]) = base[L] ≫ s[Δ] := by
      rw [← Category.assoc e.hom T.toBase, ← Category.assoc, he.w,
        Category.assoc, H.toFanHom.algebraicMap_comp_algebraicRealizationStructureMap]
    let q := e.inv p
    have hq : e.hom q = p := by simp [q]
    have hn : (boundary[L]).ker.IsNodeOfReducedBoundary (base[L] ≫ s[Δ]) q := by
      have h := isNodeOfReducedBoundary_comap_iff_of_isOpenImmersion
        ((boundary[M]).ker.comap T.toBase) (T.toBase ≫ base[M] ≫ s[Φ]) e.hom q
      have hn' := h.mpr (by simpa only [Category.comp_id, Category.assoc, hq] using hnode)
      rwa [← isNodeOfReducedBoundary_radical, radical_comap_of_isOpenImmersion, hB, hs] at hn'
    obtain ⟨Ψ, hΨ, K, d, hd, hD, hF⟩ :=
      exists_starSubdivision_of_internal_model_node b (H.liftRay ∘ r) c hΔ
        (H.isComplete_iff.mpr hc) hn
    have hcenter : (L.1.fromSpecResidueField q).ker = I.comap e.hom := by
      rw [hI, ← hq, e.hom.comap_ker_fromSpecResidueField_apply]
    let J := (L.1.fromSpecResidueField q).ker
    let a := blowupIso e hcenter
    have ha : a.hom ≫ I.blowupToBase = J.blowupToBase ≫ e.hom :=
      blowupIso_hom_blowupToBase e hcenter
    let f := d ≪≫ a
    have hf : f.hom ≫ (T.snoc I).toBase =
        (d.hom ≫ J.blowupToBase) ≫ e.hom ≫ T.toBase := by
      simp only [f, Iso.trans_hom, toBase_snoc, Category.assoc, reassoc_of% ha]
    have hr : (K.trans H).liftRay ∘ r = K.liftRay ∘ H.liftRay ∘ r := (rfl)
    refine ⟨Ψ, hΨ, K.trans H, ?_⟩
    dsimp only
    rw [hr]
    refine ⟨f, ?_, ?_, ?_⟩
    · rw [hf, IsSubdivision.toFanHom_trans, FanHom.algebraicMap_comp]
      simpa only [Category.assoc] using hd.paste_horiz he
    · -- Use the reduced boundary of the preceding stage before the final blowup.
      let E := (boundary[M]).ker.comap T.toBase
      have hE' : ((E.comap e.hom).comap J.blowupToBase).radical =
          ((boundary[L]).ker.comap J.blowupToBase).radical := by
        rw [← radical_comap_radical (E.comap e.hom), radical_comap_of_isOpenImmersion E e.hom, hB]
      rw [← radical_comap_of_isOpenImmersion, ← comap_comp, hf, Category.assoc,
        comap_comp, comap_comp, comap_comp, radical_comap_of_isOpenImmersion _ d.hom]
      exact (congrArg (·.comap d.hom) hE').trans hD
    · intro j
      rw [hf, ← LineBundleClass.pullback_comp, hE]
      exact hF j

end TauCeti.Toric.Fan

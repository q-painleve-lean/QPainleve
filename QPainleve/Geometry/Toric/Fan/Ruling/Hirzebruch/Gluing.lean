/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch.Transition
public import QPainleve.Geometry.Toric.Fan.Ruling.Laurent.Scaling

/-!
# Gluing Hirzebruch ruling charts

Two product charts of a ruling over the projective line identify it with the
Hirzebruch ruling when their overlap has the same transition. The comparison
is over the given base and is characterized by its two prescribed chart maps.
The overlap automorphism in Laurent coordinates is the projective scaling
`[X₀ : X₁] ↦ [t⁻ᵉ X₀ : X₁]`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Module
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric.Fan

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "PL" => projectiveLine ℂ
local notation "p" => (PL ↘ S)
local notation "U[" k "]" => Fan.algebraicRealization (projectiveLineAffineFan k)
local notation "j[" k "]" => projectiveLineAffineFanι k
local notation "s[" k "]" => Fan.algebraicRealizationStructureMap (projectiveLineAffineFan k)
local notation "t" => (projectiveLineTorusFan.algebraicRealization ↘ S)
local notation "iT" => projectiveLineTorusι
local notation "a[" k "]" => FanHom.algebraicMap (projectiveLineTorusToAffineFan k)
local notation "Pₐ[" k "]" => pullback p s[k]
local notation "d[" k "]" => projectiveLineTorusProductToAffine k

local notation "laurentProduct" =>
  Iso.symm (IsPullback.isoPullback isPullback_projectiveLineTorusProduct) ≪≫
    projectiveLineTorusProductIsoLaurent

/-- The overlap automorphism is diagonal scaling on the projective line over the
Laurent base. Its scaling factor uses the base coordinate `t = X₁ / X₀` of chart zero. -/
@[reassoc]
theorem hirzebruchRulingOverlapTransition_hom_comp_laurentProduct (e : ℤ) :
    (hirzebruchRulingOverlapTransition e).hom ≫ (laurentProduct).hom =
      (laurentProduct).hom ≫ (projectiveLine.scalingBy (LaurentPolynomial ℂ)
        (LaurentPolynomial.isUnit_T (-e)).unit).hom := by
  apply (cancel_epi isPullback_projectiveLineTorusProduct.isoPullback.hom).mp
  rw [isoPullback_hom_comp_hirzebruchRulingOverlapTransition_hom_assoc]
  have h (x : (Fin 1 → ℤ) × (Fin 1 → ℤ)) :
      (projectiveLineTorusShear e).toFanHom.latticeMap x = (x.1 + e • x.2, x.2) := by
    rw [FanEquiv.toFanHom_latticeMap]
    exact projectiveLineTorusShear_latticeEquiv_apply e x
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using
    FanHom.algebraicMap_comp_projectiveLineTorusProductIsoLaurent_of_shear _ e h

private def affineCover : Scheme.OpenCover PL :=
  Scheme.Cover.mkOfCovers (Fin 2) (fun k ↦ U[k]) projectiveLineAffineFanι
    exists_projectiveLineAffineFanι_apply_eq

variable {X Y : Scheme} (g : X ⟶ PL) (f : Y ⟶ PL)

private def torusToRulingChart (k : Fin 2) : pullback g iT ⟶ pullback g j[k] :=
  pullback.lift (pullback.fst g iT) (pullback.snd g iT ≫ a[k]) (by
    rw [Category.assoc, projectiveLineTorusToAffineFan_algebraicMap_comp_ι, pullback.condition])

@[reassoc (attr := simp)]
private theorem torusToRulingChart_fst (k : Fin 2) :
    torusToRulingChart g k ≫ pullback.fst g j[k] = pullback.fst g iT :=
  pullback.lift_fst _ _ _

private def overlapIso :
    pullback g iT ≅ pullback (pullback.fst g j[0]) (pullback.fst g j[1]) :=
  IsOpenImmersion.isoOfRangeEq (pullback.fst g iT)
    (pullback.fst (pullback.fst g j[0]) (pullback.fst g j[1]) ≫ pullback.fst g j[0]) (by
      rw [IsOpenImmersion.range_pullback_to_base_of_right]
      simp only [IsOpenImmersion.range_pullbackFst, Scheme.Hom.coe_preimage,
        Scheme.Hom.coe_opensRange, range_projectiveLineTorusι, range_projectiveLineAffineFanι,
        Set.preimage_inter])

private theorem overlapIso_hom_fst :
    (overlapIso g).hom ≫ pullback.fst (pullback.fst g j[0]) (pullback.fst g j[1]) =
      torusToRulingChart g 0 := by
  apply (cancel_mono (pullback.fst g j[0])).mp
  rw [Category.assoc, torusToRulingChart_fst]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

private theorem overlapIso_hom_snd :
    (overlapIso g).hom ≫ pullback.snd (pullback.fst g j[0]) (pullback.fst g j[1]) =
      torusToRulingChart g 1 := by
  apply (cancel_mono (pullback.fst g j[1])).mp
  rw [Category.assoc, ← pullback.condition, torusToRulingChart_fst]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

private theorem glue_compatibility
    (l : ∀ k : Fin 2, pullback g j[k] ⟶ Y)
    (h : torusToRulingChart g 0 ≫ l 0 = torusToRulingChart g 1 ≫ l 1)
    (k m : Fin 2) :
    pullback.fst (pullback.fst g j[k]) (pullback.fst g j[m]) ≫ l k =
      pullback.snd (pullback.fst g j[k]) (pullback.fst g j[m]) ≫ l m := by
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  all_goals obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
  · exact congrArg (· ≫ l 0) ((cancel_mono (pullback.fst g j[0])).mp pullback.condition)
  · apply (cancel_epi (overlapIso g).hom).mp
    simpa only [← Category.assoc, overlapIso_hom_fst, overlapIso_hom_snd] using h
  · apply (cancel_epi (pullbackSymmetry (pullback.fst g j[0]) (pullback.fst g j[1])).hom).mp
    rw [← Category.assoc, ← Category.assoc, pullbackSymmetry_hom_comp_fst,
      pullbackSymmetry_hom_comp_snd]
    apply (cancel_epi (overlapIso g).hom).mp
    simpa only [← Category.assoc, overlapIso_hom_fst, overlapIso_hom_snd] using h.symm
  · exact congrArg (· ≫ l 1) ((cancel_mono (pullback.fst g j[1])).mp pullback.condition)

private def productChartCover (u : ∀ k : Fin 2, Pₐ[k] ⟶ Y)
    (hu : ∀ k, IsPullback (u k) (pullback.snd p s[k]) f j[k]) : Y.OpenCover :=
  Scheme.Cover.copy (affineCover.pullback₁ f) (Fin 2) (fun k ↦ Pₐ[k]) u (Equiv.refl _)
    (fun k ↦ (hu k).isoPullback) (fun k ↦ (hu k).isoPullback_hom_fst.symm)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  (b : Module.Basis (Fin 2) ℤ N) (e : ℤ) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun k ↦ (r k).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])
  (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)

local notation "q" => Fan.characterRuling Φ (LinearMap.toAddMonoidHom (Basis.coord b 1))
  (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)
local notation "A[" k "]" => hirzebruchRulingAffineIso b e r hr hΦ hc k
local notation "C[" k "]" => hirzebruchRulingTorusChartIso b e r hr hΦ hc k
local notation "v[" k "]" => Iso.inv (A[k]) ≫ pullback.fst q j[k]

include hr in
private theorem isPullback_hirzebruchRulingProductChart (k : Fin 2) :
    IsPullback v[k] (pullback.snd p s[k]) q j[k] :=
  (IsPullback.of_hasPullback q j[k]).of_iso' (A[k]).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by
      rw [Iso.refl_hom, Category.comp_id, ← cancel_epi (A[k]).hom, Iso.symm_hom,
        Iso.hom_inv_id_assoc, hirzebruchRulingAffineIso_hom_snd])
    (by simp) (by simp)

include hr in
/-- Two Cartesian product charts over the projective line with the Hirzebruch
transition glue to a unique isomorphism from the Hirzebruch ruling. The isomorphism
restricts to the prescribed product identifications over both affine charts. -/
theorem existsUnique_hirzebruch_ruling_iso_of_overlap_transition
    (u : ∀ k : Fin 2, Pₐ[k] ⟶ Y)
    (hu : ∀ k, IsPullback (u k) (pullback.snd p s[k]) f j[k])
    (hoverlap : d[0] ≫ u 0 =
      (hirzebruchRulingOverlapTransition e).hom ≫ d[1] ≫ u 1) :
    ∃! iso : Φ.algebraicRealization ≅ Y,
      iso.hom ≫ f = q ∧ ∀ k, v[k] ≫ iso.hom = u k := by
  let l k := (A[k]).hom ≫ u k
  have htorus (k : Fin 2) :
      torusToRulingChart q k ≫ l k = (C[k]).hom ≫ d[k] ≫ u k := by
    have hd : pullback.lift (pullback.fst p t) (pullback.snd p t ≫ a[k])
        (by
          rw [← projectiveLineTorusProductToAffine_fst k,
            ← projectiveLineTorusProductToAffine_snd k, Category.assoc, Category.assoc,
            pullback.condition]) = d[k] :=
      pullback.hom_ext (by simp) (by simp)
    simpa only [l, torusToRulingChart, hd, Category.assoc] using
      congrArg (· ≫ u k) (hirzebruchRulingTorusChartIso_comp_pullback b e r hr hΦ hc k).symm
  have hcompat : torusToRulingChart q 0 ≫ l 0 = torusToRulingChart q 1 ≫ l 1 := by
    rw [htorus, htorus, ← hirzebruchRulingTorusChartIso_hom_comp_overlapTransition b e r hr hΦ hc,
      Category.assoc, ← hoverlap]
  let cover : Scheme.OpenCover Φ.algebraicRealization := affineCover.pullback₁ q
  let m := cover.glueMorphisms l (glue_compatibility q l hcompat)
  have hm (k : Fin 2) : pullback.fst q j[k] ≫ m = l k := cover.ι_glueMorphisms _ _ k
  have hchart (k : Fin 2) : v[k] ≫ m = u k := by
    simp only [Category.assoc, hm, l, Iso.inv_hom_id_assoc]
  have hbase : m ≫ f = q := by
    refine cover.hom_ext _ _ (fun (k : Fin 2) ↦ ?_)
    -- The pullback cover uses the first projection of each base-change square.
    change pullback.fst q j[k] ≫ (m ≫ f) = pullback.fst q j[k] ≫ q
    rw [← Category.assoc, hm]
    dsimp only [l]
    rw [Category.assoc, (hu k).w, ← Category.assoc,
      hirzebruchRulingAffineIso_hom_snd, pullback.condition]
  have hcart (k : Fin 2) : IsPullback v[k] (𝟙 _) m (u k) := by
    refine IsPullback.of_bot ?_ (by simpa using hchart k) (hu k)
    simpa only [Category.id_comp, hbase] using
      isPullback_hirzebruchRulingProductChart b e r hr hΦ hc k
  let targetCover := productChartCover f u hu
  have hmIso : IsIso m := by
    refine IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme)
      targetCover (fun (k : Fin 2) ↦ ?_)
    rw [MorphismProperty.isomorphisms.iff]
    -- The local map is the second projection of the base change of the glued map.
    change IsIso (pullback.snd m (u k))
    have heq := (hcart k).isoPullback_inv_snd
    rw [Category.comp_id] at heq
    exact heq ▸ (hcart k).isoPullback.isIso_inv
  let := hmIso
  refine ⟨asIso m, ⟨hbase, hchart⟩, fun a ha ↦ ?_⟩
  apply Iso.ext
  refine cover.hom_ext _ _ (fun (k : Fin 2) ↦ ?_)
  -- Both maps are compared on the same pullback cover as in the gluing step.
  change pullback.fst q j[k] ≫ a.hom = pullback.fst q j[k] ≫ m
  rw [← cancel_epi (A[k]).inv]
  simpa only [← Category.assoc] using (ha.2 k).trans (hchart k).symm

end TauCeti.Toric.Fan

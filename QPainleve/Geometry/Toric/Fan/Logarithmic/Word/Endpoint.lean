/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Endpoint
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.Path

import QPainleve.Geometry.Toric.Fan.Logarithmic.Evaluation
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Tower

/-!
# Cluster words between specified ordered toric models

The word along a resolved path can be read in the labels and frame of a
prescribed terminal model. The final relabeling preserves each chain of repeated
centers, preserves boundary orientation, and matches the full Picard marking on
the common resolving surface.
This is the endpoint comparison for the factorization of
[Lutz, Theorem 8.4](https://arxiv.org/pdf/2005.05010v3#page=68).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module Multiplicative
open QPainleve.Cluster TauCeti TauCeti.AlgebraicGeometry TauCeti.LaurentRing
open scoped Sarkisov

namespace TauCeti.Toric.Fan.LogarithmicProjection

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Φ "]" => Fan.algebraicRealization Φ
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)

variable {Z : Scheme} [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)] [IsIntegral Z]
  {D : Z.IdealSheafData} {A B : LogarithmicProjection i D} {m : ℕ}

namespace OrderedToricModel

private theorem compare_relabel {U T : OrderedToricModel B m}
    (σ : Equiv.Perm (Fin m)) (hfan : T.fan = U.fan) (hb : T.basis = U.basis)
    (href : T.refinedProjection = U.refinedProjection)
    (hσ : ∀ j, ((hfan ▸ T.rays) j, T.parameters j) = (U.rays (σ j), U.parameters (σ j))) :
    T.exchangeMatrix = (Generator.permute σ).target U.exchangeMatrix ∧
      U.HasBoundarySign T 1 ∧
      let w := ((Generator.permute σ).toStep U.exchangeMatrix).toPath
      ∃ h, U.xEvaluation.compOfDefined (w.xRationalMap ℂ) h = T.xEvaluation := by
  cases U with
  | mk Φ hΦ J b r c e he hp =>
    cases T with
    | mk Ψ hΨ K b' s d e' he' hp' =>
      cases hfan
      cases hb
      let U : OrderedToricModel B m := ⟨Φ, hΦ, J, b, r, c, e, he, hp⟩
      let T : OrderedToricModel B m := ⟨Φ, hΨ, K, b, s, d, e', he', hp'⟩
      let : Nonempty Φ.cones := J.nonempty_cones_of_nonempty B.isComplete.nonempty_cones
      let F := FanEquiv.refl Φ
      have hray (j : Fin m) : F.rayEquiv (r (σ j)) = s j := by
        simpa only [F, FanEquiv.rayEquiv_refl, Equiv.refl_apply] using
          (congrArg Prod.fst (hσ j)).symm
      have hdet (x y : N) : b.detDualEquiv (F.latticeEquiv x) (F.latticeEquiv y) =
          b.detDualEquiv x y := by
        simp only [F, FanEquiv.refl_latticeEquiv, AddEquiv.refl_apply]
      have hh : T.hom = U.hom := eq_of_heq (LogarithmicProjection.ext_iff.mp href).2
      have hf : U.hom ≫ F.toFanHom.algebraicMap ≫ (Φ.torusTranslation 1).hom = T.hom := by
        simp only [F, FanEquiv.toFanHom_refl, FanHom.algebraicMap_id, Fan.torusTranslation_one,
          Iso.refl_hom]
        exact (Category.comp_id U.hom).trans hh.symm
      have hcomp : U.hom.toRationalMap.comp
          (F.toFanHom.algebraicMap ≫ (Φ.torusTranslation 1).hom).toRationalMap =
            T.hom.toRationalMap := by
        rw [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom, hf]
      obtain ⟨hm, hx⟩ := F.comp_xEvaluation_of_resolved_toric_iso hΦ b b r s σ
        (centerCharacter c) (centerCharacter d) 1 hray hdet (fun j ↦ by
          rw [← hray j]
          apply (F.comap_internalCenter_toricIso_eq_iff b b hdet hΦ (r (σ j)) 1 _ _).mpr
          simpa [centerCharacter, Finsupp.linearEquivFunOnFinite_symm_single] using
            congrArg Prod.snd (hσ j)) U.hom T.hom hcomp U.exchangeMatrix U.exchangeMatrix_matrix
      refine ⟨SkewExchangeMatrix.ext (T.exchangeMatrix_matrix.trans hm.symm), ?_, ?_⟩
      · exact U.hasBoundarySign_of_toricIso T F 1 hf 1
          (by simpa only [Units.val_one, one_mul] using hdet)
      · simpa only [xEvaluation_def] using hx

/-- Two ordered models of a specified projection in the same frame have the same refined
projection. A permutation from target labels to source labels matches their centers,
preserves the order over every repeated center, and compares their strict boundaries, branch
orientations, full Picard markings, and fixed-center X evaluations. -/
theorem exists_relabel (U T : OrderedToricModel B m) (hb : T.basis = U.basis) :
    ∃ (hfan : T.fan = U.fan) (σ : Equiv.Perm (Fin m))
      (hmat : T.exchangeMatrix = (Generator.permute σ).target U.exchangeMatrix),
      T.refinedProjection = U.refinedProjection ∧
      (∀ j, ((hfan ▸ T.rays) j, T.parameters j) = (U.rays (σ j), U.parameters (σ j))) ∧
      (∀ a b, a < b → (T.rays a, T.parameters a) = (T.rays b, T.parameters b) → σ a < σ b) ∧
      (U.tower.2.boundaryι ≫ U.iso.hom) ≍ (T.tower.2.boundaryι ≫ T.iso.hom) ∧
      U.HasBoundarySign T 1 ∧
      (∀ (a : Additive (LineBundleClass X[U.fan])) (x : Fin m → ℤ),
        T.picardMarking (Additive.ofMul (LineBundleClass.pullback
          (eqToHom (congrArg Fan.algebraicRealization hfan)) a.toMul), x ∘ σ) =
          U.picardMarking (a, x)) ∧
      let w : Word U.exchangeMatrix T.exchangeMatrix :=
        hmat.symm ▸ ((Generator.permute σ).toStep U.exchangeMatrix).toPath
      ∃ h, U.xEvaluation.compOfDefined (w.xRationalMap ℂ) h = T.xEvaluation := by
  let : Smooth (Z ↘ S) := SmoothOfRelativeDimension.smooth 2 (Z ↘ S)
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (Z ↘ S)
  cases U with
  | mk Φ hΦ J b r c e he hp =>
    cases T with
    | mk Ψ hΨ K b' s d e' he' hp' =>
      cases hb
      obtain ⟨hfan, σ, hσ, horder, hboundary, hmark⟩ :=
        Fan.exists_reindex_of_toric_internal_factorizations b B.isComplete hΦ hΨ J K
          r s c d e e' he he' hp hp'
      subst Ψ
      let U : OrderedToricModel B m := ⟨Φ, hΦ, J, b, r, c, e, he, hp⟩
      let T : OrderedToricModel B m := ⟨Φ, hΨ, K, b, s, d, e', he', hp'⟩
      have hN := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
      let : IsModification π[J] := J.isModification_algebraicMap
        B.isRegular hΦ B.isComplete.nonempty_cones hN
      have hh : T.hom = U.hom := π[J].eq_of_comp_eq_of_isModification
        (T.hom_comp_subdivision.trans U.hom_comp_subdivision.symm)
      have href : T.refinedProjection = U.refinedProjection :=
        LogarithmicProjection.ext rfl (heq_of_eq hh)
      obtain ⟨hmat, hsign, hw⟩ := compare_relabel (U := U) (T := T) σ rfl rfl href hσ
      refine ⟨rfl, σ, hmat, href, hσ, horder, hboundary, hsign, ?_, ?_⟩
      · intro a x
        exact (T.picardMarking_apply _).trans
          ((congrArg Additive.ofMul (hmark a x)).trans (U.picardMarking_apply _).symm)
      · generalize T.exchangeMatrix = E at hmat ⊢
        subst E
        exact hw

end OrderedToricModel

/-- Read a specified resolved Sarkisov path between two prescribed ordered models.
The lifted path still commutes with the given subdivisions. Its terminal model is
reframed and relabeled to match the prescribed target, including the strict boundary
and the pullback of every marked Picard class. The resulting typed word carries the
source X evaluation to the prescribed target evaluation at the generic point.
Its inversion sign compares the branch orientations of the prescribed models. -/
theorem exists_word_of_resolved_sarkisov_path_to_model [Z.IsProjectiveOver ℂ]
    (p : SarkisovPath A B) (U : OrderedToricModel A m) (T : OrderedToricModel B m) :
    ∃ (W R : OrderedToricModel B m)
      (q : @Quiver.Path _ (presentationQuiver m) ⟨A, U⟩ ⟨B, W⟩)
      (w : Word U.exchangeMatrix T.exchangeMatrix)
      (hfan : T.fan = R.fan) (σ : Equiv.Perm (Fin m)),
      (forgetPresentation m).mapPath q = p ∧
      π[U.subdivision].toRationalMap.comp p.rationalMap =
        (SarkisovPath.rationalMap ((refinePresentation m).mapPath q)).comp
          π[W.subdivision].toRationalMap ∧
      R.refinedProjection = W.refinedProjection ∧ T.refinedProjection = R.refinedProjection ∧
      R.basis = T.basis ∧ R.picardMarking ≍ W.picardMarking ∧
      (∀ j, ((hfan ▸ T.rays) j, T.parameters j) = (R.rays (σ j), R.parameters (σ j))) ∧
      (∀ a b, a < b → (T.rays a, T.parameters a) = (T.rays b, T.parameters b) → σ a < σ b) ∧
      (R.tower.2.boundaryι ≫ R.iso.hom) ≍ (T.tower.2.boundaryι ≫ T.iso.hom) ∧
      U.HasBoundarySign T ((-1 : ℤˣ) ^ w.inversionCount) ∧
      (∀ (a : Additive (LineBundleClass X[R.fan])) (x : Fin m → ℤ),
        T.picardMarking (Additive.ofMul (LineBundleClass.pullback
          (eqToHom (congrArg Fan.algebraicRealization hfan)) a.toMul), x ∘ σ) =
          R.picardMarking (a, x)) ∧
      ∃ h, U.xEvaluation.compOfDefined (w.xRationalMap ℂ) h = T.xEvaluation := by
  obtain ⟨W, u, q, hq, hcomm, huSign, hu⟩ := exists_word_of_resolved_sarkisov_path p U
  obtain ⟨R, v, hb, href, hm, hvSign, hv⟩ := W.exists_word_reframe T.basis
  obtain ⟨hfan, σ, hmat, href', hσ, horder, hboundary, htSign, hmark, ht⟩ :=
    R.exists_relabel T hb.symm
  let t : Word R.exchangeMatrix T.exchangeMatrix :=
    hmat.symm ▸ ((Generator.permute σ).toStep R.exchangeMatrix).toPath
  refine ⟨W, R, q, (u.comp v).comp t, hfan, σ, hq, hcomm, href, href', hb, hm,
    hσ, horder, hboundary, ?_, hmark, ?_⟩
  · have htCount : t.inversionCount = 0 := by
      dsimp only [t]
      generalize T.exchangeMatrix = E at hmat ⊢
      subst E
      simp
    simpa only [Quiver.Path.inversionCount_comp, pow_add, htCount, pow_zero, mul_one] using
      (huSign.trans hvSign).trans htSign
  · exact U.exists_compOfDefined_word_comp R T (u.comp v) t
      (U.exists_compOfDefined_word_comp W R u v hu hv) ht

end TauCeti.Toric.Fan.LogarithmicProjection

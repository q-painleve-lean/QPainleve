/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Comparison
public import QPainleve.Geometry.Toric.Fan.Picard.Reindex

import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Ramification
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus
import QPainleve.AlgebraicGeometry.Scheme.FunctionField
import QPainleve.Geometry.Toric.Fan.Separated
import QPainleve.Geometry.Toric.Fan.Subdivision.FunctionField

/-!
# Matching the ordered endpoints of a logarithmic factorization

Two ordered internal models of the same log contraction have the same intermediate
fan and the same ordered chains above each original center. The relabeling matches
the total exceptional coordinates in the Picard markings, including for infinitely
near centers. This identifies the last ordered model of a resolved path as in
[Lutz, Theorem 8.4][HKL] with a specified target presentation.

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve.BlowupTower
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry LineBundleClass

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Θ Ω : Fan i} (b : Basis (Fin 2) ℤ N)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" A "]" => Fan.algebraicRealization A
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)

section FixedFan

variable [h₀ : Nonempty Φ.cones]

local notation "D" => Scheme.IdealSheafData.subscheme (Φ.boundaryIdeal h₀)

private theorem center_eq_iff {r s : Φ.Ray} {c d : ℂˣ} {p q : D}
    (hp : IsClosed ({p} : Set D))
    (hr : (r.internalCenter b c).val = ((D).fromSpecResidueField p).ker)
    (hs : (s.internalCenter b d).val = ((D).fromSpecResidueField q).ker) :
    p = q ↔ (r, c) = (s, d) := by
  constructor
  · rintro rfl
    by_contra h
    have hdis := (disjoint_support_map_internalCenter_iff b (𝟙 D) r s c d).mpr h
    simp only [map_id, hr, hs, (D).support_ker_fromSpecResidueField_of_isClosed hp] at hdis
    exact Set.disjoint_left.mp hdis (Set.mem_singleton p) (Set.mem_singleton p)
  · intro h
    apply Scheme.ker_fromSpecResidueField_inj.mp
    exact hr.symm.trans ((congrArg (fun a : Φ.Ray × ℂˣ ↦ (a.1.internalCenter b a.2).val) h)
      |>.trans hs)

private theorem exists_reindex_centers_of_internalBlowupTower_iso (hΦ : Φ.IsRegular)
    {m n : ℕ} (r : Fin m → Φ.Ray) (s : Fin n → Φ.Ray) (c : Fin m → ℂˣ) (d : Fin n → ℂˣ)
    (e : (Φ.internalBlowupTower b r c).1 ≅ (Φ.internalBlowupTower b s d).1)
    (he : e.hom ≫ (Φ.internalBlowupTower b s d).2.toTower.toBase =
      (Φ.internalBlowupTower b r c).2.toTower.toBase) :
    ∃ σ : Fin n ≃ Fin m,
      (∀ j, (s j, d j) = (r (σ j), c (σ j))) ∧
      ∀ a b, a < b → (s a, d a) = (s b, d b) → σ a < σ b := by
  have hCenter (ρ : Φ.Ray) (t : ℂˣ) : ∃ p : D, IsClosed ({p} : Set D) ∧
      (ρ.internalCenter b t).val = ((D).fromSpecResidueField p).ker := by
    rw [Ray.internalCenter_val]
    exact ρ.exists_closedPoint_ker_binomialCenterOnBoundary rankTwo (b.detDualEquiv_self _)
      (ρ.surjective_detCharacter b) t
  choose p hp hJ using fun j ↦ hCenter (r j) (c j)
  choose q hq hK using fun j ↦ hCenter (s j) (d j)
  let : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  revert he e
  rw [internalBlowupTower_eq_alongBoundary, internalBlowupTower_eq_alongBoundary]
  intro e he
  obtain ⟨σ, hσ, horder⟩ := exists_ordered_equiv_of_alongBoundary_iso
    (Φ.boundaryIdeal h₀).subschemeι ℂ hq hp hK hJ e.symm
    ((Iso.inv_comp_eq e).mpr he.symm)
  refine ⟨σ, fun j ↦ ?_, fun a b' hab h ↦ ?_⟩
  · exact ((center_eq_iff b (hq j) (hK j) (hJ (σ j))).mp (hσ j).symm)
  · exact horder a b' hab ((center_eq_iff b (hq a) (hK a) (hK b')).mpr h)

private theorem internalBlowupPicardMarking_pullback_of_reindex (hΦ : Φ.IsRegular)
    {n : ℕ} (r s : Fin n → Φ.Ray) (c d : Fin n → ℂˣ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ j, (s j, d j) = (r (σ j), c (σ j)))
    (horder : ∀ a b, a < b → (s a, d a) = (s b, d b) → σ a < σ b)
    (e : (Φ.internalBlowupTower b r c).1 ≅ (Φ.internalBlowupTower b s d).1)
    (he : e.hom ≫ (Φ.internalBlowupTower b s d).2.toTower.toBase =
      (Φ.internalBlowupTower b r c).2.toTower.toBase)
    (a : Additive (LineBundleClass X[Φ])) (x : Fin n → ℤ) :
    pullback e.hom (Φ.internalBlowupPicardMarking b s d hΦ (a, x ∘ σ)).toMul =
      (Φ.internalBlowupPicardMarking b r c hΦ (a, x)).toMul := by
  have hs : s = r ∘ σ := funext fun j ↦ congrArg Prod.fst (hσ j)
  have hd : d = c ∘ σ := funext fun j ↦ congrArg Prod.snd (hσ j)
  subst s d
  obtain ⟨e', he', -, hmark⟩ := exists_iso_internalBlowupPicardMarking_reindex
    b r c hΦ σ (fun j l hjl hlj h ↦ (not_lt_of_gt hlj) (horder j l hjl h))
  have := Φ.isIntegral_internalBlowupTower b r c hΦ
  have := Φ.isModification_internalBlowupTower_toBase b (r ∘ σ) (c ∘ σ) hΦ
  have h : e.hom = e'.hom := Scheme.Hom.eq_of_comp_eq_of_isModification
    (Φ.internalBlowupTower b (r ∘ σ) (c ∘ σ)).2.toTower.toBase (he.trans he'.symm)
  rw [h]
  exact hmark a x

/-- A specified isomorphism of projections to a regular toric surface determines
a reindexing of the centers that preserves each chain of infinitely near points.
It identifies the strict boundary embeddings. Its Picard pullback permutes the
total exceptional coordinates and fixes the pullback of every toric class. -/
theorem exists_reindex_of_internalBlowupTower_iso (hΦ : Φ.IsRegular)
    {m n : ℕ} (r : Fin m → Φ.Ray) (s : Fin n → Φ.Ray) (c : Fin m → ℂˣ) (d : Fin n → ℂˣ)
    (e : (Φ.internalBlowupTower b r c).1 ≅ (Φ.internalBlowupTower b s d).1)
    (he : e.hom ≫ (Φ.internalBlowupTower b s d).2.toTower.toBase =
      (Φ.internalBlowupTower b r c).2.toTower.toBase) :
    ∃ σ : Fin n ≃ Fin m,
      (∀ j, (s j, d j) = (r (σ j), c (σ j))) ∧
      (∀ a b, a < b → (s a, d a) = (s b, d b) → σ a < σ b) ∧
      (Φ.internalBlowupTower b r c).2.boundaryι ≫ e.hom =
        (Φ.internalBlowupTower b s d).2.boundaryι ∧
      ∀ (a : Additive (LineBundleClass X[Φ])) (x : Fin m → ℤ),
        pullback e.hom (Φ.internalBlowupPicardMarking b s d hΦ (a, x ∘ σ)).toMul =
          (Φ.internalBlowupPicardMarking b r c hΦ (a, x)).toMul := by
  obtain ⟨σ, hσ, horder⟩ := exists_reindex_centers_of_internalBlowupTower_iso b hΦ r s c d e he
  have hboundary : (Φ.internalBlowupTower b r c).2.boundaryι ≫ e.hom =
      (Φ.internalBlowupTower b s d).2.boundaryι := by
    revert he e
    rw [internalBlowupTower_eq_alongBoundary, internalBlowupTower_eq_alongBoundary]
    exact fun e he ↦ boundaryι_comp_of_alongBoundary (Φ.boundaryIdeal h₀).subschemeι e.hom he
  have hnm : n = m := by simpa only [Fintype.card_fin] using Fintype.card_congr σ
  subst n
  exact ⟨σ, hσ, horder, hboundary,
    internalBlowupPicardMarking_pullback_of_reindex b hΦ r s c d σ hσ horder e he⟩

end FixedFan

variable {Z : Scheme} [IsIntegral Z] [IsLocallyNoetherian Z] {P : Z.IdealSheafData}
  {f : Z ⟶ X[Φ]}

/-- Two ordered internal factorizations of a specified regular logarithmic projection
have the same intermediate fan. Their centers differ by a relabeling that preserves
the order above every repeated point. The strict boundary embeddings agree on the
resolving surface, and the relabeling compares the Picard markings there. -/
theorem exists_reindex_of_toric_internal_factorizations (hc : Φ.IsComplete)
    (hΘ : Θ.IsRegular) (hΩ : Ω.IsRegular) (J : Θ.IsSubdivision Φ) (K : Ω.IsSubdivision Φ)
    {m n : ℕ} (r : Fin m → Θ.Ray) (s : Fin n → Ω.Ray) (c : Fin m → ℂˣ) (d : Fin n → ℂˣ) :
    letI := J.nonempty_cones_of_nonempty hc.nonempty_cones
    letI := K.nonempty_cones_of_nonempty hc.nonempty_cones
    let A := Θ.internalBlowupTower b r c
    let B := Ω.internalBlowupTower b s d
    ∀ (e : A.1 ≅ Z) (e' : B.1 ≅ Z),
      e.hom ≫ f = A.2.toTower.toBase ≫ π[J] →
      e'.hom ≫ f = B.2.toTower.toBase ≫ π[K] →
      P.comap e.hom = A.2.boundaryι.ker →
      P.comap e'.hom = B.2.boundaryι.ker →
      ∃ (h : Ω = Θ) (σ : Fin n ≃ Fin m),
        (∀ j, ((h ▸ s) j, d j) = (r (σ j), c (σ j))) ∧
        (∀ a b, a < b → (s a, d a) = (s b, d b) → σ a < σ b) ∧
        (A.2.boundaryι ≫ e.hom) ≍ (B.2.boundaryι ≫ e'.hom) ∧
        ∀ (a : Additive (LineBundleClass X[Θ])) (x : Fin m → ℤ),
          pullback e'.inv (Ω.internalBlowupPicardMarking b s d hΩ
            (Additive.ofMul (pullback (eqToHom (congrArg Fan.algebraicRealization h)) a.toMul),
              x ∘ σ)).toMul =
            pullback e.inv (Θ.internalBlowupPicardMarking b r c hΘ (a, x)).toMul := by
  intro A B e e' he he' hp hp'
  have h := eq_of_toric_internal_factorizations b hc hΘ hΩ J K r s c d e e' he he' hp hp'
  subst Ω
  let g := e ≪≫ e'.symm
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : Nonempty Θ.cones := J.nonempty_cones_of_nonempty hc.nonempty_cones
  have := Θ.isIntegral_internalBlowupTower b r c hΘ
  have := Θ.isModification_internalBlowupTower_toBase b r c hΘ
  have := Θ.isModification_internalBlowupTower_toBase b s d hΘ
  have hg : g.hom ≫ B.2.toTower.toBase = A.2.toTower.toBase := by
    have hcomp : (g.hom ≫ B.2.toTower.toBase) ≫ π[J] = A.2.toTower.toBase ≫ π[J] := by
      rw [Category.assoc, ← he', Iso.trans_hom, Iso.symm_hom, Category.assoc,
        Iso.inv_hom_id_assoc, he]
    apply Scheme.Hom.ext_of_functionFieldMap_eq (⊤_ Scheme)
    apply (cancel_epi (π[J]).functionFieldMap).mp
    simpa only [← Scheme.Hom.functionFieldMap_comp] using
      Scheme.Hom.functionFieldMap_congr hcomp
  obtain ⟨σ, hσ, horder, hb, hmark⟩ := exists_reindex_of_internalBlowupTower_iso b hΘ r s c d g hg
  refine ⟨rfl, σ, hσ, horder, heq_of_eq ?_, fun a x ↦ ?_⟩
  · simpa only [g, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      using congrArg (fun j ↦ j ≫ e'.hom) hb
  · simpa only [g, pullback_comp, Iso.trans_hom, Iso.symm_hom, Iso.inv_hom_id_assoc, eqToHom_refl,
      pullback_id, ofMul_toMul] using congrArg (pullback e.inv) (hmark a x)

end TauCeti.Toric.Fan

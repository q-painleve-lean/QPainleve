/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Comparison
public import QPainleve.Geometry.Toric.Fan.Picard.Reindex

import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Comparison
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Tower

/-!
# Matching ordered models at a logarithmic endpoint

The specified projection and its pole boundary determine the intermediate fan
and the internal centers, with multiplicities. Two ordered models of that
projection differ by a relabeling which preserves the order above each
repeated center. The comparison computes pullback on the entire Picard group
and compares the fixed-center evaluations through the given resolving isomorphisms.

This is the ordered endpoint comparison for a factorization of the kind in
[Lutz, Theorem 8.4](https://arxiv.org/pdf/2005.05010v3#page=68).
-/

public section

open AlgebraicGeometry CategoryTheory Module Multiplicative
open QPainleve.BlowupTower TauCeti.AlgebraicGeometry TauCeti.LaurentRing LineBundleClass
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Θ Ω : Fan i} {m n : ℕ}

local notation "π[" A "]" => toBase (WithBoundary.toTower (Sigma.snd A))
local notation "ι[" A "]" => WithBoundary.boundaryι (Sigma.snd A)
local notation "toric[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)
local notation "χ[" c "," j "]" => (c (ofAdd (Pi.single j 1)))
local notation "rankTwo(" b ")" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)

variable {b : Basis (Fin 2) ℤ N}

section FixedFan

variable [h₀ : Nonempty Θ.cones]

local notation "D" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Θ h₀)

private theorem exists_reindex_of_internalBlowupTower_iso
    (hΘ : Θ.IsRegular) (r : Fin m → Θ.Ray) (s : Fin n → Θ.Ray)
    (c : Fin m → ℂˣ) (d : Fin n → ℂˣ) :
    let A := Θ.internalBlowupTower b r c
    let B := Θ.internalBlowupTower b s d
    ∀ (e : A.1 ≅ B.1), e.hom ≫ π[B] = π[A] →
      ∃ σ : Fin n ≃ Fin m, r ∘ σ = s ∧ c ∘ σ = d ∧
        ∀ j l, j < l → (s j, d j) = (s l, d l) → σ j < σ l := by
  intro A B e he
  let f := Θ.algebraicRealizationStructureMap
  have : SmoothOfRelativeDimension 2 f :=
    rankTwo(b) ▸ Θ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΘ
  have hpoint (a : Θ.Ray × ℂˣ) : ∃ p : D, IsClosed ({p} : Set D) ∧
      (a.1.internalCenter b a.2).val = ((D).fromSpecResidueField p).ker := by
    rw [Ray.internalCenter_val]
    exact a.1.exists_closedPoint_ker_binomialCenterOnBoundary rankTwo(b)
      (b.detDualEquiv_self _) (a.1.surjective_detCharacter b) a.2
  choose p hp hcenter using hpoint
  have hinj : Function.Injective p := by
    intro a a' h
    have hd := Θ.disjoint_support_map_internalCenter_iff b (𝟙 D) a.1 a'.1 a.2 a'.2
    rw [map_id, map_id, hcenter, hcenter, (D).support_ker_fromSpecResidueField_of_isClosed (hp a),
      (D).support_ker_fromSpecResidueField_of_isClosed (hp a'), Set.disjoint_singleton] at hd
    exact not_ne_iff.mp (fun hn ↦ (hd.mpr hn) h)
  let P := fun j ↦ p (r j, c j)
  let Q := fun j ↦ p (s j, d j)
  have hP (j : Fin m) : ((D).fromSpecResidueField (P j)).ker.IsEffectiveCartier :=
    hcenter (r j, c j) ▸ ((r j).internalCenter b (c j)).property
  have hQ (j : Fin n) : ((D).fromSpecResidueField (Q j)).ker.IsEffectiveCartier :=
    hcenter (s j, d j) ▸ ((s j).internalCenter b (d j)).property
  have hA : A = alongBoundary (Θ.boundaryIdeal h₀).subschemeι (fun j ↦ ⟨_, hP j⟩) :=
    (Θ.internalBlowupTower_eq_alongBoundary b r c).trans (congrArg (alongBoundary _)
      (funext fun j ↦ Subtype.ext (hcenter (r j, c j))))
  have hB : B = alongBoundary (Θ.boundaryIdeal h₀).subschemeι (fun j ↦ ⟨_, hQ j⟩) :=
    (Θ.internalBlowupTower_eq_alongBoundary b s d).trans (congrArg (alongBoundary _)
      (funext fun j ↦ Subtype.ext (hcenter (s j, d j))))
  have hcmp := exists_reindex_alongBoundary_of_iso
    (i := (Θ.boundaryIdeal h₀).subschemeι) f Q P
    (fun j ↦ hp (s j, d j)) (fun j ↦ hp (r j, c j)) hQ hP
  rw [← hA, ← hB] at hcmp
  have he' : e.inv ≫ π[A] = π[B] := by rw [← he, Iso.inv_hom_id_assoc]
  obtain ⟨σ, hσ, hord⟩ := hcmp e.symm he'
  have hmatch (j : Fin n) : (r (σ j), c (σ j)) = (s j, d j) := hinj (congrFun hσ j)
  exact ⟨σ, funext fun j ↦ congrArg Prod.fst (hmatch j),
    funext fun j ↦ congrArg Prod.snd (hmatch j),
    fun j l hlt h ↦ hord j l hlt (congrArg p h)⟩

private theorem boundaryι_comp_and_pullback_of_reindex
    (hΘ : Θ.IsRegular) (r : Fin m → Θ.Ray) (s : Fin n → Θ.Ray)
    (c : Fin m → ℂˣ) (d : Fin n → ℂˣ) (σ : Fin n ≃ Fin m)
    (hr : r ∘ σ = s) (hc : c ∘ σ = d)
    (hord : ∀ j l, j < l → (s j, d j) = (s l, d l) → σ j < σ l) :
    let A := Θ.internalBlowupTower b r c
    let B := Θ.internalBlowupTower b s d
    ∀ (e : A.1 ≅ B.1), e.hom ≫ π[B] = π[A] →
      ι[A] ≫ e.hom = ι[B] ∧
      ∀ (a : Additive (LineBundleClass Θ.algebraicRealization)) (x : Fin n → ℤ),
        pullback e.hom (Θ.internalBlowupPicardMarking b s d hΘ (a, x)).toMul =
          (Θ.internalBlowupPicardMarking b r c hΘ (a, x ∘ σ.symm)).toMul := by
  intro A B e he
  have hlen : n = m := by simpa only [Fintype.card_fin] using Fintype.card_congr σ
  subst n
  have horder (j l : Fin m) (hjl : j < l) (hσ : σ l < σ j) :
      (r (σ j), c (σ j)) ≠ (r (σ l), c (σ l)) := by
    have h (j : Fin m) : (r (σ j), c (σ j)) = (s j, d j) :=
      Prod.ext (congrFun hr j) (congrFun hc j)
    rw [h j, h l]
    exact fun hEq ↦ (not_lt_of_gt hσ) (hord j l hjl hEq)
  have hcmp := Θ.exists_iso_internalBlowupPicardMarking_reindex b r c hΘ σ horder
  dsimp only at hcmp
  rw [hr, hc] at hcmp
  obtain ⟨g, hg, hb, hp⟩ := hcmp
  have : IsIntegral A.1 := Θ.isIntegral_internalBlowupTower b r c hΘ
  have : IsModification π[A] := Θ.isModification_internalBlowupTower_toBase b r c hΘ
  have : IsModification π[B] := Θ.isModification_internalBlowupTower_toBase b s d hΘ
  have heq : e.hom = g.hom := π[B].eq_of_comp_eq_of_isModification (he.trans hg.symm)
  refine ⟨heq ▸ hb, fun a x ↦ ?_⟩
  simpa only [heq, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using
    hp a (x ∘ σ.symm)

end FixedFan

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] {P : X.IdealSheafData}
  {f : X ⟶ Φ.algebraicRealization}

/-- Two ordered internal factorizations of the same logarithmic projection with the same pole
boundary have the same intermediate fan. The resolving isomorphisms identify the strict
boundaries, and all toric and exceptional Picard coordinates agree after the induced
reindexing. On the common resolving surface the fixed-center X evaluations differ by the
same renaming. Coincident centers match in the order in which they are blown up. -/
theorem exists_reindex_of_toric_internal_factorizations
    (hc : Φ.IsComplete) (hΦ : Φ.IsRegular) (hΘ : Θ.IsRegular) (hΩ : Ω.IsRegular)
    (J : Θ.IsSubdivision Φ) (K : Ω.IsSubdivision Φ)
    (b : Basis (Fin 2) ℤ N) (r : Fin m → Θ.Ray) (s : Fin n → Ω.Ray)
    (c : Multiplicative (Fin m → ℤ) →* ℂˣ)
    (d : Multiplicative (Fin n → ℤ) →* ℂˣ) :
    let c₀ := fun j ↦ χ[c,j]
    let d₀ := fun j ↦ χ[d,j]
    letI : Nonempty _ := hc.nonempty_cones
    letI : Nonempty _ := J.nonempty_cones_of_nonempty hc.nonempty_cones
    letI : Nonempty _ := K.nonempty_cones_of_nonempty hc.nonempty_cones
    let A := Θ.internalBlowupTower b r c₀
    let B := Ω.internalBlowupTower b s d₀
    ∀ (e : A.1 ≅ X) (e' : B.1 ≅ X), e.hom ≫ f = π[A] ≫ toric[J] →
      e'.hom ≫ f = π[B] ≫ toric[K] → P.comap e.hom = ι[A].ker → P.comap e'.hom = ι[B].ker →
      letI : IsModification π[A] :=
        Θ.isModification_internalBlowupTower_toBase b r c₀ hΘ
      letI : IsModification π[B] :=
        Ω.isModification_internalBlowupTower_toBase b s d₀ hΩ
      ∃ h : Ω = Θ, ∃ σ : Fin n ≃ Fin m,
        (∀ j, (s j).primitiveGenerator = (r (σ j)).primitiveGenerator) ∧ c₀ ∘ σ = d₀ ∧
        (∀ j l, j < l → (s j, d₀ j) = (s l, d₀ l) → σ j < σ l) ∧
        (∃ a : (Θ.boundaryIdeal inferInstance).subscheme ≅
            (Ω.boundaryIdeal inferInstance).subscheme,
          ι[A] ≫ e.hom = a.hom ≫ ι[B] ≫ e'.hom) ∧
        (∀ (a : Additive (LineBundleClass Θ.algebraicRealization)) (x : Fin n → ℤ),
          pullback (e.hom ≫ e'.inv) (Ω.internalBlowupPicardMarking b s d₀ hΩ
            (Additive.ofMul (pullback (eqToHom (congrArg Fan.algebraicRealization h)) a.toMul),
              x)).toMul = (Θ.internalBlowupPicardMarking b r c₀ hΘ (a, x ∘ σ.symm)).toMul) ∧
        (e'.inv ≫ π[B]).toRationalMap.comp (Ω.xEvaluation b s d) =
          ((e.inv ≫ π[A]).toRationalMap.comp (Θ.xEvaluation b r c)).compHom
            (Spec.map (CommRingCat.ofHom (rename (R := ℂ) σ).toRingHom)) := by
  intro c₀ d₀
  let : Nonempty _ := hc.nonempty_cones
  let : Nonempty _ := J.nonempty_cones_of_nonempty hc.nonempty_cones
  let : Nonempty _ := K.nonempty_cones_of_nonempty hc.nonempty_cones
  intro A B e e' he he' hA hB
  have h := eq_of_toric_internal_factorizations b hc hΘ hΩ J K r s c₀ d₀ e e' he he' hA hB
  subst Ω
  let g := e ≪≫ e'.symm
  have : IsIntegral A.1 := Θ.isIntegral_internalBlowupTower b r c₀ hΘ
  have : IsModification π[A] := Θ.isModification_internalBlowupTower_toBase b r c₀ hΘ
  have : IsModification π[B] := Θ.isModification_internalBlowupTower_toBase b s d₀ hΘ
  have : IsModification toric[J] :=
    J.isModification_algebraicMap hΦ hΘ hc.nonempty_cones rankTwo(b)
  have hg : g.hom ≫ π[B] = π[A] := by
    apply (toric[J]).eq_of_comp_eq_of_isModification
    rw [Category.assoc, ← he', Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc, he]
  obtain ⟨σ, hr, hd, hord⟩ := exists_reindex_of_internalBlowupTower_iso (b := b) hΘ r s c₀ d₀ g hg
  obtain ⟨hb, hp⟩ := boundaryι_comp_and_pullback_of_reindex (b := b) hΘ r s c₀ d₀ σ hr hd hord g hg
  refine ⟨rfl, σ, fun j ↦ congrArg Ray.primitiveGenerator (congrFun hr j).symm,
    hd, hord, ⟨Iso.refl _, ?_⟩, ?_, ?_⟩
  · simpa only [g, Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, Category.id_comp,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, A, B] using (reassoc_of% hb) e'.hom
  · simpa only [g, Iso.trans_hom, Iso.symm_hom, eqToHom_refl, pullback_id, ofMul_toMul] using hp
  · have hπ : e'.inv ≫ π[B] = e.inv ≫ π[A] := by
      rw [← hg]
      simp only [g, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    have hdom : IsDominant (FanHom.id Θ).algebraicMap := by
      rw [FanHom.algebraicMap_id]
      infer_instance
    have hev := (FanHom.id Θ).comp_xEvaluation b b r s σ c d
      (fun j ↦ (congrFun hd j).symm) (fun j ↦ by
        have hrj : r (σ j) = s j := congrFun hr j
        rw [hrj, FanHom.id_latticeMap, AddMonoidHom.comp_id])
    have hev' : Θ.xEvaluation b s d =
        (Θ.xEvaluation b r c).compHom
          (Spec.map (CommRingCat.ofHom (rename (R := ℂ) σ).toRingHom)) := by
      simpa only [FanHom.algebraicMap_id, Scheme.Hom.toRationalMap, Scheme.RationalMap.id_comp,
        Scheme.PartialMap.id] using hev
    rw [hev', Scheme.RationalMap.comp_compHom]
    congr 2
    exact congrArg Scheme.Hom.toRationalMap hπ

end TauCeti.Toric.Fan

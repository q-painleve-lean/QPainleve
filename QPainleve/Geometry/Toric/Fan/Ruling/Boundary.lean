/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Ideal
public import QPainleve.Geometry.Toric.Fan.Ruling.Laurent
public import QPainleve.AlgebraicGeometry.Blowup.Projective.Line

import TauCeti.AlgebraicGeometry.IdealSheaf.Locality
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Boundary sections of a toric ruling

Over the base torus of a character ruling, the ray divisors of the two opposite
rays in the kernel of the character are the two coordinate sections of the relative
projective line. This identifies the boundary divisors in the ruling coordinates
used for the elementary transformation of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, §3.1](https://arxiv.org/html/1309.2573v2#S3.SS1).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Module PointedCone AddMonoidAlgebra
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric

variable (K : Type) [CommRing K] [IsDomain K] [IsNoetherianRing K]
  {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

namespace Fan

variable {Φ : Fan i} {m : N →+ ℤ}
  (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
    ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0)
  (b : Basis (Fin 2) ℤ N) (hm : m = (b.coord 1).toAddMonoidHom)
  (hp : hull ℝ {i (b 0)} ∈ Φ.cones) (hn : hull ℝ {-i (b 0)} ∈ Φ.cones)

local notation "U" => Φ.characterRulingTorusSubfan m h
local notation "p" => Φ.isPullback_characterRulingTorusSubfan K m h
local notation "ι" => pullback.fst (Φ.characterRuling K m h) (projectiveLineTorusι K)
local notation "e" => Φ.characterRulingTorusIso K m h b hm hp hn
local notation "eL" => Φ.characterRulingLaurentIso K m h b hm hp hn

private abbrev rulingSectionGenerator (j : Fin 2) : N :=
  if j = 0 then b 0 else -b 0

private abbrev rulingSectionCharacter (j : Fin 2) : N →+ ℤ :=
  if j = 0 then (b.coord 0).toAddMonoidHom else -(b.coord 0).toAddMonoidHom

private theorem rulingSectionCharacter_apply (j : Fin 2) :
    rulingSectionCharacter b j (rulingSectionGenerator b j) = 1 := by
  fin_cases j <;> simp [rulingSectionGenerator, rulingSectionCharacter]

private theorem rulingSectionCharacter_mem (j : Fin 2) (σ : (U).cones)
    (hσ : σ.val = hull ℝ {i (rulingSectionGenerator b j)}) :
    rulingSectionCharacter b j ∈ dualSemigroup (U).lattice σ.val := by
  rw [hσ, ← Set.image_singleton, mem_dualSemigroup_hull_image, Set.forall_mem_singleton,
    rulingSectionCharacter_apply]
  omega

private theorem rulingSectionCharacter_mem_bot (j : Fin 2) (σ : (U).cones)
    (hσ : σ.val = ⊥) : rulingSectionCharacter b j ∈ dualSemigroup (U).lattice σ.val := by
  simp [hσ]

omit [IsDomain K] [IsNoetherianRing K] in
private theorem comap_coordinateSection_on_rulingChart (σ : (U).cones) (j : Fin 2)
    (ha : rulingSectionCharacter b j ∈ dualSemigroup (U).lattice σ.val) :
    (projectiveLine.coordinateSectionCenter (0 : K) j).comap
      ((U).affineChartι K σ ≫ (p).isoPullback.hom ≫ (e).hom ≫ pullback.fst _ _) =
      ofIdealTop ((Ideal.span {single ⟨_, ha⟩ (1 : K)}).map
        (Scheme.ΓSpecIso (.of (affineChartRing K (U).lattice σ.val))).inv.hom) := by
  rw [Φ.affineToricChartι_comp_characterRulingTorusIso_fst K m h b hm hp hn σ j ha]
  exact projectiveLine.comap_coordinateSectionCenter_zero_polynomialPoint j _ _

private theorem comap_rayBoundaryIdeal_rulingChart_self (hΦ : Φ.IsRegular) (ρ : Φ.Ray)
    (j : Fin 2) (hr : ρ.primitiveGenerator = rulingSectionGenerator b j)
    (σ : (U).cones) (hσ : σ.val = hull ℝ {i (rulingSectionGenerator b j)}) :
    (Φ.rayDivisorIdeal K hΦ ρ).comap (Φ.affineChartι K
      ⟨σ.val, ((Φ.mem_characterRulingTorusSubfan_cones_iff m h).mp σ.property).1⟩) =
      (projectiveLine.coordinateSectionCenter (0 : K) j).comap
        ((U).affineChartι K σ ≫ (p).isoPullback.hom ≫ (e).hom ≫ pullback.fst _ _) := by
  let τ : Φ.cones := ⟨σ.val, ((Φ.mem_characterRulingTorusSubfan_cones_iff m h).mp σ.property).1⟩
  have he : ρ.toCone.val = τ.val := (ρ.toCone_eq_hull_primitiveGenerator.trans
    (by rw [hr, hσ]))
  have hle : ρ.toCone ≤ τ := he.le
  let r := ρ.toToricRay Φ τ hle
  have hgen := ρ.primitiveGenerator_toToricRay τ hle
  rw [comap_coordinateSection_on_rulingChart K h b hm hp hn σ j
    (rulingSectionCharacter_mem h b j σ hσ),
    Φ.comap_rayDivisorIdeal_eq_ofIdealTop K hΦ ρ τ hle,
    rayChartIdeal_eq_span_of_apply_eq_one _ _ r K (a := ⟨_, rulingSectionCharacter_mem h b j σ hσ⟩)]
  · rw [hgen, ← ρ.toCone_eq_hull_primitiveGenerator, he]
  · rw [hgen, hr]
    exact rulingSectionCharacter_apply b j

include hm hp hn in
private theorem rulingChart_eq_bot_or_eq_hull (σ : (U).cones) :
    σ.val = ⊥ ∨ ∃ k : Fin 2, σ.val = hull ℝ {i (rulingSectionGenerator b k)} := by
  have hchart := (Φ.mem_characterRulingTorusSubfan_cones_iff_eq_bot_or_opposite_rays
    m h b hm hp hn).mp σ.property
  rcases hchart with hbot | hpos | hneg
  · exact Or.inl hbot
  · exact Or.inr ⟨0, by simpa [rulingSectionGenerator] using hpos⟩
  · exact Or.inr ⟨1, by simpa [rulingSectionGenerator] using hneg⟩

private theorem comap_rayBoundaryIdeal_rulingChart
    (ρ : Φ.Ray) (hΦ : Φ.IsRegular) (j : Fin 2)
    (hr : ρ.primitiveGenerator = if j = 0 then b 0 else -b 0) (σ : (U).cones) :
    (projectiveLine.coordinateSectionCenter (0 : K) j).comap
      ((U).affineChartι K σ ≫ (p).isoPullback.hom ≫ (e).hom ≫ pullback.fst _ _) =
      (Φ.rayDivisorIdeal K hΦ ρ).comap (Φ.affineChartι K
        ⟨σ.val, ((Φ.mem_characterRulingTorusSubfan_cones_iff m h).mp σ.property).1⟩) := by
  rcases rulingChart_eq_bot_or_eq_hull h b hm hp hn σ with hbot | ⟨k, hk⟩
  · rw [comap_coordinateSection_on_rulingChart K h b hm hp hn σ j
      (rulingSectionCharacter_mem_bot h b j σ hbot),
      Φ.comap_rayDivisorIdeal_eq_top K hΦ ρ _]
    · have hu {τ : PointedCone ℝ V} (ht : τ = ⊥) (a : dualSemigroup (U).lattice τ) :
          IsUnit (single a (1 : K)) := by
        subst τ
        exact isUnit_single_bot (R := K) (U).lattice a
      rw [Ideal.span_singleton_eq_top.mpr (hu hbot _), Ideal.map_top,
        ← equivOfIsAffine_symm_apply, TopHomClass.map_top]
    · intro hle
      have hv := hle ρ.primitiveGenerator_mem
      exact ρ.primitiveGenerator_ne_zero (Φ.lattice.injective (by simpa [hbot] using hv))
  · by_cases hkj : k = j
    · subst k
      exact (comap_rayBoundaryIdeal_rulingChart_self K h b hm hp hn hΦ ρ j hr σ hk).symm
    · have hkrev : k = j.rev := by fin_cases k <;> fin_cases j <;> simp_all
      subst k
      rw [Φ.affineToricChartι_comp_characterRulingTorusIso_fst K m h b hm hp hn σ j.rev
        (rulingSectionCharacter_mem h b j.rev σ hk),
        projectiveLine.comap_coordinateSectionCenter_zero_polynomialPoint_rev,
        Φ.comap_rayDivisorIdeal_eq_top K hΦ ρ _]
      refine mt (ρ.primitiveGenerator_eq_of_toCone_le_hull hk ?_) ?_
      · fin_cases j
        · exact (isPrimitive_def.mpr ⟨b.coord 0, by simp⟩ : IsPrimitive (b 0)).neg
        · exact isPrimitive_def.mpr ⟨b.coord 0, by simp [rulingSectionGenerator]⟩
      · have h01 : b 0 ≠ -b 0 := by
          intro he
          have he' := congrArg (b.coord 0) he
          simp at he'
        rw [hr]
        fin_cases j <;> simp_all [rulingSectionGenerator, eq_comm]

/-- Over the base torus, the ray generated by the first basis vector gives the zero
coordinate section and the opposite ray gives the other coordinate section. -/
theorem Ray.comap_coordinateSection_characterRulingTorusIso (ρ : Φ.Ray) (hΦ : Φ.IsRegular)
    (j : Fin 2) (hr : ρ.primitiveGenerator = if j = 0 then b 0 else -b 0) :
    (projectiveLine.coordinateSectionCenter (0 : K) j).comap ((e).hom ≫ pullback.fst _ _) =
      (Φ.rayDivisorIdeal K hΦ ρ).comap ι := by
  let I := ((projectiveLine.coordinateSectionCenter (0 : K) j).comap
    ((e).hom ≫ pullback.fst _ _)).comap (p).isoPullback.hom
  let J := ((Φ.rayDivisorIdeal K hΦ ρ).comap ι).comap (p).isoPullback.hom
  have H (σ : (U).cones) :
      I.comap ((U).affineChartι K σ) = J.comap ((U).affineChartι K σ) := by
    dsimp only [I, J]
    rw [← comap_comp, ← comap_comp, ← comap_comp, ← comap_comp]
    rw [Category.assoc ((U).affineChartι K σ) (p).isoPullback.hom ι,
      (p).isoPullback_hom_fst,
      Φ.affineToricChartι_comp_characterRulingTorusSubfanInclusion K]
    exact comap_rayBoundaryIdeal_rulingChart K h b hm hp hn ρ hΦ j hr σ
  have he := ext_of_comap_openCover ((U).affineChartOpenCover K) (I := I) (J := J) (fun σ ↦ by
    let cone : (U).cones := σ
    exact H cone)
  have he' := congrArg (fun D ↦ comap D (p).isoPullback.inv) he
  simpa only [I, J, ← comap_comp, Iso.inv_hom_id_assoc] using he'

/-- The two ray divisors over the base torus are the relative coordinate sections
in the Laurent-polynomial model of the ruling. -/
theorem Ray.comap_coordinateSection_characterRulingLaurentIso (ρ : Φ.Ray)
    (hΦ : Φ.IsRegular) (j : Fin 2)
    (hr : ρ.primitiveGenerator = if j = 0 then b 0 else -b 0) :
    (projectiveLine.coordinateSectionCenter (0 : LaurentPolynomial K) j).comap (eL).hom =
      (Φ.rayDivisorIdeal K hΦ ρ).comap ι := by
  rw [← projectiveLine.comap_coordinateSectionCenter_zero_baseChangeProjection (R := K),
    ← comap_comp, Φ.characterRulingLaurentIso_hom_comp_baseChangeProjection K]
  exact ρ.comap_coordinateSection_characterRulingTorusIso K h b hm hp hn hΦ j hr

include hm hp hn in
/-- On either horizontal ray, a morphism over the base torus is determined by its
projection to that torus. The kernel conditions express factorization through the
same reduced ray divisor. -/
theorem Ray.eq_of_characterRuling_eq_of_le_ker (ρ : Φ.Ray) (hΦ : Φ.IsRegular)
    (j : Fin 2) (hρ : ρ.primitiveGenerator = if j = 0 then b 0 else -b 0)
    {W : Scheme} {f g : W ⟶ (Φ.finiteFanScheme K)}
    (hf : Φ.rayDivisorIdeal K hΦ ρ ≤ f.ker) (hg : Φ.rayDivisorIdeal K hΦ ρ ≤ g.ker)
    (t : W ⟶ projectiveLineTorusFan.finiteFanScheme K)
    (htf : f ≫ Φ.characterRuling K m h = t ≫ (projectiveLineTorusι K))
    (htg : g ≫ Φ.characterRuling K m h = t ≫ (projectiveLineTorusι K)) : f = g := by
  let z := projectiveLine.polynomialPoint (LaurentPolynomial K) (RingHom.id _) j 0
  let q := projectiveLine (LaurentPolynomial K) ↘ Spec (.of (LaurentPolynomial K))
  have : IsClosedImmersion z := projectiveLine.isClosedImmersion_coordinateSection j
  have hz : z ≫ q = 𝟙 _ := by simp [z, q, projectiveLine.polynomialPoint_over]
  let lift (a : W ⟶ (Φ.finiteFanScheme K))
      (ha : a ≫ Φ.characterRuling K m h = t ≫ (projectiveLineTorusι K)) :=
    pullback.lift a t ha
  have hsection (a : W ⟶ (Φ.finiteFanScheme K)) (ha₀ : Φ.rayDivisorIdeal K hΦ ρ ≤ a.ker)
      (ha : a ≫ Φ.characterRuling K m h = t ≫ (projectiveLineTorusι K)) :
      lift a ha ≫ (eL).hom = t ≫ (projectiveLineTorusIsoSpecLaurent K).hom ≫ z := by
    have hfst : lift a ha ≫ ι = a := pullback.lift_fst _ _ _
    have hker : z.ker ≤ (lift a ha ≫ (eL).hom).ker := by
      rw [← Scheme.IdealSheafData.map_bot (lift a ha ≫ (eL).hom),
        le_map_iff_comap_le, comap_comp,
        projectiveLine.ker_coordinateSection,
        ρ.comap_coordinateSection_characterRulingLaurentIso K h b hm hp hn hΦ j hρ,
        ← comap_comp, hfst, ← le_map_iff_comap_le,
        Scheme.IdealSheafData.map_bot]
      exact ha₀
    let s := IsClosedImmersion.lift z (lift a ha ≫ (eL).hom) hker
    have hs : s ≫ z = lift a ha ≫ (eL).hom := IsClosedImmersion.lift_fac _ _ _
    have hsq := congrArg (· ≫ q) hs
    have hq : (eL).hom ≫ q = pullback.snd _ _ ≫ (projectiveLineTorusIsoSpecLaurent K).hom :=
      Φ.characterRulingLaurentIso_hom_comp_toBase K m h b hm hp hn
    simp only [Category.assoc, hz, Category.comp_id, hq, lift, pullback.lift_snd_assoc] at hsq
    rw [← hs, hsq, Category.assoc]
  have hfg : lift f htf = lift g htg :=
    (cancel_mono (eL).hom).mp ((hsection f hf htf).trans (hsection g hg htg).symm)
  simpa only [lift, pullback.lift_fst] using congrArg (· ≫ ι) hfg

include hm hp hn in
private theorem ray_eq_of_rayBoundaryPoint_mem_rulingTorus (hΦ : Φ.IsRegular)
    (s : Fin 2 → Φ.Ray) (hs : ∀ j, (s j).primitiveGenerator = rulingSectionGenerator b j)
    (ρ : Φ.Ray) (hx : (Φ.rayBoundaryChartPoint (R := K) hΦ ρ).val ∈ Set.range ι) :
    ∃ j, ρ = s j := by
  obtain ⟨x, hx⟩ := hx
  obtain ⟨σ, y, hy⟩ := (U).exists_affineChartι_apply_eq K ((p).isoPullback.inv x)
  let α : Φ.cones := ⟨σ.val, ((Φ.mem_characterRulingTorusSubfan_cones_iff m h).mp σ.property).1⟩
  have he : (U).affineChartι K σ ≫ (p).isoPullback.hom ≫ ι = Φ.affineChartι K α := by
    rw [(p).isoPullback_hom_fst, Φ.affineToricChartι_comp_characterRulingTorusSubfanInclusion K]
  have hy' := congrArg (fun f : affineChart K (U).lattice σ ⟶ (Φ.finiteFanScheme K) ↦ f y) he
  have hinv : (p).isoPullback.hom ((p).isoPullback.inv x) = x := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  simp only [Scheme.Hom.comp_apply, hy, hinv, hx] at hy'
  have hle := (Φ.rayBoundaryChartPoint_mem_range_affineChartι_iff (R := K) hΦ ρ α).mp ⟨y, hy'.symm⟩
  rcases rulingChart_eq_bot_or_eq_hull h b hm hp hn σ with hz | ⟨j, hj⟩
  · have hv := (ρ.toCone_le_iff α).mp hle
    exact (ρ.primitiveGenerator_ne_zero (Φ.lattice.injective (by simpa [α, hz] using hv))).elim
  · refine ⟨j, Ray.primitiveGenerator_injective ?_⟩
    by_contra! hne
    exact hne ((ρ.primitiveGenerator_eq_of_toCone_le_hull hj
      (hs j ▸ (s j).isPrimitiveGenerator.isPrimitive) hle).trans (hs j).symm)

/-- Over the base torus, the reduced toric boundary is the union of the two horizontal
ray divisors, expressed in Laurent coordinates as the union of the two coordinate sections. -/
theorem comap_boundaryIdeal_characterRulingLaurentIso (hΦ : Φ.IsRegular) :
    (Φ.toricBoundaryIdeal K ⟨⟨_, hp⟩⟩).comap ι =
      (projectiveLine.coordinateSectionCenter (0 : LaurentPolynomial K) 0 ⊓
        projectiveLine.coordinateSectionCenter 0 1).comap (eL).hom := by
  have hb : IsPrimitive (b 0) := isPrimitive_def.mpr ⟨b.coord 0, by simp⟩
  have hn' : hull ℝ {i (-b 0)} ∈ Φ.cones := by simpa only [map_neg] using hn
  let s (j : Fin 2) := if j = 0 then Ray.ofPrimitiveGenerator hb hp
    else Ray.ofPrimitiveGenerator hb.neg hn'
  have hs (j : Fin 2) : (s j).primitiveGenerator = rulingSectionGenerator b j := by
    by_cases hj : j = 0 <;> simp [s, rulingSectionGenerator, hj]
  let B := Φ.toricBoundaryIdeal K ⟨⟨_, hp⟩⟩
  let R (j : Fin 2) := Φ.rayDivisorIdeal K hΦ (s j)
  have hsupport : (B.comap ι).support = (R 0 |>.comap ι).support ⊔ (R 1 |>.comap ι).support := by
    apply SetLike.coe_injective
    simp only [support_comap, TopologicalSpace.Closeds.coe_preimage,
      TopologicalSpace.Closeds.coe_sup, B, R, Φ.support_toricBoundaryIdeal_eq_iUnion_closure K hΦ,
      Φ.coe_support_rayDivisorIdeal K]
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨ρ, hρ⟩
      have hx := (specializes_iff_mem_closure.mpr hρ).mem_open
        (ι).isOpenEmbedding.isOpen_range (Set.mem_range_self x)
      obtain ⟨j, rfl⟩ := ray_eq_of_rayBoundaryPoint_mem_rulingTorus K h b hm hp hn hΦ s hs ρ hx
      fin_cases j
      · exact Or.inl hρ
      · exact Or.inr hρ
    · rintro (h₀ | h₁)
      · exact ⟨s 0, h₀⟩
      · exact ⟨s 1, h₁⟩
  let D (j : Fin 2) := projectiveLine.coordinateSectionCenter (0 : LaurentPolynomial K) j
  have hD (j : Fin 2) : (D j).comap (eL).hom = (R j).comap ι :=
    (s j).comap_coordinateSection_characterRulingLaurentIso K h b hm hp hn hΦ j (hs j)
  have hv (I : (Φ.finiteFanScheme K).IdealSheafData) [IsReduced I.subscheme] :
      vanishingIdeal (I.comap ι).support = I.comap ι := by
    rw [vanishingIdeal_support, radical_comap_of_isOpenImmersion,
      I.isReduced_subscheme_iff_radical_eq.mp inferInstance]
  have hred : IsReduced B.subscheme := by
    dsimp only [B]
    infer_instance
  rw [← hv B, hsupport, vanishingIdeal_sup, hv (R 0), hv (R 1), comap_inf_of_isIso]
  exact congrArg₂ (· ⊓ ·) (hD 0).symm (hD 1).symm

end Fan
end TauCeti.Toric

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Projective.Line
public import TauCeti.AlgebraicGeometry.Blowup.Pullback

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Basic
import QPainleve.AlgebraicGeometry.Blowup.Projective.Divisors
import TauCeti.Algebra.Regular.SMul
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Section
import TauCeti.Data.Fin.Rev

/-!
# Strict transforms of the coordinate sections of a projective line

Blowing up a base divisor on one coordinate section of a projective line lifts both
coordinate sections. The elementary transformation identifies their strict transforms
with the same section indices on the other blowup. This is the section comparison in
Gross, Hacking and Keel, [*Birational geometry of cluster algebras*][GHK], §3.1.

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory Polynomial
open Scheme.IdealSheafData

namespace TauCeti.AlgebraicGeometry.projectiveLine

universe u

variable {R : Type u} [CommRing R] (f : R) (i : Fin 2)

local notation "S" => Spec (CommRingCat.of R)
local notation "P" => projectiveLine R
local notation "Z(" j ")" => coordinateSectionCenter f j
local notation "D(" j ")" => coordinateSectionCenter (0 : R) j
local notation "s(" j ")" => polynomialPoint R (RingHom.id R) j (0 : R)
local notation "π(" j ")" => IdealSheafData.blowupToBase (Z(j))
local notation "z" => Spec.map (CommRingCat.ofHom (eval₂RingHom (RingHom.id R) (0 : R)))

private theorem ker_coordinateSection (j : Fin 2) : (s(j)).ker = D(j) := by
  symm
  apply coordinateSectionCenter_eq_ker_polynomialPoint_of_surjective
  · exact Function.surjective_id
  · rw [Ideal.span_singleton_zero]
    exact (RingHom.injective_iff_ker_eq_bot (RingHom.id R)).mp Function.injective_id

private theorem isClosedImmersion_coordinateSection (j : Fin 2) : IsClosedImmersion (s(j)) :=
  (s(j)).isClosedImmersion_of_comp_eq_id (f := P ↘ S) (by simp [polynomialPoint_over])

private theorem coordinateSectionCenter_comap_own_section :
    (Z(i)).comap (s(i)) =
      IdealSheafData.ofIdealTop ((Ideal.span {f}).map (Scheme.ΓSpecIso (.of R)).inv.hom) := by
  rw [polynomialPoint_def, comap_comp, coordinateSectionCenter_comap_polynomialChartι,
    IdealSheafData.comap_ofIdealTop_map_ΓSpecIso_inv, Ideal.map_span, Set.image_insert_eq,
    Set.image_singleton, CommRingCat.hom_ofHom, coe_eval₂RingHom, eval₂_X, eval₂_C,
    RingHom.id_apply, Set.pair_comm, Ideal.span_pair_zero]

private theorem coordinateSectionCenter_comap_opposite_section :
    (Z(i)).comap (s(i.rev)) = ⊤ := by
  rw [polynomialPoint_def, comap_comp, coordinateSectionCenter_comap_polynomialChartι_rev,
    comap_top]

private theorem ker_lift_coordinateSection (j : Fin 2)
    (h : ((Z(i)).comap (s(j))).IsEffectiveCartier) {q : S ⟶ (Z(i)).blowup}
    (hq : q ≫ π(i) = s(j)) :
    q.ker = ((Z(i)).blowupMap (D(j)).subschemeι).ker := by
  have := isClosedImmersion_coordinateSection (R := R) j
  rw [(Z(i)).eq_blowupLift h hq, ker_blowupLift, ← ker_blowupMap,
    ker_blowupMap_eq_ker_blowupMap_subschemeι, ker_coordinateSection]

/-- The blowup center is Cartier on each coordinate section. On its own section it cuts out
`f = 0`, and on the opposite one it cuts out the empty subscheme. -/
theorem isEffectiveCartier_comap_coordinateSectionCenter (hf : IsSMulRegular R f) (j : Fin 2) :
    ((Z(i)).comap (s(j))).IsEffectiveCartier := by
  rcases Fin.fin_two_eq_or_eq_rev i j with rfl | rfl
  · rw [coordinateSectionCenter_comap_own_section, Ideal.map_span, Set.image_singleton]
    have h := Scheme.Hom.isEffectiveCartier_ofIdealTop_span_appTop (𝟙 S)
      ((isSMulRegular_map_iff (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv f).mpr hf)
    rwa [Scheme.Hom.id_appTop] at h
  · rw [coordinateSectionCenter_comap_opposite_section]
    exact isEffectiveCartier_top _

/-- The lift of coordinate section `j` to the blowup at the center on section `i`.
It embeds the base scheme as the scheme-theoretic strict transform of that section. -/
def coordinateSectionStrictTransformι (hf : IsSMulRegular R f) (j : Fin 2) :
    S ⟶ (Z(i)).blowup :=
  (Z(i)).blowupLift (s(j)) (isEffectiveCartier_comap_coordinateSectionCenter f i hf j)

/-- The lifted section projects to the zero point on its original coordinate chart. -/
@[reassoc (attr := simp)]
theorem coordinateSectionStrictTransformι_blowupToBase (hf : IsSMulRegular R f) (j : Fin 2) :
    coordinateSectionStrictTransformι f i hf j ≫ π(i) = s(j) :=
  (Z(i)).blowupLift_blowupToBase _ _

instance isClosedImmersion_coordinateSectionStrictTransformι
    (hf : IsSMulRegular R f) (j : Fin 2) :
    IsClosedImmersion (coordinateSectionStrictTransformι f i hf j) := by
  have := isClosedImmersion_coordinateSection (R := R) j
  exact (Z(i)).isClosedImmersion_blowupLift (s(j))
    (isEffectiveCartier_comap_coordinateSectionCenter f i hf j)

/-- The ideal of the lifted section is the ideal of its native strict transform. -/
@[simp]
theorem ker_coordinateSectionStrictTransformι (hf : IsSMulRegular R f) (j : Fin 2) :
    (coordinateSectionStrictTransformι f i hf j).ker =
      ((Z(i)).blowupMap (D(j)).subschemeι).ker := by
  exact ker_lift_coordinateSection f i j (isEffectiveCartier_comap_coordinateSectionCenter f i hf j)
    (coordinateSectionStrictTransformι_blowupToBase f i hf j)

/-- The strict transform of the section containing the center is the zero section in
the chart with coordinate `X/f`. -/
theorem coordinateSectionStrictTransformι_self (hf : IsSMulRegular R f) :
    coordinateSectionStrictTransformι f i hf i = z ≫ sectionBlowupDivisorChartι f i hf := by
  symm
  apply (Z(i)).eq_blowupLift
  rw [Category.assoc, sectionBlowupDivisorChartι_blowupToBase, SpecMap_polynomialPoint]
  have h : (eval₂RingHom (RingHom.id R) 0).comp C = RingHom.id R := by ext r; simp
  simp [h, coe_eval₂RingHom]

/-- The opposite coordinate section lifts along the unchanged polynomial chart. -/
theorem coordinateSectionStrictTransformι_rev (hf : IsSMulRegular R f) :
    coordinateSectionStrictTransformι f i hf i.rev = z ≫ sectionBlowupOppositeChartι f i := by
  symm
  apply (Z(i)).eq_blowupLift
  rw [Category.assoc, sectionBlowupOppositeChartι_blowupToBase, polynomialPoint_def]

/-- The strict transform of the opposite section is its full inverse image. -/
theorem comap_coordinateSectionCenter_zero_rev_eq_strictTransform :
    (D(i.rev)).comap π(i) = ((Z(i)).blowupMap (D(i.rev)).subschemeι).ker := by
  let a := polynomialChartι R i.rev
  let b := sectionBlowupOppositeChartι f i
  have hchart : IsPullback b (𝟙 _) π(i) a :=
    (IsOpenImmersion.isPullback (𝟙 _) b a π(i)
      (by simp [a, b, sectionBlowupOppositeChartι_blowupToBase])
      (opensRange_sectionBlowupOppositeChartι f i).symm).flip
  have hz : IsPullback z (𝟙 S) (𝟙 _) z := .of_vert_isIso ⟨by simp⟩
  have hs : IsPullback (z ≫ b) (𝟙 S) π(i) (s(i.rev)) := by
    rw [polynomialPoint_def]
    simpa only [a, b] using hz.paste_horiz hchart
  have h : ((Z(i)).comap (s(i.rev))).IsEffectiveCartier := by
    rw [coordinateSectionCenter_comap_opposite_section]
    exact isEffectiveCartier_top _
  have := isClosedImmersion_coordinateSection (R := R) i.rev
  rw [← ker_coordinateSection i.rev, ← ker_eq_comap_of_isPullback _ hs,
    ker_lift_coordinateSection f i i.rev h (by simpa only [Category.id_comp] using hs.w),
    ker_coordinateSection]

section Domain

variable [IsDomain R] (hf : f ≠ 0)

local notation "hr" => IsLeftRegular.isSMulRegular (IsRegular.left (IsRegular.of_ne_zero hf))
local notation "e" => elementaryTransform f i hf

/-- The elementary transformation sends each lifted coordinate section to the
lift of the same section on the other blowup, as a morphism from the base. -/
@[reassoc (attr := simp)]
theorem coordinateSectionStrictTransformι_comp_elementaryTransform_hom (j : Fin 2) :
    coordinateSectionStrictTransformι f i hr j ≫ (e).hom =
      coordinateSectionStrictTransformι f i.rev hr j := by
  rcases Fin.fin_two_eq_or_eq_rev i j with hj | hj
  · subst j
    rw [coordinateSectionStrictTransformι_self, Category.assoc,
      sectionBlowupDivisorChartι_elementaryTransform_hom]
    simpa only [Fin.rev_rev] using (coordinateSectionStrictTransformι_rev f i.rev hr).symm
  · subst j
    rw [coordinateSectionStrictTransformι_rev, Category.assoc,
      sectionBlowupOppositeChartι_elementaryTransform_hom, coordinateSectionStrictTransformι_self]

/-- The elementary transformation identifies the scheme-theoretic strict transform
ideals of both coordinate sections. -/
@[simp]
theorem comap_ker_blowupMap_coordinateSectionCenter_elementaryTransform (j : Fin 2) :
    (((Z(i.rev)).blowupMap (D(j)).subschemeι).ker).comap (e).hom =
      ((Z(i)).blowupMap (D(j)).subschemeι).ker := by
  let s₀ := coordinateSectionStrictTransformι f i hr j
  let s₁ := coordinateSectionStrictTransformι f i.rev hr j
  have hc : s₀ ≫ (e).hom = s₁ :=
    coordinateSectionStrictTransformι_comp_elementaryTransform_hom f i hf j
  have hk := Scheme.Hom.comap_ker_comp_of_isClosedImmersion s₀ (e).hom
  rw [hc] at hk
  rw [← ker_coordinateSectionStrictTransformι f i.rev hr j,
    ← ker_coordinateSectionStrictTransformι f i hr j]
  exact hk

include hf in
/-- The total transform of the section containing the center is the product of its strict
transform ideal and one copy of the exceptional ideal. -/
theorem comap_coordinateSectionCenter_zero_eq_strictTransform_mul_exceptional :
    (D(i)).comap π(i) =
      ((Z(i)).blowupMap (D(i)).subschemeι).ker * (Z(i)).comap π(i) := by
  have h := comap_coordinateSectionCenter_zero_rev_eq_strictTransform f i.rev
  rw [Fin.rev_rev] at h
  rw [comap_coordinateSectionCenter_elementaryTransform f i hf, comap_comp, h,
    comap_ker_blowupMap_coordinateSectionCenter_elementaryTransform]

end Domain

end TauCeti.AlgebraicGeometry.projectiveLine

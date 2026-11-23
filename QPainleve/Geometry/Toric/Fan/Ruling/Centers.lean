/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Projective.Line
public import QPainleve.Geometry.Toric.Fan.Boundary.Ruling
public import QPainleve.Geometry.Toric.Fan.Ruling.Laurent

import QPainleve.Algebra.Polynomial.Laurent
import QPainleve.AlgebraicGeometry.Blowup.Isomorphism
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Binomial centers in ruling product coordinates

In the projective-line product above the torus of a character ruling, a binomial center
on either pivot ray lies on the corresponding coordinate section. The base coordinate
is the root of the boundary binomial. This identifies the blowup centers of the
elementary transformation in Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, §3.1][GHK].

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory LaurentPolynomial Limits Module Multiplicative PointedCone
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} {m : N →+ ℤ}
  (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
    ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0)

local notation "U" => Φ.characterRulingTorusSubfan m h
local notation "p" => Φ.isPullback_characterRulingTorusSubfan m h
local notation "base" => Spec (CommRingCat.of ℂ)

variable (b : Basis (Fin 2) ℤ N) (hm : m = (b.coord 1).toAddMonoidHom)
  (hpos : hull ℝ {i (b 0)} ∈ Φ.cones) (hneg : hull ℝ {-i (b 0)} ∈ Φ.cones)

local notation "e" => Φ.characterRulingTorusIso m h b hm hpos hneg

private theorem binomialCenter_firstCoordinate {ρ : Φ.Ray}
    (hσ : ρ.toCone.val ∈ (U).cones) (j : Fin 2)
    (hρ : ρ.primitiveGenerator = if j = 0 then b 0 else -b 0)
    (hdim : Module.finrank ℤ N = 2) (hmρ : m ρ.primitiveGenerator = 0)
    (hsurj : Function.Surjective m) (c : ℂˣ) :
    Spec.map (CommRingCat.ofHom (ρ.binomialCenterEval hdim hmρ hsurj c).toRingHom) ≫
        (U).affineToricChartι ⟨ρ.toCone.val, hσ⟩ ≫ (p).isoPullback.hom ≫
          (e).hom ≫ pullback.fst _ _ =
      projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) j 0 := by
  let a : N →+ ℤ := if j = 0 then (b.coord 0).toAddMonoidHom else -(b.coord 0).toAddMonoidHom
  have ha : a ρ.primitiveGenerator = 1 := by
    rw [hρ]
    by_cases hj : j = 0 <;> simp [a, hj]
  have haσ : a ∈ dualSemigroup (U).lattice ρ.toCone.val := by
    rw [ρ.toCone_eq_hull_primitiveGenerator, ← Set.image_singleton,
      mem_dualSemigroup_hull_image, Set.forall_mem_singleton, ha]
    omega
  let ev := ρ.binomialCenterEval hdim hmρ hsurj c
  rw [Φ.affineToricChartι_comp_characterRulingTorusIso_fst m h b hm hpos hneg
    ⟨ρ.toCone.val, hσ⟩ j haσ, projectiveLine.SpecMap_polynomialPoint]
  refine congrArg₂ (fun k a ↦ projectiveLine.polynomialPoint ℂ k j a) ?_ ?_
  · apply RingHom.ext
    intro r
    exact ev.commutes r
  · exact ρ.binomialCenterEval_monomial_of_pos hdim hmρ hsurj c _ (ha.symm ▸ Int.zero_lt_one)

/-- The binomial center regarded as a point of the ruling's restriction above the base torus. -/
def Ray.binomialCenterInRulingTorus (ρ : Φ.Ray)
    (hdim : Module.finrank ℤ N = 2) (hmρ : m ρ.primitiveGenerator = 0)
    (hsurj : Function.Surjective m) (c : ℂˣ) :
    base ⟶ pullback (Φ.characterRuling m h) projectiveLineTorusι :=
  pullback.lift (ρ.binomialCenter hdim hmρ hsurj c)
    (projectiveLineTorusPoint ((-1 : ℂˣ) * c⁻¹)) (by
      rw [ρ.binomialCenter_comp_characterRuling h hdim hmρ hsurj c,
        projectiveLineTorusPoint_comp_projectiveLineTorusι]
      simp)

/-- The ambient projection recovers the original binomial center. -/
@[reassoc (attr := simp)]
theorem Ray.binomialCenterInRulingTorus_fst (ρ : Φ.Ray)
    (hdim : Module.finrank ℤ N = 2) (hmρ : m ρ.primitiveGenerator = 0)
    (hsurj : Function.Surjective m) (c : ℂˣ) :
    ρ.binomialCenterInRulingTorus h hdim hmρ hsurj c ≫ pullback.fst _ _ =
      ρ.binomialCenter hdim hmρ hsurj c :=
  pullback.lift_fst _ _ _

/-- The ruling projection is the torus point at the root of the binomial. -/
@[reassoc (attr := simp)]
theorem Ray.binomialCenterInRulingTorus_snd (ρ : Φ.Ray)
    (hdim : Module.finrank ℤ N = 2) (hmρ : m ρ.primitiveGenerator = 0)
    (hsurj : Function.Surjective m) (c : ℂˣ) :
    ρ.binomialCenterInRulingTorus h hdim hmρ hsurj c ≫ pullback.snd _ _ =
      projectiveLineTorusPoint ((-1 : ℂˣ) * c⁻¹) :=
  pullback.lift_snd _ _ _

/-- In the ruling product, the center on the ray of `b 0` is on the zero coordinate section,
and the center on the ray of `-b 0` is on the opposite coordinate section. -/
@[reassoc]
theorem Ray.binomialCenterInRulingTorus_comp_characterRulingTorusIso_fst (ρ : Φ.Ray)
    (j : Fin 2) (hρ : ρ.primitiveGenerator = if j = 0 then b 0 else -b 0)
    (hdim : Module.finrank ℤ N = 2) (hmρ : m ρ.primitiveGenerator = 0)
    (hsurj : Function.Surjective m) (c : ℂˣ) :
    ρ.binomialCenterInRulingTorus h hdim hmρ hsurj c ≫ (e).hom ≫ pullback.fst _ _ =
      projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) j 0 := by
  have hσ : ρ.toCone.val ∈ (U).cones := by
    apply (Φ.mem_characterRulingTorusSubfan_cones_iff m h).2
    refine ⟨ρ.toCone.property, ?_⟩
    rw [ρ.toCone_eq_hull_primitiveGenerator]
    intro x hx
    obtain ⟨r, -, rfl⟩ := mem_hull_singleton.mp hx
    rw [map_smul, IsIntegralLattice.realCharacter_apply, hmρ, Int.cast_zero, smul_zero]
  let σ : (U).cones := ⟨ρ.toCone.val, hσ⟩
  let t : base ⟶ (U).algebraicRealization :=
    Spec.map (CommRingCat.ofHom (ρ.binomialCenterEval hdim hmρ hsurj c).toRingHom) ≫
      (U).affineToricChartι σ
  have ht : t ≫ (p).isoPullback.hom = ρ.binomialCenterInRulingTorus h hdim hmρ hsurj c := by
    apply (cancel_mono (pullback.fst (Φ.characterRuling m h) projectiveLineTorusι)).mp
    rw [Category.assoc, (p).isoPullback_hom_fst, Ray.binomialCenterInRulingTorus_fst,
      Ray.binomialCenter_def]
    simp only [t, Category.assoc, Φ.affineToricChartι_comp_characterRulingTorusSubfanInclusion]
    rfl
  rw [← ht, Category.assoc]
  simpa only [t, Category.assoc] using
    binomialCenter_firstCoordinate h b hm hpos hneg hσ j hρ hdim hmρ hsurj c

local notation "L" => LaurentPolynomial ℂ
local notation "eL" => Φ.characterRulingLaurentIso m h b hm hpos hneg
local notation "root" => fun (c : ℂˣ) ↦ (-1 : ℂˣ) * c⁻¹
local notation "center[" j ", " c "]" =>
  projectiveLine.coordinateSectionCenter (1 + C (c : ℂ) * T 1 : L) j
local notation "ι" => pullback.fst (Φ.characterRuling m h) projectiveLineTorusι

/-- In Laurent product coordinates the entire binomial point is specified by the zero
coordinate on its section and by evaluation at the root of the boundary binomial. -/
theorem Ray.binomialCenterInRulingTorus_comp_characterRulingLaurentIso (ρ : Φ.Ray)
    (j : Fin 2) (hρ : ρ.primitiveGenerator = if j = 0 then b 0 else -b 0)
    (hdim : Module.finrank ℤ N = 2) (hmρ : m ρ.primitiveGenerator = 0)
    (hsurj : Function.Surjective m) (c : ℂˣ) :
    ρ.binomialCenterInRulingTorus h hdim hmρ hsurj c ≫ (eL).hom =
      projectiveLine.polynomialPoint L (laurentEval (root c)).toRingHom j 0 := by
  let ev : L →ₐ[ℂ] ℂ := laurentEval (root c)
  apply (projectiveLine.isPullback_baseChangeProjection ℂ L).hom_ext
  · have he : ev.toRingHom.comp (algebraMap ℂ L) = RingHom.id ℂ := by
      apply RingHom.ext
      intro a
      exact ev.commutes a
    rw [Category.assoc, Φ.characterRulingLaurentIso_hom_comp_baseChangeProjection,
      ρ.binomialCenterInRulingTorus_comp_characterRulingTorusIso_fst h b hm hpos hneg j hρ,
      projectiveLine.polynomialPoint_comp_baseChangeProjection, he]
  · simp only [Category.assoc, Φ.characterRulingLaurentIso_hom_comp_toBase,
      ρ.binomialCenterInRulingTorus_snd_assoc,
      projectiveLineTorusPoint_comp_projectiveLineTorusIsoSpecLaurent,
      projectiveLine.polynomialPoint_over]

/-- The native center ideal for the elementary transformation pulls back to the restriction
of the actual toric binomial center ideal. This identifies the closed subschemes. -/
theorem Ray.comap_coordinateSectionCenter_characterRulingLaurentIso (ρ : Φ.Ray)
    (j : Fin 2) (hρ : ρ.primitiveGenerator = if j = 0 then b 0 else -b 0)
    (hdim : Module.finrank ℤ N = 2) (hmρ : m ρ.primitiveGenerator = 0)
    (hsurj : Function.Surjective m) (c : ℂˣ) :
    (center[j, c]).comap (eL).hom = (ρ.binomialCenter hdim hmρ hsurj c).ker.comap (ι) := by
  let ev : L →ₐ[ℂ] ℂ := laurentEval (root c)
  have hsurjEv : Function.Surjective ev.toRingHom :=
    fun a ↦ ⟨C a, ev.apply_laurentPolynomial_C_self a⟩
  rw [projectiveLine.coordinateSectionCenter_eq_ker_polynomialPoint_of_surjective _ _
      ev.toRingHom hsurjEv (ker_laurentEval_neg_inv c),
    ← ρ.binomialCenterInRulingTorus_comp_characterRulingLaurentIso h b hm hpos hneg
      j hρ hdim hmρ hsurj c, Scheme.Hom.comap_ker_comp_of_isClosedImmersion]
  apply ker_eq_comap_of_isPullback
  exact IsPullback.of_vert_isIso_mono (snd := 𝟙 base) ⟨by simp⟩

/-- The blowup of the binomial center over the base torus is the blowup of the corresponding
coordinate-section point in the projective line over the Laurent ring. -/
def Ray.characterRulingLaurentBlowupIso (ρ : Φ.Ray)
    (j : Fin 2) (hρ : ρ.primitiveGenerator = if j = 0 then b 0 else -b 0)
    (hdim : Module.finrank ℤ N = 2) (hmρ : m ρ.primitiveGenerator = 0)
    (hsurj : Function.Surjective m) (c : ℂˣ) :
    ((ρ.binomialCenter hdim hmρ hsurj c).ker.comap (ι)).blowup ≅ (center[j, c]).blowup :=
  (center[j, c]).blowupIso (eL) (ρ.comap_coordinateSectionCenter_characterRulingLaurentIso
    h b hm hpos hneg j hρ hdim hmρ hsurj c)

/-- The blowup comparison intertwines the projections by the Laurent ruling isomorphism. -/
@[reassoc (attr := simp)]
theorem Ray.characterRulingLaurentBlowupIso_hom_comp_blowupToBase (ρ : Φ.Ray)
    (j : Fin 2) (hρ : ρ.primitiveGenerator = if j = 0 then b 0 else -b 0)
    (hdim : Module.finrank ℤ N = 2) (hmρ : m ρ.primitiveGenerator = 0)
    (hsurj : Function.Surjective m) (c : ℂˣ) :
    (ρ.characterRulingLaurentBlowupIso h b hm hpos hneg j hρ hdim hmρ hsurj c).hom ≫
        (center[j, c]).blowupToBase =
      ((ρ.binomialCenter hdim hmρ hsurj c).ker.comap (ι)).blowupToBase ≫ (eL).hom :=
  (center[j, c]).blowupIso_hom_blowupToBase _ _

end TauCeti.Toric.Fan

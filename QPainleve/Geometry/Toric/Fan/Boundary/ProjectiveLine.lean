/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Component
public import QPainleve.Geometry.Toric.Fan.Point
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Scaling

import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
import QPainleve.Geometry.Toric.Fan.Adjacency
import QPainleve.Geometry.Toric.Fan.Boundary.Intersection
import TauCeti.AlgebraicGeometry.Curves.ProjectiveLine

/-!
# Projective coordinates on toric boundary components

For a proper ray divisor of a regular toric surface, a primitive character annihilating
the ray identifies the divisor with the projective line, extending the Laurent coordinate
on its open orbit. The neighboring nodes correspond to zero and the pole according to the
sign of the character. A binomial center with parameter `c` has value `-c⁻¹`. This fixes
the projective coordinate used to compare center divisors in the period calculation of
Gross, Hacking and Keel,
[*Moduli of surfaces with an anti-canonical cycle*, §2](https://arxiv.org/html/1211.6367v5#S2).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Multiplicative
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry

namespace TauCeti.Toric

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

namespace Fan

variable {Φ : Fan i} (hΦ : Φ.IsRegular) (ρ : Φ.Ray)

local notation "D" => Φ.rayBoundaryIdeal hΦ ρ

local notation "base" => Spec (CommRingCat.of ℂ)
local notation "Gm" => Spec (CommRingCat.of (LaurentPolynomial ℂ))

variable (hdim : Module.finrank ℤ N = 2) {m : N →+ ℤ}
  (hm : m ρ.primitiveGenerator = 0) (hprim : Function.Surjective m)

local notation "j" => ρ.orbitToComponent hΦ hdim hm hprim
local notation "t" => projectiveLine.torusInclusion ℂ

private instance : (t).IsOver base := ⟨projectiveLine.torusInclusion_over ℂ⟩

private def rayBoundaryFunctionFieldEquiv :
    (projectiveLine ℂ).functionField ≃ₐ[ℂ] (D).subscheme.functionField :=
  let eP := (asIso (t).functionFieldMap).commRingCatIsoToRingEquiv
  let eD := (asIso (j).functionFieldMap).commRingCatIsoToRingEquiv
  (AlgEquiv.ofRingEquiv (f := eP) ((t).functionFieldMap_algebraMap ℂ)).trans
    (AlgEquiv.ofRingEquiv (f := eD) ((j).functionFieldMap_algebraMap ℂ)).symm

variable [hproper : IsProper ((Φ.rayBoundaryIdeal hΦ ρ).subscheme ↘ Spec (.of ℂ))]

/-- A proper reduced ray divisor of a regular toric surface is a projective line.
The coordinate is normalized by the given primitive character on the open orbit. -/
def Ray.boundaryIsoProjectiveLine : (D).subscheme ≅ projectiveLine ℂ :=
  letI := Φ.isRegular_rayBoundary hΦ ρ
  (D).subscheme.isoProjectiveLine
    ((projectiveLine.functionFieldEquiv ℂ).symm.trans
      (rayBoundaryFunctionFieldEquiv hΦ ρ hdim hm hprim))

instance Ray.isOver_boundaryIsoProjectiveLine_hom :
    (ρ.boundaryIsoProjectiveLine hΦ hdim hm hprim).hom.IsOver base := by
  let := Φ.isRegular_rayBoundary hΦ ρ
  unfold Ray.boundaryIsoProjectiveLine
  infer_instance

/-- The projective coordinate restricts to the prescribed Laurent coordinate on the ray orbit. -/
@[reassoc (attr := simp)]
theorem Ray.orbitToComponent_comp_boundaryIsoProjectiveLine :
    j ≫ (ρ.boundaryIsoProjectiveLine hΦ hdim hm hprim).hom = t := by
  let := Φ.isRegular_rayBoundary hΦ ρ
  apply Scheme.Hom.ext_of_functionFieldMap_eq base
  ext x
  rw [Scheme.Hom.functionFieldMap_comp, CommRingCat.comp_apply]
  simp only [Ray.boundaryIsoProjectiveLine, Scheme.functionFieldMap_isoProjectiveLine_hom,
    AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, rayBoundaryFunctionFieldEquiv]
  let e := AlgEquiv.ofRingEquiv (f := (asIso (j).functionFieldMap).commRingCatIsoToRingEquiv)
    ((j).functionFieldMap_algebraMap ℂ)
  exact e.apply_symm_apply _

/-- The binomial center with parameter `c` is the projective point with coordinates
`[-c⁻¹ : 1]` in the projective coordinate extending its primitive character. -/
@[reassoc]
theorem Ray.binomialCenterOnComponent_comp_boundaryIsoProjectiveLine (c : ℂˣ) :
    ρ.binomialCenterOnComponent hΦ hdim hm hprim c ≫
      (ρ.boundaryIsoProjectiveLine hΦ hdim hm hprim).hom =
        projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 1
          (((-1 : ℂˣ) * c⁻¹ : ℂˣ) : ℂ) := by
  rw [ρ.binomialCenterOnComponent_eq, Category.assoc,
    Ray.orbitToComponent_comp_boundaryIsoProjectiveLine,
    projectiveLine.torusInclusion_eq_polynomialPoint, projectiveLine.SpecMap_polynomialPoint]
  congr 2
  · ext a
    exact (laurentEval ((-1 : ℂˣ) * c⁻¹)).commutes a
  · exact laurentEval_T_one _

section Nodes

open LaurentPolynomial

private theorem torusInclusion_eq_polynomialPoint (s : Fin 2) :
    t = projectiveLine.polynomialPoint ℂ (algebraMap ℂ (LaurentPolynomial ℂ)) s
      (T (if s = 1 then 1 else -1)) := by
  fin_cases s
  · rw [projectiveLine.torusInclusion_eq_polynomialPoint]
    simpa [genericUnit_val, genericUnit_inv] using
      projectiveLine.polynomialPoint_rev (algebraMap ℂ (LaurentPolynomial ℂ)) 1 (genericUnit ℂ)
  · exact projectiveLine.torusInclusion_eq_polynomialPoint ℂ

variable {σ : Φ.cones} (hρ : ρ.toCone ≤ σ)

local notation "A" => affineCoordinateRing Φ.lattice σ.val
local notation "face" => Φ.isFaceOf_of_le σ.property ρ.toCone.property hρ
local notation "q" => ρ.orbitToRayChart hdim hm hprim

omit hproper in
private theorem orbitToRayChart_comp_face_comp_polynomialPoint
    (s : Fin 2) (a : dualSemigroup Φ.lattice σ.val)
    (ha : (a : N →+ ℤ) = (if s = 1 then 1 else -1 : ℤ) • m) :
    q ≫ faceAffineToricSchemeMap Φ.lattice face ≫
      projectiveLine.polynomialPoint ℂ (algebraMap ℂ A) s (MonoidAlgebra.single (ofAdd a) 1) =
        t := by
  rw [faceAffineToricSchemeMap_def, projectiveLine.SpecMap_polynomialPoint,
    Ray.orbitToRayChart_def, projectiveLine.SpecMap_polynomialPoint,
    torusInclusion_eq_polynomialPoint s]
  have hcoeff :
      ((ρ.orbitCoordinateMap hdim hm hprim).toRingHom.comp
        ((faceAffineCoordinateRingMap Φ.lattice face).toRingHom.comp (algebraMap ℂ A))) =
          algebraMap ℂ (LaurentPolynomial ℂ) := by
    apply RingHom.ext
    intro c
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rw [hcoeff]
  congr 1
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, faceAffineCoordinateRingMap_single]
  let n : ℤ := if s = 1 then 1 else -1
  have he : (⟨a, dualSemigroup_anti Φ.lattice (face).le a.property⟩ :
      dualSemigroup Φ.lattice ρ.toCone.val) = ρ.chartCharacter (m := n • m) (by simp [hm]) :=
    Subtype.ext (by simpa only [Ray.coe_chartCharacter] using ha)
  rw [he, ρ.orbitCoordinateMap_zsmul_chartCharacter]

include hρ

private theorem boundaryIsoProjectiveLine_on_cone
    (s : Fin 2) (a : dualSemigroup Φ.lattice σ.val)
    (ha : (a : N →+ ℤ) = (if s = 1 then 1 else -1 : ℤ) • m) :
    pullback.fst (D).subschemeι (Φ.affineToricChartι σ) ≫
        (ρ.boundaryIsoProjectiveLine hΦ hdim hm hprim).hom =
      pullback.snd (D).subschemeι (Φ.affineToricChartι σ) ≫
        projectiveLine.polynomialPoint ℂ (algebraMap ℂ A) s (MonoidAlgebra.single (ofAdd a) 1) := by
  let u := pullback.fst (D).subschemeι (Φ.affineToricChartι σ)
  let v := pullback.snd (D).subschemeι (Φ.affineToricChartι σ)
  let e := ρ.boundaryIsoProjectiveLine hΦ hdim hm hprim
  let p := projectiveLine.polynomialPoint ℂ (algebraMap ℂ A) s (MonoidAlgebra.single (ofAdd a) 1)
  let g : Gm ⟶ pullback (D).subschemeι (Φ.affineToricChartι σ) :=
    pullback.lift j (q ≫ faceAffineToricSchemeMap Φ.lattice face) (by simp)
  have hgu : g ≫ u = j := pullback.lift_fst _ _ _
  have hgv : g ≫ v = q ≫ faceAffineToricSchemeMap Φ.lattice face := pullback.lift_snd _ _ _
  let : (pullback (D).subschemeι (Φ.affineToricChartι σ)).Over base := ⟨u ≫ (D).subscheme ↘ base⟩
  have : IsOpenImmersion u := inferInstanceAs (IsOpenImmersion (pullback.fst _ _))
  have : IsReduced (pullback (D).subschemeι (Φ.affineToricChartι σ)) :=
    isReduced_of_isOpenImmersion u
  have : IsDominant g := IsDominant.of_comp_of_isOpenImmersion g u (H := hgu ▸ inferInstance)
  have hu : pullback (D).subschemeι (Φ.affineToricChartι σ) ↘ base =
      u ≫ (D).subscheme ↘ base := (rfl)
  have : u.IsOver base := ⟨hu.symm⟩
  have : g.IsOver base := ⟨by rw [hu, ← Category.assoc, hgu, comp_over]⟩
  have : (v ≫ p).IsOver base := ⟨by
    rw [Category.assoc, projectiveLine.polynomialPoint_over, ← specOverSpec_over,
      ← comp_over (Φ.affineToricChartι σ) base, ← pullback.condition_assoc, hu,
      over_eq_subschemeι_comp]⟩
  apply ext_of_isDominant_of_isSeparated' base g (f := u ≫ e.hom) (g := v ≫ p)
  rw [← Category.assoc, hgu, Ray.orbitToComponent_comp_boundaryIsoProjectiveLine,
    ← Category.assoc, hgv, Category.assoc]
  exact (orbitToRayChart_comp_face_comp_polynomialPoint ρ hdim hm hprim hρ s a ha).symm

private theorem polynomialPoint_comp_boundaryIsoProjectiveLine_inv_subschemeι
    (τ : Φ.Ray) (hτ : τ.toCone ≤ σ) (hne : ρ ≠ τ) (s : Fin 2)
    (hs : 0 < (if s = 1 then 1 else -1 : ℤ) * m τ.primitiveGenerator) :
    projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) s 0 ≫
      (ρ.boundaryIsoProjectiveLine hΦ hdim hm hprim).inv ≫ (D).subschemeι =
        Φ.distinguishedPointHom σ := by
  let n : ℤ := if s = 1 then 1 else -1
  let hσ := Φ.isToricCone σ.property
  let r := τ.toToricRay Φ σ hτ
  have hn : n • m ∈ dualSemigroup Φ.lattice σ.val := by
    rw [mem_dualSemigroup_iff_primitiveGenerator Φ.lattice hσ]
    intro υ
    have hmem := Φ.toricRays_eq_pair ((isRegular_iff.mp hΦ) _ σ.property) hdim hne hρ hτ
    have hυ : υ ∈ ({ρ.toToricRay Φ σ hρ, r} : Set (ToricRay σ.val)) := hmem.symm ▸ Set.mem_univ _
    rcases Set.mem_insert_iff.mp hυ with h | h
    · rw [h, Ray.primitiveGenerator_toToricRay]
      simp [hm]
    · rw [Set.mem_singleton_iff.mp h, Ray.primitiveGenerator_toToricRay]
      exact hs.le
  let a : dualSemigroup Φ.lattice σ.val := ⟨n • m, hn⟩
  let d := distinguishedPoint Φ.lattice (⊤ : σ.val.Face)
  have hz : d (MonoidAlgebra.single (ofAdd a) 1) = 0 := by
    refine distinguishedPoint_top_single_eq_zero_of_pos Φ.lattice hσ r a ?_
    rw [Ray.primitiveGenerator_toToricRay]
    exact hs
  let w := Spec.map (CommRingCat.ofHom d.toRingHom)
  have hk : D ≤ (Φ.distinguishedPointHom σ).ker := by
    rw [Φ.distinguishedPointHom_def]
    exact le_sup_left.trans_eq (Φ.sup_rayBoundaryIdeal_eq_ker_distinguishedPoint hΦ hdim
      hne σ hρ hτ)
  let p := IsClosedImmersion.lift (D).subschemeι (Φ.distinguishedPointHom σ)
    (by rwa [ker_subschemeι])
  have hp : p ≫ (D).subschemeι = Φ.distinguishedPointHom σ := IsClosedImmersion.lift_fac _ _ _
  have he : p ≫ (ρ.boundaryIsoProjectiveLine hΦ hdim hm hprim).hom =
      projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) s 0 := by
    rw [← pullback.lift_fst p w (hp.trans (Φ.distinguishedPointHom_def σ)), Category.assoc,
      boundaryIsoProjectiveLine_on_cone hΦ ρ hdim hm hprim hρ s a rfl, ← Category.assoc,
      pullback.lift_snd, projectiveLine.SpecMap_polynomialPoint]
    have hcoeff : (d : A →+* ℂ).comp (algebraMap ℂ A) = RingHom.id ℂ :=
      RingHom.ext d.commutes
    simp only [hcoeff, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hz]
  rw [← he, Category.assoc, Iso.hom_inv_id_assoc, hp]

/-- At the intersection with a neighboring ray on which the character is positive,
the projective coordinate is zero, with homogeneous coordinates `[0 : 1]`. -/
@[reassoc]
theorem Ray.polynomialPoint_comp_boundaryIsoProjectiveLine_inv_subschemeι_of_pos
    (τ : Φ.Ray) (hτ : τ.toCone ≤ σ) (hs : 0 < m τ.primitiveGenerator) :
    projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 1 0 ≫
      (ρ.boundaryIsoProjectiveLine hΦ hdim hm hprim).inv ≫ (D).subschemeι =
        Φ.distinguishedPointHom σ := by
  have hne : ρ ≠ τ := fun h ↦ hs.ne' (h ▸ hm)
  exact polynomialPoint_comp_boundaryIsoProjectiveLine_inv_subschemeι hΦ ρ
    hdim hm hprim hρ τ hτ hne 1 (by simpa using hs)

/-- At the intersection with a neighboring ray on which the character is negative,
the projective coordinate has a pole, with homogeneous coordinates `[1 : 0]`. -/
@[reassoc]
theorem Ray.polynomialPoint_comp_boundaryIsoProjectiveLine_inv_subschemeι_of_neg
    (τ : Φ.Ray) (hτ : τ.toCone ≤ σ) (hs : m τ.primitiveGenerator < 0) :
    projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 0 0 ≫
      (ρ.boundaryIsoProjectiveLine hΦ hdim hm hprim).inv ≫ (D).subschemeι =
        Φ.distinguishedPointHom σ := by
  have hne : ρ ≠ τ := fun h ↦ hs.ne (h ▸ hm)
  exact polynomialPoint_comp_boundaryIsoProjectiveLine_inv_subschemeι hΦ ρ
    hdim hm hprim hρ τ hτ hne 0 (by simpa using neg_pos.mpr hs)

end Nodes

end Fan
end TauCeti.Toric

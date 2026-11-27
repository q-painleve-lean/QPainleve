/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Component
public import QPainleve.Geometry.Toric.BaseChange.Point
public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Scaling

import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Basic
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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AddMonoidAlgebra
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry

namespace TauCeti.Toric

universe u

variable (k : Type u) [Field k] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

namespace Fan

variable {Φ : Fan i} (hΦ : Φ.IsRegular) (ρ : Φ.Ray)

local notation "D" => Φ.rayDivisorIdeal k hΦ ρ

local notation "base" => Spec (CommRingCat.of k)
local notation "Gm" => Spec (CommRingCat.of (LaurentPolynomial k))

variable (hdim : Module.finrank ℤ N = 2) {m : N →+ ℤ}
  (hm : m ρ.primitiveGenerator = 0) (hprim : Function.Surjective m)

local notation "j" => ρ.orbitToComponent k hΦ hdim hm hprim
local notation "t" => projectiveLine.torusInclusion k

private instance : (t).IsOver base := ⟨projectiveLine.torusInclusion_over k⟩

private def rayBoundaryFunctionFieldEquiv :
    (projectiveLine k).functionField ≃ₐ[k] (D).subscheme.functionField :=
  let eP := (asIso (t).functionFieldMap).commRingCatIsoToRingEquiv
  let eD := (asIso (j).functionFieldMap).commRingCatIsoToRingEquiv
  (AlgEquiv.ofRingEquiv (f := eP) ((t).functionFieldMap_algebraMap k)).trans
    (AlgEquiv.ofRingEquiv (f := eD) ((j).functionFieldMap_algebraMap k)).symm

variable [hproper : IsProper ((Φ.rayDivisorIdeal k hΦ ρ).subscheme ↘ Spec (.of k))]

/-- A proper reduced ray divisor of a regular toric surface is a projective line.
The coordinate is normalized by the given primitive character on the open orbit. -/
def Ray.boundaryIsoProjectiveLine : (D).subscheme ≅ projectiveLine k :=
  letI := Φ.isRegular_rayBoundary k hΦ ρ
  (D).subscheme.isoProjectiveLine
    ((projectiveLine.functionFieldEquiv k).symm.trans
      (rayBoundaryFunctionFieldEquiv k hΦ ρ hdim hm hprim))

instance Ray.isOver_boundaryIsoProjectiveLine_hom :
    (ρ.boundaryIsoProjectiveLine k hΦ hdim hm hprim).hom.IsOver base := by
  let := Φ.isRegular_rayBoundary k hΦ ρ
  unfold Ray.boundaryIsoProjectiveLine
  infer_instance

include hdim hm hprim in
/-- A proper ray divisor of a regular toric surface is a curve over the coefficient field. -/
theorem Ray.isCurveOver_boundaryComponent : (D).subscheme.IsCurveOver k := by
  let p := ρ.boundaryIsoProjectiveLine k hΦ hdim hm hprim
  have hp := p.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq
  exact Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, hp.trans (Scheme.IsCurveOver.topologicalKrullDim_eq_one k)⟩

/-- The projective coordinate restricts to the prescribed Laurent coordinate on the ray orbit. -/
@[reassoc (attr := simp)]
theorem Ray.orbitToComponent_comp_boundaryIsoProjectiveLine :
    j ≫ (ρ.boundaryIsoProjectiveLine k hΦ hdim hm hprim).hom = t := by
  let := Φ.isRegular_rayBoundary k hΦ ρ
  apply Scheme.Hom.ext_of_functionFieldMap_eq base
  ext x
  rw [Scheme.Hom.functionFieldMap_comp, CommRingCat.comp_apply]
  simp only [Ray.boundaryIsoProjectiveLine, Scheme.functionFieldMap_isoProjectiveLine_hom,
    AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, rayBoundaryFunctionFieldEquiv]
  let e := AlgEquiv.ofRingEquiv (f := (asIso (j).functionFieldMap).commRingCatIsoToRingEquiv)
    ((j).functionFieldMap_algebraMap k)
  exact e.apply_symm_apply _

/-- The binomial center with parameter `c` is the projective point with coordinates
`[-c⁻¹ : 1]` in the projective coordinate extending its primitive character. -/
@[reassoc]
theorem Ray.binomialCenterOnComponent_comp_boundaryIsoProjectiveLine (c : kˣ) :
    ρ.binomialCenterOnComponent k hΦ hdim hm hprim c ≫
      (ρ.boundaryIsoProjectiveLine k hΦ hdim hm hprim).hom =
        projectiveLine.polynomialPoint k (RingHom.id k) 1
          (((-1 : kˣ) * c⁻¹ : kˣ) : k) := by
  rw [ρ.binomialCenterOnComponent_eq k, Category.assoc,
    Ray.orbitToComponent_comp_boundaryIsoProjectiveLine,
    projectiveLine.torusInclusion_eq_polynomialPoint, projectiveLine.SpecMap_polynomialPoint]
  congr 2
  · ext a
    exact (laurentEval ((-1 : kˣ) * c⁻¹)).commutes a
  · exact laurentEval_T_one _

section Nodes

open LaurentPolynomial

private theorem torusInclusion_eq_polynomialPoint (s : Fin 2) :
    t = projectiveLine.polynomialPoint k (algebraMap k (LaurentPolynomial k)) s
      (T (if s = 1 then 1 else -1)) := by
  fin_cases s
  · rw [projectiveLine.torusInclusion_eq_polynomialPoint]
    simpa [genericUnit_val, genericUnit_inv] using
      projectiveLine.polynomialPoint_rev (algebraMap k (LaurentPolynomial k)) 1 (genericUnit k)
  · exact projectiveLine.torusInclusion_eq_polynomialPoint k

variable {σ : Φ.cones} (hρ : ρ.toCone ≤ σ)

local notation "A" => affineChartRing k Φ.lattice σ.val
local notation "face" => Φ.isFaceOf_of_le σ.property ρ.toCone.property hρ
local notation "q" => ρ.orbitToRayChart k hdim hm hprim

omit hproper in
private theorem orbitToRayChart_comp_face_comp_polynomialPoint
    (s : Fin 2) (a : dualSemigroup Φ.lattice σ.val)
    (ha : (a : N →+ ℤ) = (if s = 1 then 1 else -1 : ℤ) • m) :
    q ≫ faceAffineChartMap k Φ.lattice face ≫
      projectiveLine.polynomialPoint k (algebraMap k A) s (single a 1) =
        t := by
  rw [faceAffineChartMap_def, projectiveLine.SpecMap_polynomialPoint,
    Ray.orbitToRayChart_def, projectiveLine.SpecMap_polynomialPoint,
    torusInclusion_eq_polynomialPoint k s]
  have hcoeff :
      ((ρ.orbitCoordinateMap k hdim hm hprim).toRingHom.comp
        ((faceAffineChartRingMap k Φ.lattice face).toRingHom.comp (algebraMap k A))) =
          algebraMap k (LaurentPolynomial k) := by
    apply RingHom.ext
    intro c
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rw [hcoeff]
  congr 1
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, faceAffineChartRingMap_single]
  let n : ℤ := if s = 1 then 1 else -1
  have he : AddSubmonoid.inclusion (dualSemigroup_anti Φ.lattice (face).le) a =
      ρ.chartCharacter (m := n • m) (by simp [hm]) := by
    apply Subtype.ext
    rw [AddSubmonoid.coe_inclusion, Ray.coe_chartCharacter]
    exact ha
  rw [he, ρ.orbitCoordinateMap_zsmul_chartCharacter]

include hρ

private theorem boundaryIsoProjectiveLine_on_cone
    (s : Fin 2) (a : dualSemigroup Φ.lattice σ.val)
    (ha : (a : N →+ ℤ) = (if s = 1 then 1 else -1 : ℤ) • m) :
    pullback.fst (D).subschemeι (Φ.affineChartι k σ) ≫
        (ρ.boundaryIsoProjectiveLine k hΦ hdim hm hprim).hom =
      pullback.snd (D).subschemeι (Φ.affineChartι k σ) ≫
        projectiveLine.polynomialPoint k (algebraMap k A) s (single a 1) := by
  let u := pullback.fst (D).subschemeι (Φ.affineChartι k σ)
  let v := pullback.snd (D).subschemeι (Φ.affineChartι k σ)
  let e := ρ.boundaryIsoProjectiveLine k hΦ hdim hm hprim
  let p := projectiveLine.polynomialPoint k (algebraMap k A) s (single a 1)
  let g : Gm ⟶ pullback (D).subschemeι (Φ.affineChartι k σ) :=
    pullback.lift j (q ≫ faceAffineChartMap k Φ.lattice face) (by simp)
  have hgu : g ≫ u = j := pullback.lift_fst _ _ _
  have hgv : g ≫ v = q ≫ faceAffineChartMap k Φ.lattice face := pullback.lift_snd _ _ _
  let : (pullback (D).subschemeι (Φ.affineChartι k σ)).Over base := ⟨u ≫ (D).subscheme ↘ base⟩
  have : IsOpenImmersion u := inferInstanceAs (IsOpenImmersion (pullback.fst _ _))
  have : IsReduced (pullback (D).subschemeι (Φ.affineChartι k σ)) :=
    isReduced_of_isOpenImmersion u
  have : IsDominant g := IsDominant.of_comp_of_isOpenImmersion g u (H := hgu ▸ inferInstance)
  have hu : pullback (D).subschemeι (Φ.affineChartι k σ) ↘ base =
      u ≫ (D).subscheme ↘ base := (rfl)
  have : u.IsOver base := ⟨hu.symm⟩
  have : g.IsOver base := ⟨by rw [hu, ← Category.assoc, hgu, comp_over]⟩
  have : (v ≫ p).IsOver base := ⟨by
    rw [Category.assoc, projectiveLine.polynomialPoint_over, ← specOverSpec_over,
      ← comp_over (Φ.affineChartι k σ) base, ← pullback.condition_assoc, hu,
      over_eq_subschemeι_comp]⟩
  apply ext_of_isDominant_of_isSeparated' base g (f := u ≫ e.hom) (g := v ≫ p)
  rw [← Category.assoc, hgu, Ray.orbitToComponent_comp_boundaryIsoProjectiveLine,
    ← Category.assoc, hgv, Category.assoc]
  exact (orbitToRayChart_comp_face_comp_polynomialPoint k ρ hdim hm hprim hρ s a ha).symm

private theorem polynomialPoint_comp_boundaryIsoProjectiveLine_inv_subschemeι
    (τ : Φ.Ray) (hτ : τ.toCone ≤ σ) (hne : ρ ≠ τ) (s : Fin 2)
    (hs : 0 < (if s = 1 then 1 else -1 : ℤ) * m τ.primitiveGenerator) :
    projectiveLine.polynomialPoint k (RingHom.id k) s 0 ≫
      (ρ.boundaryIsoProjectiveLine k hΦ hdim hm hprim).inv ≫ (D).subschemeι =
        Φ.distinguishedSection (R := k) σ := by
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
  let d := facePointAlgebraHom Φ.lattice (⊤ : σ.val.Face) k
  have hz : d (single a 1) = 0 := by
    refine facePointAlgebraHom_top_single_eq_zero_of_pos k Φ.lattice hσ r a 1 ?_
    rw [Ray.primitiveGenerator_toToricRay]
    exact hs
  let w := Spec.map (CommRingCat.ofHom d.toRingHom)
  have hk : D ≤ (Φ.distinguishedSection (R := k) σ).ker :=
    le_sup_left.trans_eq (Φ.sup_rayBoundaryIdeal_eq_ker_distinguishedPoint k hΦ hdim
      hne σ hρ hτ)
  let p := IsClosedImmersion.lift (D).subschemeι (Φ.distinguishedSection (R := k) σ)
    (by rwa [ker_subschemeι])
  have hp : p ≫ (D).subschemeι = Φ.distinguishedSection (R := k) σ :=
    IsClosedImmersion.lift_fac _ _ _
  have he : p ≫ (ρ.boundaryIsoProjectiveLine k hΦ hdim hm hprim).hom =
      projectiveLine.polynomialPoint k (RingHom.id k) s 0 := by
    rw [← pullback.lift_fst p w (hp.trans (Φ.distinguishedSection_def (R := k) σ)), Category.assoc,
      boundaryIsoProjectiveLine_on_cone k hΦ ρ hdim hm hprim hρ s a rfl, ← Category.assoc,
      pullback.lift_snd, projectiveLine.SpecMap_polynomialPoint]
    have hcoeff : (d : A →+* k).comp (algebraMap k A) = RingHom.id k :=
      RingHom.ext d.commutes
    simp only [hcoeff, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hz]
  rw [← he, Category.assoc, Iso.hom_inv_id_assoc, hp]

/-- At the intersection with a neighboring ray on which the character is positive,
the projective coordinate is zero, with homogeneous coordinates `[0 : 1]`. -/
@[reassoc]
theorem Ray.polynomialPoint_comp_boundaryIsoProjectiveLine_inv_subschemeι_of_pos
    (τ : Φ.Ray) (hτ : τ.toCone ≤ σ) (hs : 0 < m τ.primitiveGenerator) :
    projectiveLine.polynomialPoint k (RingHom.id k) 1 0 ≫
      (ρ.boundaryIsoProjectiveLine k hΦ hdim hm hprim).inv ≫ (D).subschemeι =
        Φ.distinguishedSection (R := k) σ := by
  have hne : ρ ≠ τ := fun h ↦ hs.ne' (h ▸ hm)
  exact polynomialPoint_comp_boundaryIsoProjectiveLine_inv_subschemeι k hΦ ρ
    hdim hm hprim hρ τ hτ hne 1 (by simpa using hs)

/-- At the intersection with a neighboring ray on which the character is negative,
the projective coordinate has a pole, with homogeneous coordinates `[1 : 0]`. -/
@[reassoc]
theorem Ray.polynomialPoint_comp_boundaryIsoProjectiveLine_inv_subschemeι_of_neg
    (τ : Φ.Ray) (hτ : τ.toCone ≤ σ) (hs : m τ.primitiveGenerator < 0) :
    projectiveLine.polynomialPoint k (RingHom.id k) 0 0 ≫
      (ρ.boundaryIsoProjectiveLine k hΦ hdim hm hprim).inv ≫ (D).subschemeι =
        Φ.distinguishedSection (R := k) σ := by
  have hne : ρ ≠ τ := fun h ↦ hs.ne (h ▸ hm)
  exact polynomialPoint_comp_boundaryIsoProjectiveLine_inv_subschemeι k hΦ ρ
    hdim hm hprim hρ τ hτ hne 0 (by simpa using neg_pos.mpr hs)

end Nodes

end Fan
end TauCeti.Toric

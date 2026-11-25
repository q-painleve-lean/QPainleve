/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Numbering
public import QPainleve.AlgebraicGeometry.Curves.GenusZero
public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.SmoothProjective
public import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef
public import QPainleve.SignedClusterModularGroup.Examples.ElevenVertex.Model

import QPainleve.AlgebraicGeometry.Blowup.Intersection
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.Chow.Birational
import QPainleve.AlgebraicGeometry.Chow.Nef.Boundary
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Curves.Node.Image
import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial
import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Regular
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.Image.Over
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Numerical
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Rationality
import QPainleve.Geometry.Toric.Fan.Boundary.DualGraph
import QPainleve.Geometry.Toric.Fan.Boundary.InternalBlowup
import QPainleve.Geometry.Toric.Fan.Boundary.Prestable
import QPainleve.Geometry.Toric.Fan.Boundary.StrictTransform
import QPainleve.Geometry.Toric.Fan.Logarithmic.InternalBlowup
import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Canonical
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition
import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# Boundary contractions of the eleven-vertex model

The boundary of the ordered plane blowup is an anticanonical triangle. The first
two strict lines can be contracted in order, giving an integral nodal anticanonical
curve with primitive nef square-zero class. Its pullback is the weighted triangle,
and its ordered branches retain the orientation of the original boundary.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module TopologicalSpace
open QPainleve.BlowupTower Scheme.IdealSheafData TauCeti.AlgebraicGeometry
open TauCeti.Toric TauCeti.Toric.Fan LineBundleClass

namespace QPainleve.ElevenVertex

local notation "b" => Pi.basisFun ℤ (Fin 2)
local notation "hi" => isIntegralLattice_intCast 2
local notation "Φ" => projectiveSpace b hi
local notation "hΦ" => isRegular_projectiveSpace b hi
local notation "hc" => isComplete_projectiveSpace b hi
local notation "Plane" => Fan.algebraicRealization Φ
local notation "S" => Spec (CommRingCat.of ℂ)
local instance : Nonempty (Φ).cones := Fan.IsComplete.nonempty_cones hc

local notation "T(" c ")" => WithBoundary.toTower (Sigma.snd (planeBlowup c))
local notation "Y(" c ")" => Sigma.fst (planeBlowup c)
local notation "hT(" c ")" => isClosedPointTower_internalBlowupTower b planeCenterRay c
local notation "D₀" => Fan.boundaryIdeal Φ inferInstance
local notation "B(" c ")" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd (planeBlowup c)))
local notation "C(" c ", " j ")" =>
  BlowupTower.strictTransform (Fan.rayBoundaryIdeal Φ hΦ (planeBoundaryRay j)) (T(c))
local notation "L(" c ", " j ")" =>
  strictRayBoundaryClass hΦ (by simp) (T(c)) (hT(c)) (planeBoundaryRay j)
local notation "class[" h "]" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "K(" X ")" => LineBundleClass.mk (canonicalBundle ℂ X 2)

local instance : SmoothOfRelativeDimension 2 (Plane ↘ S) := by
  rw [algebraicRealization_over]
  simpa using (Φ).smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ

local instance : (Plane).IsProjectiveOver ℂ :=
  (Φ).isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b

/-- The structure map of the ordered blowup model factors through the plane. -/
local instance modelOver (c : Fin 11 → ℂˣ) : (Y(c)).Over S :=
  ⟨(T(c)).toBase ≫ (Plane ↘ S)⟩

local instance modelSmooth (c : Fin 11 → ℂˣ) : SmoothOfRelativeDimension 2 (Y(c) ↘ S) :=
  (hT(c)).smoothOfRelativeDimension (Plane ↘ S)

local instance (c : Fin 11 → ℂˣ) : (Y(c)).IsProjectiveOver ℂ := (T(c)).isProjectiveOver ℂ

local instance (c : Fin 11 → ℂˣ) : IsIntegral (Y(c)) :=
  isIntegral_internalBlowupTower b planeCenterRay c hΦ

local instance (c : Fin 11 → ℂˣ) :
    (WithBoundary.boundaryι (Sigma.snd (planeBlowup c))).IsOver S := by
  refine ⟨?_⟩
  rw [(D₀).over_eq_subschemeι_comp]
  exact (planeBlowup c).2.boundaryι_toBase_assoc _

private theorem subschemeIso_planeBlowup_boundary (c : Fin 11 → ℂˣ) :
    ∃ e : (D₀).subscheme ≅ (B(c)).subscheme, e.hom.IsOver S := by
  let f := (planeBlowup c).2.boundaryι
  let : f.IsOver S := inferInstanceAs
    ((WithBoundary.boundaryι (Sigma.snd (planeBlowup c))).IsOver S)
  exact ⟨asIso f.toImage, inferInstanceAs (f.toImage.IsOver S)⟩

/-- The ideal line bundle of the strict triangle is the canonical bundle of the
ordered plane blowup. -/
theorem mk_toInvertibleSheaf_planeBlowup_boundary (c : Fin 11 → ℂˣ)
    (hB : (B(c)).IsEffectiveCartier) : LineBundleClass.mk hB.toInvertibleSheaf = K(Y(c)) := by
  let hD := (Φ).isEffectiveCartier_boundaryIdeal hΦ hc (by simp)
  let : IsNoetherian Plane := isNoetherian_of_finiteType (Plane ↘ S)
  let : (T(c)).toBase.IsOver S := ⟨rfl⟩
  let hR := (hT(c)).isEffectiveCartier_ramificationIdealSheafToBase ℂ
  let hTot := (hT(c)).isEffectiveCartier_totalTransform (Plane ↘ S) hD
  have hI := comap_boundaryIdeal_internalBlowupTower b planeCenterRay c hΦ hD
  have hPic := (hD.pullback_mk_toInvertibleSheaf hTot).trans
    ((mk_toInvertibleSheaf_congr hTot (TauCeti.isEffectiveCartier_mul hB hR) hI).trans
      (mk_toInvertibleSheaf_mul hB hR))
  have hRam := (hT(c)).ramificationIdealSheafToBase_def ℂ
  have hK := mk_canonicalBundle_eq_pullback_mul_inv_ramification ℂ (T(c)).toBase 2
    (hRam ▸ hR)
  rw [← mk_toInvertibleSheaf_congr hR _ hRam,
    ← mk_toInvertibleSheaf_boundaryIdeal_projectivePlane b hi hD, hPic,
    mul_inv_cancel_right] at hK
  exact hK.symm

private theorem prestableFamily_planeBlowup_boundary (c : Fin 11 → ℂˣ) :
    PrestableFamily ((B(c)).subscheme ↘ S) := by
  have : IsProper (Φ).algebraicRealizationStructureMap := by
    rw [← algebraicRealization_over]
    infer_instance
  obtain ⟨e, he⟩ := subschemeIso_planeBlowup_boundary c
  let : e.hom.IsOver S := he
  have hpre := (Φ).prestableFamily_boundary hΦ hc (by simp)
  rw [← comp_over e.hom S] at hpre
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @PrestableFamily) e.hom _).mp hpre

private theorem exists_planeBlowup_boundary_numbering (c : Fin 11 → ℂˣ)
    [PrestableFamily ((B(c)).subscheme ↘ S)] :
    Nonempty (Scheme.NodalCycleNumbering
      (PEmpty.elim : PEmpty.{1} → ((B(c)).subscheme ↘ S).smoothLocus) 3) := by
  have : IsProper (Φ).algebraicRealizationStructureMap := by
    rw [← algebraicRealization_over]
    infer_instance
  let : PrestableFamily ((D₀).subscheme ↘ S) := (Φ).prestableFamily_boundary hΦ hc (by simp)
  have hr {n : ℕ} (hn : Nat.card (Φ).Ray = n) :
      ∃ v : ZMod n ≃ (Φ).Ray, ∀ j,
        (b).detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
        ∃ σ : (Φ).cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ := by
    subst n
    obtain ⟨u, ⟨-, hu⟩, -⟩ :=
      (Φ).existsUnique_cyclicRayNumbering b hΦ hc (planeBoundaryRay 0)
    exact ⟨u, hu⟩
  obtain ⟨v, hv⟩ := hr ((Nat.card_congr planeBoundaryRay.symm).trans (Nat.card_fin 3))
  let marks : PEmpty.{1} → ((D₀).subscheme ↘ S).smoothLocus := PEmpty.elim
  obtain ⟨edge, order, vertex, hend, -, -⟩ :=
    (Φ).exists_toric_boundary_dualGraph_cycle hΦ hc marks b v hv
  obtain ⟨e, he⟩ := subschemeIso_planeBlowup_boundary c
  let : e.hom.IsOver S := he
  let A : Scheme.NodalCycleNumbering marks 3 := ⟨vertex, edge, order, hend⟩
  exact ⟨e.mapNodalCycleNumbering A (q := PEmpty.elim)⟩


private theorem planeBlowup_isRationalOver (c : Fin 11 → ℂˣ) :
    Scheme.IsRationalOver (Y(c) ↘ S) := by
  let e := projectivePlaneIso b hi
  let : Scheme.IsRationalOver (Plane ↘ S) := by
    have he := e.hom.birationalOver _ (Plane ↘ S)
      ((projectivePlaneIso_hom_toSpecCoeff b hi).trans (algebraicRealization_over Φ).symm)
    exact ⟨_, he.trans (Proj.birationalOver_affineSpace ℂ 2)⟩
  exact (hT(c)).isRationalOver (Plane ↘ S)

private theorem boundary_le_line (c : Fin 11 → ℂˣ) (j : Fin 3) :
    B(c) ≤ C(c, j) := by
  rw [← ker_boundaryComponentι_internalBlowupTower b planeCenterRay c hΦ (planeBoundaryRay j)]
  exact Scheme.Hom.le_ker_comp _ _

private theorem support_planeBlowup_boundary (c : Fin 11 → ℂˣ) :
    SetLike.coe (B(c)).support = ⋃ j : Fin 3, SetLike.coe (C(c, j)).support := by
  rw [support_ker_internalBlowupTower_boundaryι b planeCenterRay c hΦ]
  let P (ρ : (Φ).Ray) := SetLike.coe (strictTransform ((Φ).rayBoundaryIdeal hΦ ρ) (T(c))).support
  exact (planeBoundaryRay.surjective.iUnion_comp P).symm

/-- Contracting the strict transform of the line with two centers yields a smooth
projective rational surface with a numbered anticanonical two-component boundary.
The first line is the exceptional fiber, and the boundary map is an oriented
subdivision of the original triangle. -/
theorem exists_first_boundary_contraction (c : Fin 11 → ℂˣ) :
    letI : (Y(c)).Over S := ⟨(T(c)).toBase ≫ (Plane ↘ S)⟩
    ∃ (Z : Scheme) (s : Z ⟶ S) (f : Y(c) ⟶ Z) (p : Z),
      letI : Z.Over S := ⟨s⟩
      ∃ (_ : SmoothOfRelativeDimension 2 (Z ↘ S)),
        IsIntegral Z ∧ Z.IsProjectiveOver ℂ ∧ Scheme.IsRationalOver s ∧
        f.IsOver S ∧ IsModification f ∧ IsClosed ({p} : Set Z) ∧
        (Z.fromSpecResidueField p).ker.comap f = C(c, 0) ∧
        ∃ e : Y(c) ≅ (Z.fromSpecResidueField p).ker.blowup,
          e.hom ≫ (Z.fromSpecResidueField p).ker.blowupToBase = f ∧
          let D := (B(c)).map f
          ∃ (hD : D.IsEffectiveCartier) (_ : PrestableFamily (D.subscheme ↘ S))
            (_ : PrestableFamily ((B(c)).subscheme ↘ S)),
            LineBundleClass.mk hD.toInvertibleSheaf = K(Z) ∧
            D.comap f = B(c) * C(c, 0) ∧
            ∃ (A : Scheme.NodalCycleNumbering
                (PEmpty.elim : PEmpty.{1} → ((B(c)).subscheme ↘ S).smoothLocus) 3)
              (A' : Scheme.NodalCycleNumbering
                (PEmpty.elim : PEmpty.{1} → (D.subscheme ↘ S).smoothLocus) 2)
              (g : (B(c)).subscheme ⟶ D.subscheme),
              g ≫ D.subschemeι = (B(c)).subschemeι ≫ f ∧
              g.IsOrientedCycleSubdivision A A' := by
  let : Smooth (Y(c) ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  obtain ⟨Z, s, f, p, hZ, hProj, hSm, hf, hMod, hp, -, hF, -, e, he⟩ :=
    (isExceptionalCurveOfFirstKind_planeBlowup_first c).exists_smooth_projective_contraction
      (k := ℂ)
  let : Z.Over S := ⟨s⟩
  let : SmoothOfRelativeDimension 2 (Z ↘ S) := hSm
  let : f.IsOver S := hf
  let : IsModification f := hMod
  let : IsIntegral Z := hZ
  let : Z.IsProjectiveOver ℂ := hProj
  let : Scheme.IsRationalOver (Y(c) ↘ S) := planeBlowup_isRationalOver c
  obtain ⟨U, hU, hfU, _⟩ := IsModification.exists_isIso_morphismRestrict (f := f)
  have hover : f ≫ s = Y(c) ↘ S := hf.comp_over
  have hBir := hover ▸ f.birationalOver_of_isIso_morphismRestrict s U hU hfU
  have hRat := hBir.symm.isRationalOver s (Y(c) ↘ S)
  let hB : (B(c)).IsEffectiveCartier :=
    Fan.isEffectiveCartier_internalBlowupBoundary b planeCenterRay hΦ c
      ((Φ).isEffectiveCartier_boundaryIdeal hΦ hc (by simp))
  let hPre := prestableFamily_planeBlowup_boundary c
  let : PrestableFamily ((B(c)).subscheme ↘ S) := hPre
  obtain ⟨A⟩ := exists_planeBlowup_boundary_numbering c
  have hs : ((Z.fromSpecResidueField p).ker.comap f).support ≤ (B(c)).support :=
    hF.symm ▸ support_antitone (boundary_le_line c 0)
  obtain ⟨hD, hPre', hK, htotal, n, hn, hlen, A', g, hg, hsub⟩ :=
    hB.exists_numbering_of_exceptional_boundary_contraction A
      (mk_toInvertibleSheaf_planeBlowup_boundary c hB) hp e he hs
  have hn' : n = 2 := by omega
  subst n
  exact ⟨Z, s, f, p, hSm, hZ, hProj, hRat, hf, hMod, hp, hF, e, he,
    hD, hPre', hPre, hK, by simpa only [hF] using htotal, A, A', g, hg, hsub⟩

private theorem isEffectiveCartier_planeBlowup_line (c : Fin 11 → ℂˣ) (j : Fin 3) :
    (C(c, j)).IsEffectiveCartier :=
  (hT(c)).isEffectiveCartier_strictTransform (Plane ↘ S)
    ((Φ).isEffectiveCartier_rayBoundaryIdeal hΦ (planeBoundaryRay j))

private theorem isIntegral_planeBlowup_line (c : Fin 11 → ℂˣ) (j : Fin 3) :
    IsIntegral (C(c, j)).subscheme := by
  obtain ⟨e, -⟩ := exists_iso_projectiveLine_planeBlowup_boundary c j
  exact IsIntegral.of_isIso e.inv

private theorem planeBlowup_line_class (c : Fin 11 → ℂˣ) (j : Fin 3)
    (h : (C(c, j)).IsEffectiveCartier) : Additive.ofMul class[h] = L(c, j) :=
  (strictRayBoundaryClass_eq _ _ _ _ _ h).symm

private theorem planeBlowup_line_intersection (c : Fin 11 → ℂˣ) (j k : Fin 3)
    (hj : (C(c, j)).IsEffectiveCartier) (hk : (C(c, k)).IsEffectiveCartier) :
    Chow.classIntersectionNumber ℂ (Y(c)) class[hj] class[hk] =
      if j = k then (![(-1 : ℤ), -2, -5] : Fin 3 → ℤ) j else 1 := by
  have h := classIntersectionNumber_planeBlowup_boundary c j k
  simpa only [← planeBlowup_line_class c j hj, ← planeBlowup_line_class c k hk,
    toMul_ofMul] using h

private theorem planeBlowup_boundary_class (c : Fin 11 → ℂˣ)
    (hB : (B(c)).IsEffectiveCartier) : Additive.ofMul class[hB] = ∑ j : Fin 3, L(c, j) := by
  classical
  let : IsNoetherian Plane := isNoetherian_of_finiteType (Plane ↘ S)
  let : IsNoetherian (Y(c)) := (T(c)).isNoetherian
  let := (Y(c) ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let : PrestableFamily ((B(c)).subscheme ↘ S) := prestableFamily_planeBlowup_boundary c
  let : IsReduced (B(c)).subscheme :=
    PrestableFamily.atWorstNodalOfRelativeDimensionOne.isReduced (f := (B(c)).subscheme ↘ S)
  let v := planeBoundaryRay.trans (internalBlowupBoundaryPrimeEquiv hΦ b planeCenterRay c)
  let p := v.toEmbedding.trans (B(c)).boundaryPrimeEmbedding
  have hp : Set.range p = Set.range (B(c)).boundaryPrimeEmbedding := by
    rw [Function.Embedding.coe_trans, Set.range_comp, Equiv.coe_toEmbedding,
      Equiv.range_eq_univ, Set.image_univ]
  have hclass (j : Fin 3) : Additive.ofMul (primeDivisorClass (p j)) = L(c, j) := by
    rw [← picardHom_markedBoundaryMap_single_internalBlowupTower hΦ b planeCenterRay c
      (planeBoundaryRay j)]
    let q := internalBlowupBoundaryPrimeEquiv hΦ b planeCenterRay c (planeBoundaryRay j)
    have hq : p j = ⟨q.val, (mem_boundaryPrimes.mp q.property).2⟩ :=
      Subtype.ext ((B(c)).coe_boundaryPrimeEmbedding q)
    rw [hq]
    exact (picardHom_markedBoundaryMap_single_eq_primeDivisorClass hΦ b planeCenterRay c
      (planeBoundaryRay j)).symm
  rw [hB.ofMul_inv_toInvertibleSheaf_eq_sum_primeDivisorClass p (fun x ↦ by
    rw [hp, range_boundaryPrimeEmbedding]
    rfl)]
  exact Finset.sum_congr rfl fun j _ ↦ hclass j

private theorem support_first_not_le_second (c : Fin 11 → ℂˣ) :
    ¬ (C(c, 0)).support ≤ (C(c, 1)).support := by
  intro h
  let : IsIntegral (C(c, 0)).subscheme := isIntegral_planeBlowup_line c 0
  let : IsIntegral (C(c, 1)).subscheme := isIntegral_planeBlowup_line c 1
  let : IsNoetherian (Y(c)) := isNoetherian_of_finiteType (Y(c) ↘ S)
  let h₀ := isEffectiveCartier_planeBlowup_line c 0
  let h₁ := isEffectiveCartier_planeBlowup_line c 1
  let x := (C(c, 0)).subschemeι (genericPoint (C(c, 0)).subscheme)
  have hx : x ∈ (C(c, 1)).support :=
    h (by rw [← SetLike.mem_coe, ← range_subschemeι]; exact Set.mem_range_self _)
  have he := (h₁.mem_support_iff_eq_subschemeι_genericPoint
    h₀.coheight_subschemeι_genericPoint).mp hx
  have hC : C(c, 0) = C(c, 1) := by
    rw [← (C(c, 0)).vanishingIdeal_closure_subschemeι_genericPoint,
      ← (C(c, 1)).vanishingIdeal_closure_subschemeι_genericPoint, he]
  have h := planeBlowup_line_intersection c 0 0 h₀ h₀
  have h' := planeBlowup_line_intersection c 1 1 h₁ h₁
  have hL := mk_toInvertibleSheaf_congr h₀ h₁ hC
  simp only [hL, ite_true] at h
  simp only [ite_true] at h'
  norm_num at h h'
  omega

private theorem classIntersectionNumber_second_canonical (c : Fin 11 → ℂˣ)
    (h₀ : (C(c, 0)).IsEffectiveCartier) (h₁ : (C(c, 1)).IsEffectiveCartier) :
    Chow.classIntersectionNumber ℂ (Y(c)) (class[h₁] * class[h₀]) (K(Y(c))) = -1 := by
  let hB : (B(c)).IsEffectiveCartier :=
    Fan.isEffectiveCartier_internalBlowupBoundary b planeCenterRay hΦ c
      ((Φ).isEffectiveCartier_boundaryIdeal hΦ hc (by simp))
  let F := Chow.intersectionBilinForm ℂ (Y(c))
  have hK : Additive.ofMul (K(Y(c))) = -(∑ j : Fin 3, L(c, j)) := by
    rw [← planeBlowup_boundary_class c hB, ofMul_inv, neg_neg,
      mk_toInvertibleSheaf_planeBlowup_boundary]
  have hp (i j : Fin 3) : F (L(c, i)) (L(c, j)) =
      if i = j then (![(-1 : ℤ), -2, -5] : Fin 3 → ℤ) i else 1 := by
    rw [← planeBlowup_line_class c i (isEffectiveCartier_planeBlowup_line c i),
      ← planeBlowup_line_class c j (isEffectiveCartier_planeBlowup_line c j),
      Chow.intersectionBilinForm_apply, toMul_ofMul, toMul_ofMul]
    exact planeBlowup_line_intersection c i j _ _
  have he : F (Additive.ofMul (class[h₁] * class[h₀])) (Additive.ofMul (K(Y(c)))) = -1 := by
    simp only [hK, ofMul_mul, planeBlowup_line_class, map_add, LinearMap.add_apply,
      map_neg, Fin.sum_univ_three, hp]
    decide
  simpa only [F, Chow.intersectionBilinForm_apply, toMul_ofMul] using he

section SecondContraction

variable {Z : Scheme} [Z.Over (Spec (.of ℂ))]
  [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of ℂ))] [Z.IsProjectiveOver ℂ] [IsIntegral Z]
  {c : Fin 11 → ℂˣ} (f : Y(c) ⟶ Z) [f.IsOver (Spec (.of ℂ))] [IsModification f]
  {p : Z} (hp : IsClosed ({p} : Set Z))

variable (e : Y(c) ≅ (Z.fromSpecResidueField p).ker.blowup)
  (he : e.hom ≫ (Z.fromSpecResidueField p).ker.blowupToBase = f)
  (hF : (Z.fromSpecResidueField p).ker.comap f = C(c, 0))

local notation "I" => Scheme.Hom.ker (Z.fromSpecResidueField p)

omit [IsModification f] in
include hp e he hF in
private theorem second_line_pullback_class
    (h₀ : (C(c, 0)).IsEffectiveCartier) (h₁ : (C(c, 1)).IsEffectiveCartier) :
    ∃ hC : ((C(c, 1)).map f).IsEffectiveCartier,
      pullback f class[hC] = class[h₁] * class[h₀] := by
  let J := vanishingIdeal (Closeds.mk (closure ({p} : Set Z)) isClosed_closure)
  have : IsNoetherian Z := isNoetherian_of_finiteType (Z ↘ S)
  have hIJ : I = J := Z.ker_fromSpecResidueField_eq_vanishingIdeal p
  let u : (I).blowup ≅ J.blowup := blowupIso (Iso.refl Z) (hIJ.trans (comap_id J).symm)
  have hu : (e ≪≫ u).hom ≫ J.blowupToBase = f := by
    rw [Iso.trans_hom, Category.assoc]
    dsimp only [u]
    rw [blowupIso_hom_blowupToBase, Iso.refl_hom, Category.comp_id, he]
  dsimp only [J] at hIJ
  let : IsIntegral (C(c, 1)).subscheme := isIntegral_planeBlowup_line c 1
  obtain ⟨hC, m, hm⟩ := h₁.exists_comap_map_eq_mul_pow_of_pointBlowdown ℂ hp (e ≪≫ u) hu
    (by rw [← hIJ, hF]; exact support_first_not_le_second c)
  rw [← hIJ, hF] at hm
  have hProd := TauCeti.isEffectiveCartier_mul h₁ (TauCeti.isEffectiveCartier_pow h₀ m)
  have hclass : pullback f class[hC] = class[h₁] * class[h₀] ^ m := by
    rw [pullback_inv, hC.pullback_mk_toInvertibleSheaf (hm.symm ▸ hProd),
      mk_toInvertibleSheaf_congr _ hProd hm,
      mk_toInvertibleSheaf_mul h₁ (TauCeti.isEffectiveCartier_pow h₀ m),
      mk_toInvertibleSheaf_pow, mul_inv_rev, inv_pow, mul_comm]
  have hcoord : pullback f class[hC] * class[h₀] ^ (-(m : ℤ)) = class[h₁] := by
    rw [hclass, zpow_neg, zpow_natCast, mul_inv_cancel_right]
  have h := f.classIntersectionNumber_pointBlowdown (k := ℂ) hp e he h₀ hF
    class[hC] 1 (-(m : ℤ)) 1
  dsimp only at h
  rw [hcoord, pullback_one, zpow_one, one_mul, Chow.classIntersectionNumber_one_right,
    mul_one, zero_sub, neg_neg, planeBlowup_line_intersection c 1 0 h₁ h₀] at h
  have hm₁ : m = 1 := by simpa using h.symm
  exact ⟨hC, by simpa only [hm₁, pow_one] using hclass⟩

omit [IsIntegral Z] [IsModification f] in
include hp e he hF in
private theorem second_line_self_intersection
    (h₀ : (C(c, 0)).IsEffectiveCartier) (h₁ : (C(c, 1)).IsEffectiveCartier)
    (hC : ((C(c, 1)).map f).IsEffectiveCartier)
    (hClass : pullback f class[hC] = class[h₁] * class[h₀]) :
    Chow.classIntersectionNumber ℂ Z class[hC] class[hC] = -1 := by
  have h := f.classIntersectionNumber_pointBlowdown (k := ℂ) hp e he h₀ hF
    class[hC] class[hC] (-1) (-1)
  have hcoord : pullback f class[hC] * class[h₀] ^ (-1 : ℤ) = class[h₁] := by
    rw [hClass, zpow_neg_one, mul_inv_cancel_right]
  dsimp only at h
  have hself : Chow.classIntersectionNumber ℂ (Y(c)) class[h₁] class[h₁] = -2 :=
    (planeBlowup_line_intersection c 1 1 h₁ h₁).trans (by decide)
  rw [hcoord, hself] at h
  omega

include hp e he hF in
/-- The image of the line that carries three internal centers is exceptional of the
first kind after the first boundary blowdown. -/
theorem isExceptionalCurveOfFirstKind_second_line_image
    [Scheme.IsRationalOver (Z ↘ S)] :
    ((C(c, 1)).map f).IsExceptionalCurveOfFirstKind := by
  let h₀ := isEffectiveCartier_planeBlowup_line c 0
  let h₁ := isEffectiveCartier_planeBlowup_line c 1
  obtain ⟨hC, hClass⟩ := second_line_pullback_class f hp e he hF h₀ h₁
  let C := (C(c, 1)).map f
  let : IsIntegral (C(c, 1)).subscheme := isIntegral_planeBlowup_line c 1
  let : IsIntegral C.subscheme := inferInstanceAs
    (IsIntegral ((C(c, 1)).subschemeι ≫ f).image)
  let : IsNoetherian Z := isNoetherian_of_finiteType (Z ↘ S)
  let := (Z ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let η : CodimensionOnePoint Z :=
    ⟨C.subschemeι (genericPoint C.subscheme), hC.coheight_subschemeι_genericPoint⟩
  have hZ := topologicalKrullDim_eq_of_smoothOfRelativeDimension (Z ↘ S) (n := 2)
  have hdim := topologicalKrullDim_vanishingIdeal_subscheme ℂ hZ η
  rw [C.vanishingIdeal_closure_subschemeι_genericPoint] at hdim
  have hProper : IsProper (C.subscheme ↘ S) := by rw [C.over_eq_subschemeι_comp]; infer_instance
  have : C.subscheme.IsCurveOver ℂ := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, hProper, hdim⟩
  have hself := second_line_self_intersection f hp e he hF h₀ h₁ hC hClass
  have hK := f.classIntersectionNumber_pullback_canonicalBundle_of_birational (k := ℂ)
    (IsModification.birationalOver f) class[hC]
  rw [hClass, classIntersectionNumber_second_canonical] at hK
  have hAdj := C.subschemeι.two_mul_genus_sub_two_eq_intersection_of_isRationalOver ℂ
  simp only [ker_subschemeι] at hAdj
  refine (hC.isExceptionalCurveOfFirstKind_iff_genus_eq_zero_and_classIntersectionNumber
    hZ.le).mpr ⟨?_, hself⟩
  rw [hself, ← hK] at hAdj
  have hg : C.subscheme.genus ℂ = 0 := by omega
  exact hg

omit [Z.Over (Spec (.of ℂ))] [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of ℂ))]
  [Z.IsProjectiveOver ℂ] [IsIntegral Z] [f.IsOver (Spec (.of ℂ))] [IsModification f] in
private theorem pullback_boundary_class_after_first
    (h₀ : (C(c, 0)).IsEffectiveCartier) (hB : (B(c)).IsEffectiveCartier)
    (hD : ((B(c)).map f).IsEffectiveCartier)
    (hTot : ((B(c)).map f).comap f = B(c) * C(c, 0)) :
    Additive.ofMul (pullback f class[hD]) = ∑ j : Fin 3, L(c, j) + L(c, 0) := by
  have hProd := TauCeti.isEffectiveCartier_mul hB h₀
  rw [pullback_inv, hD.pullback_mk_toInvertibleSheaf (hTot.symm ▸ hProd),
    mk_toInvertibleSheaf_congr _ hProd hTot, mk_toInvertibleSheaf_mul hB h₀, mul_inv_rev, mul_comm,
    ofMul_mul, planeBlowup_boundary_class c hB, planeBlowup_line_class c 0 h₀]

end SecondContraction

section FinalBoundary

variable {Z W : Scheme} [Z.Over (Spec (.of ℂ))] [W.Over (Spec (.of ℂ))]
  [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of ℂ))]
  [SmoothOfRelativeDimension 2 (W ↘ Spec (.of ℂ))]
  [Z.IsProjectiveOver ℂ] [W.IsProjectiveOver ℂ] [IsIntegral Z] [IsIntegral W]
  {c : Fin 11 → ℂˣ} (f : Y(c) ⟶ Z) [f.IsOver (Spec (.of ℂ))] [IsModification f]
  (g : Z ⟶ W) [g.IsOver (Spec (.of ℂ))] [IsModification g]
  {p : Z} {q : W} (hp : IsClosed ({p} : Set Z)) (hq : IsClosed ({q} : Set W))

local notation "E" => map (C(c, 1)) f
local notation "D" => map (B(c)) f
local notation "F" => map (D) g

variable (hF₀ : (Z.fromSpecResidueField p).ker.comap f = C(c, 0))
  (hF₁ : (W.fromSpecResidueField q).ker.comap g = (C(c, 1)).map f)

omit [Z.Over (Spec (.of ℂ))] [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of ℂ))]
  [Z.IsProjectiveOver ℂ] [W.IsProjectiveOver ℂ] [IsIntegral Z] [IsIntegral W]
  [f.IsOver (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))] in
include hp hq hF₀ hF₁ in
private theorem boundaryPrime_mem_final_line {x : W} (hx : x ∈ (F).boundaryPrimes) :
    x ∈ ((C(c, 2)).map (f ≫ g)).support := by
  have hB : x ∈ ((B(c)).map (f ≫ g)).support := by
    rw [map_comp]
    exact (mem_boundaryPrimes.mp hx).1
  rw [← SetLike.mem_coe, support_map, Closeds.coe_closure,
    ((f ≫ g).isClosedMap _ (B(c)).support.isClosed).closure_eq] at hB
  obtain ⟨y, hy, rfl⟩ := hB
  rw [support_planeBlowup_boundary c, Set.mem_iUnion] at hy
  obtain ⟨j, hj⟩ := hy
  have hne (r : W) (hr : IsClosed ({r} : Set W)) : r ∉ (F).boundaryPrimes := by
    intro h
    have hd := coheight_eq_of_isClosed_of_smoothOfRelativeDimension (n := 2) (W ↘ S) hr
    rw [(mem_boundaryPrimes.mp h).2] at hd
    norm_num at hd
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by
    fin_cases j <;> decide
  rcases hj' with rfl | rfl | rfl
  · rw [← hF₀, support_comap, Closeds.coe_preimage, Set.mem_preimage,
      Z.support_ker_fromSpecResidueField_of_isClosed hp] at hj
    have he : (f ≫ g) y = g p := by
      rw [Scheme.Hom.comp_apply, Set.mem_singleton_iff.mp hj]
    have hclosed : IsClosed ({g p} : Set W) := by
      simpa only [Set.image_singleton] using g.isClosedMap _ hp
    exact (hne _ hclosed (he ▸ hx)).elim
  · have hmem : f y ∈ (E).support := by
      rw [← SetLike.mem_coe, support_map, Closeds.coe_closure]
      exact subset_closure (Set.mem_image_of_mem _ hj)
    rw [← hF₁, support_comap, ← SetLike.mem_coe, Closeds.coe_preimage, Set.mem_preimage,
      W.support_ker_fromSpecResidueField_of_isClosed hq] at hmem
    have he : (f ≫ g) y = q := by rw [Scheme.Hom.comp_apply, Set.mem_singleton_iff.mp hmem]
    exact (hne _ hq (he ▸ hx)).elim
  · rw [← SetLike.mem_coe, support_map, Closeds.coe_closure]
    exact subset_closure (Set.mem_image_of_mem _ hj)

omit [Z.Over (Spec (.of ℂ))] [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of ℂ))]
  [Z.IsProjectiveOver ℂ] [IsIntegral Z] [IsIntegral W]
  [f.IsOver (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))] in
include hp hq hF₀ hF₁ in
private theorem final_boundary_eq_map_last_line
    [PrestableFamily ((((B(c)).map f).map g).subscheme ↘ Spec (.of ℂ))]
    (hD : (F).IsEffectiveCartier) :
    F = (C(c, 2)).map (f ≫ g) := by
  let J := (C(c, 2)).map (f ≫ g)
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (W ↘ S)
  let : IsIntegral (C(c, 2)).subscheme := isIntegral_planeBlowup_line c 2
  have : IsReduced J.subscheme := inferInstanceAs
    (IsReduced ((C(c, 2)).subschemeι ≫ (f ≫ g)).image)
  have hRed : IsReduced (F).subscheme :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := (F).subscheme ↘ S)).isReduced
  refine ((vanishingIdeal_support (I := F)).trans
    ((F).isReduced_subscheme_iff_radical_eq.mp hRed)).symm.trans ?_
  refine Eq.trans (congrArg vanishingIdeal ?_) (vanishingIdeal_support.trans
    (J.isReduced_subscheme_iff_radical_eq.mp inferInstance))
  apply le_antisymm
  · intro z hz
    obtain ⟨x, hx, hzx⟩ := hD.mem_support_iff_exists_codimensionOnePoint.mp hz
    have hx' : (x : W) ∈ (F).boundaryPrimes := mem_boundaryPrimes.mpr ⟨hx, x.property⟩
    exact hzx.mem_closed J.support.isClosed (boundaryPrime_mem_final_line f g hp hq hF₀ hF₁ hx')
  · dsimp only [J]
    rw [← map_comp]
    exact support_antitone (map_mono _ (boundary_le_line c 2))

omit [Z.Over (Spec (.of ℂ))] [W.Over (Spec (.of ℂ))]
  [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of ℂ))] [SmoothOfRelativeDimension 2 (W ↘ Spec (.of ℂ))]
  [Z.IsProjectiveOver ℂ] [W.IsProjectiveOver ℂ] [IsIntegral Z] [IsIntegral W]
  [f.IsOver (Spec (.of ℂ))] [IsModification f] [g.IsOver (Spec (.of ℂ))] [IsModification g] in
private theorem pullback_final_boundary_class
    (h₀ : (C(c, 0)).IsEffectiveCartier) (h₁ : (C(c, 1)).IsEffectiveCartier)
    (hE : (E).IsEffectiveCartier) (hD : (D).IsEffectiveCartier) (hF : (F).IsEffectiveCartier)
    (hTot₀ : (D).comap f = B(c) * C(c, 0)) (hTot₁ : (F).comap g = D * E)
    (hClass : pullback f class[hE] = class[h₁] * class[h₀]) :
    Additive.ofMul (pullback (f ≫ g) class[hF]) = weightedBoundaryClass c := by
  let hB : (B(c)).IsEffectiveCartier :=
    Fan.isEffectiveCartier_internalBlowupBoundary b planeCenterRay hΦ c
      ((Φ).isEffectiveCartier_boundaryIdeal hΦ hc (by simp))
  have hProd := TauCeti.isEffectiveCartier_mul hD hE
  have h : pullback g class[hF] = class[hD] * class[hE] := by
    rw [pullback_inv, hF.pullback_mk_toInvertibleSheaf (hTot₁.symm ▸ hProd),
      mk_toInvertibleSheaf_congr _ hProd hTot₁, mk_toInvertibleSheaf_mul hD hE,
      mul_inv_rev, mul_comm]
  rw [← pullback_comp, h, pullback_mul, ofMul_mul,
    pullback_boundary_class_after_first f h₀ hB hD hTot₀, hClass, ofMul_mul,
    planeBlowup_line_class c 1 h₁, planeBlowup_line_class c 0 h₀, Fin.sum_univ_three,
    weightedBoundaryClass_def]
  abel

omit [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of ℂ))] [Z.IsProjectiveOver ℂ] [IsIntegral Z] in
private theorem final_boundary_class_properties
    (hF : (F).IsEffectiveCartier) [IsIntegral (((B(c)).map f).map g).subscheme]
    (hClass : Additive.ofMul (pullback (f ≫ g) class[hF]) = weightedBoundaryClass c) :
    TauCeti.IsPrimitive (Additive.ofMul class[hF]) ∧
      class[hF].IsNef ℂ (W ↘ S) ∧
      Chow.classIntersectionNumber ℂ W class[hF] class[hF] = 0 := by
  let ψ : Additive (LineBundleClass W) →ₗ[ℤ] Additive (LineBundleClass (Y(c))) :=
    (pullbackHom (f ≫ g)).toAdditive.toIntLinearMap
  have hψ : ψ (Additive.ofMul class[hF]) = Additive.ofMul (pullback (f ≫ g) class[hF]) := by
    simp only [ψ, AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditive,
      Function.comp_apply, toMul_ofMul, pullbackHom_apply]
  have hprim : TauCeti.IsPrimitive (ψ (Additive.ofMul class[hF])) :=
    (hψ.trans hClass).symm ▸ isPrimitive_weightedBoundaryClass c
  have hsq := (f ≫ g).classIntersectionNumber_pullback_of_birational (k := ℂ)
    (IsModification.birationalOver (f ≫ g)) class[hF] class[hF]
  have hclass := congrArg Additive.toMul hClass
  simp only [toMul_ofMul] at hclass
  simp only [hclass, classIntersectionNumber_weightedBoundaryClass_self c] at hsq
  have : IsNoetherian W := isNoetherian_of_finiteType (W ↘ S)
  let := (W ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hW := topologicalKrullDim_eq_of_smoothOfRelativeDimension (W ↘ S) (n := 2)
  refine ⟨hprim.of_map, (hF.isNef_inv_mk_toInvertibleSheaf_iff hW).mpr ?_, hsq.symm⟩
  intro x hx
  have he := (hF.mem_support_iff_eq_subschemeι_genericPoint x.property).mp hx
  have hIdeal : vanishingIdeal ⟨closure {(x : W)}, isClosed_closure⟩ = F := by
    rw [he, (F).vanishingIdeal_closure_subschemeι_genericPoint]
  rw [primeDivisorClass_def, mk_toInvertibleSheaf_congr _ hF hIdeal, hsq.symm]

omit [Z.Over (Spec (.of ℂ))] [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of ℂ))]
  [Z.IsProjectiveOver ℂ] [IsIntegral Z] [f.IsOver (Spec (.of ℂ))] [IsModification f]
  [g.IsOver (Spec (.of ℂ))] [IsModification g] in
private theorem isCurveOver_final_boundary (hF : (F).IsEffectiveCartier)
    [IsIntegral (((B(c)).map f).map g).subscheme] : (F).subscheme.IsCurveOver ℂ := by
  have : IsNoetherian W := isNoetherian_of_finiteType (W ↘ S)
  let η : CodimensionOnePoint W :=
    ⟨(F).subschemeι (genericPoint (F).subscheme), hF.coheight_subschemeι_genericPoint⟩
  have hW := topologicalKrullDim_eq_of_smoothOfRelativeDimension (W ↘ S) (n := 2)
  have hdim := topologicalKrullDim_vanishingIdeal_subscheme ℂ hW η
  rw [(F).vanishingIdeal_closure_subschemeι_genericPoint] at hdim
  have hProper : IsProper ((F).subscheme ↘ S) := by
    rw [(F).over_eq_subschemeι_comp]
    infer_instance
  exact Scheme.isCurveOver_iff.mpr ⟨inferInstance, hProper, hdim⟩

omit [Z.Over (Spec (.of ℂ))] [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of ℂ))]
  [Z.IsProjectiveOver ℂ] [IsIntegral Z] [f.IsOver (Spec (.of ℂ))] [IsModification f]
  [g.IsOver (Spec (.of ℂ))] [IsModification g] in
private theorem normalizationGenus_final_boundary [Scheme.IsRationalOver (W ↘ S)]
    [((((B(c)).map f).map g).subscheme).IsCurveOver ℂ]
    [PrestableFamily ((((B(c)).map f).map g).subscheme ↘ Spec (.of ℂ))]
    (hF : (F).IsEffectiveCartier) (hKF : LineBundleClass.mk hF.toInvertibleSheaf = K(W))
    (hsq : Chow.classIntersectionNumber ℂ W class[hF] class[hF] = 0)
    (A : Scheme.NodalCycleNumbering
      (PEmpty.elim : PEmpty.{1} → ((F).subscheme ↘ S).smoothLocus) 1) :
    (F).subscheme.normalizationGenus ℂ = 0 := by
  let C := (F).subscheme
  let B := Chow.intersectionBilinForm ℂ W
  have hpair : Chow.classIntersectionNumber ℂ W class[hF] (K(W)) = 0 := by
    have h := (B (Additive.ofMul class[hF])).map_neg (Additive.ofMul class[hF])
    simp only [B, Chow.intersectionBilinForm_apply, toMul_ofMul, toMul_neg, hsq, neg_zero] at h
    simpa only [inv_inv, hKF] using h
  have hadj := (F).subschemeι.two_mul_genus_sub_two_eq_intersection_of_isRationalOver ℂ
  dsimp only at hadj
  simp only [ker_subschemeι, hsq, hpair, add_zero] at hadj
  have hgen : (F).subscheme.genus ℂ = 1 := by omega
  suffices hreg : ¬ IsRegular C by
    have hgen' : C.genus ℂ = 1 := hgen
    have h := C.normalizationGenus_lt_genus_of_not_isRegular (k := ℂ) hreg
    rw [hgen'] at h
    exact Nat.lt_one_iff.mp h
  intro hreg
  let x := (C.singularLocus ℂ).subschemeι (A.node 0)
  have hx : x ∈ (C.singularLocus ℂ).support :=
    (C.singularLocus ℂ).range_subschemeι.le (Set.mem_range_self _)
  have hsm := (C ↘ S).mem_smoothLocus_of_isRegularLocalRing_over_perfectField x
  exact (C.mem_support_singularLocus_iff_notMem_smoothLocus x).mp hx hsm

end FinalBoundary

/-- Contract the strict line with two centers and then the image of the strict
line with three centers. The image of the remaining line is an irreducible
one-node anticanonical boundary of normalization genus zero on a smooth
projective rational surface. Its class is primitive, nef and square zero. The map
from the original triangle remembers the ordered branches of the surviving node. -/
theorem exists_eleven_vertex_nodal_boundary (c : Fin 11 → ℂˣ) :
    letI : (Y(c)).Over S := ⟨(T(c)).toBase ≫ (Plane ↘ S)⟩
    ∃ (Z W : Scheme) (s : Z ⟶ S) (t : W ⟶ S) (f : Y(c) ⟶ Z) (g : Z ⟶ W) (p : Z) (q : W),
      letI : Z.Over S := ⟨s⟩
      letI : W.Over S := ⟨t⟩
      ∃ (_ : SmoothOfRelativeDimension 2 (W ↘ S)),
        IsIntegral W ∧ W.IsProjectiveOver ℂ ∧ Scheme.IsRationalOver t ∧
        f.IsOver S ∧ g.IsOver S ∧ IsModification f ∧ IsModification g ∧
        IsClosed ({p} : Set Z) ∧ IsClosed ({q} : Set W) ∧
        (Z.fromSpecResidueField p).ker.comap f = C(c, 0) ∧
        (W.fromSpecResidueField q).ker.comap g = (C(c, 1)).map f ∧
        ∃ (e : Y(c) ≅ (Z.fromSpecResidueField p).ker.blowup)
          (e' : Z ≅ (W.fromSpecResidueField q).ker.blowup),
          e.hom ≫ (Z.fromSpecResidueField p).ker.blowupToBase = f ∧
          e'.hom ≫ (W.fromSpecResidueField q).ker.blowupToBase = g ∧
          let D := ((B(c)).map f).map g
          D = (C(c, 2)).map (f ≫ g) ∧ IsIntegral D.subscheme ∧
          ∃ (hD : D.IsEffectiveCartier) (_ : PrestableFamily (D.subscheme ↘ S))
            (_ : PrestableFamily ((B(c)).subscheme ↘ S))
            (_ : D.subscheme.IsCurveOver ℂ),
            D.subscheme.normalizationGenus ℂ = 0 ∧
            LineBundleClass.mk hD.toInvertibleSheaf = K(W) ∧
            Additive.ofMul (pullback (f ≫ g) class[hD]) = weightedBoundaryClass c ∧
            TauCeti.IsPrimitive (Additive.ofMul class[hD]) ∧
            class[hD].IsNef ℂ (W ↘ S) ∧
            Chow.classIntersectionNumber ℂ W class[hD] class[hD] = 0 ∧
            ∃ (A : Scheme.NodalCycleNumbering
                (PEmpty.elim : PEmpty.{1} → ((B(c)).subscheme ↘ S).smoothLocus) 3)
              (A' : Scheme.NodalCycleNumbering
                (PEmpty.elim : PEmpty.{1} → (D.subscheme ↘ S).smoothLocus) 1)
              (u : (B(c)).subscheme ⟶ D.subscheme),
              u ≫ D.subschemeι = (B(c)).subschemeι ≫ f ≫ g ∧
              u.IsOrientedCycleSubdivision A A' := by
  obtain ⟨Z, s, f, p, hZsm, hZ, hZproj, hZrat, hf, hfmod, hp, hF₀, e, he,
    hD, hPreD, hPreB, hKD, hTot₀, A, A', u, hu, huSub⟩ := exists_first_boundary_contraction c
  let : Z.Over S := ⟨s⟩
  let : SmoothOfRelativeDimension 2 (Z ↘ S) := hZsm
  let : Smooth (Z ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsIntegral Z := hZ
  let : Z.IsProjectiveOver ℂ := hZproj
  let : Scheme.IsRationalOver (Z ↘ S) := hZrat
  let : f.IsOver S := hf
  let : IsModification f := hfmod
  let : PrestableFamily (((B(c)).map f).subscheme ↘ S) := hPreD
  let : PrestableFamily ((B(c)).subscheme ↘ S) := hPreB
  have hE := isExceptionalCurveOfFirstKind_second_line_image f hp e he hF₀
  obtain ⟨W, t, g, q, hW, hWproj, hWsm, hg, hgmod, hq, -, hF₁, -, e', he'⟩ :=
    hE.exists_smooth_projective_contraction (k := ℂ)
  let : W.Over S := ⟨t⟩
  let : SmoothOfRelativeDimension 2 (W ↘ S) := hWsm
  let : IsIntegral W := hW
  let : W.IsProjectiveOver ℂ := hWproj
  let : g.IsOver S := hg
  let : IsModification g := hgmod
  obtain ⟨U, hU, hgU, _⟩ := IsModification.exists_isIso_morphismRestrict (f := g)
  have hover : g ≫ t = Z ↘ S := hg.comp_over
  have hBir := hover ▸ g.birationalOver_of_isIso_morphismRestrict t U hU hgU
  let hRat : Scheme.IsRationalOver (W ↘ S) := hBir.symm.isRationalOver t (Z ↘ S)
  have hS : ((W.fromSpecResidueField q).ker.comap g).support ≤ ((B(c)).map f).support :=
    hF₁.symm ▸ support_antitone (map_mono _ (boundary_le_line c 1))
  obtain ⟨hF, hPreF, hKF, hTot₁, n, hn, hlen, A'', v, hv, hvSub⟩ :=
    hD.exists_numbering_of_exceptional_boundary_contraction A' hKD hq e' he' hS
  have hn' : n = 1 := by omega
  subst n
  let : PrestableFamily ((((B(c)).map f).map g).subscheme ↘ S) := hPreF
  have hLast := final_boundary_eq_map_last_line f g hp hq hF₀ hF₁ hF
  let : IsIntegral (C(c, 2)).subscheme := isIntegral_planeBlowup_line c 2
  let : IsIntegral (((B(c)).map f).map g).subscheme := hLast.symm ▸
    (inferInstance : IsIntegral ((C(c, 2)).subschemeι ≫ (f ≫ g)).image)
  let h₀ := isEffectiveCartier_planeBlowup_line c 0
  let h₁ := isEffectiveCartier_planeBlowup_line c 1
  obtain ⟨_, hClass⟩ := second_line_pullback_class f hp e he hF₀ h₀ h₁
  have hClass' := pullback_final_boundary_class f g h₀ h₁ hE.isEffectiveCartier hD hF
    hTot₀ (by simpa only [hF₁] using hTot₁) hClass
  obtain ⟨hprim, hnef, hsq⟩ := final_boundary_class_properties f g hF hClass'
  let hCurve := isCurveOver_final_boundary f g hF
  have hGen := normalizationGenus_final_boundary f g hF hKF hsq A''
  refine ⟨Z, W, s, t, f, g, p, q, hWsm, hW, hWproj, hRat, hf, hg, hfmod, hgmod,
    hp, hq, hF₀, hF₁, e, e', he, he', hLast, inferInstance, hF, hPreF, hPreB, hCurve, hGen, hKF,
    hClass', hprim, hnef, hsq, A, A'', u ≫ v, ?_, huSub.comp hvSub⟩
  rw [Category.assoc, hv, reassoc_of% hu]

end QPainleve.ElevenVertex

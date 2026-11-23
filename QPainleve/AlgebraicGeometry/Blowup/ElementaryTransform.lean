/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.RegularPair
public import QPainleve.RingTheory.Node.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
import TauCeti.AlgebraicGeometry.Blowup.BaseChange
import TauCeti.AlgebraicGeometry.Blowup.UniversalProperty
import TauCeti.RingTheory.Regular.Pair

/-!
# Blowup charts for an elementary transformation

Over an affine base with parameter `t`, the elementary transformation has formula
`z' = z/t`. Near the two opposite centers use `x = z` and `y = 1/z'`, so the
chart common to the two blowups has equation `xy = t`. Its two coordinates cut
out the respective exceptional divisors. Each blowup also has a chart of the
base parameter with coordinate `Z = x/t` or `Z = y/t`. On its overlap with the
common chart this is the reciprocal of the other node coordinate.

The Rees blowups here compare to the corresponding affine pieces of a scheme
blowup by `Scheme.IdealSheafData.exists_isPullback_toSpecCoeff_reesAlgebra`.

This is the affine calculation for the elementary transformation in
[Gross, Hacking and Keel, *Birational geometry of cluster algebras*, §3.1]
(https://arxiv.org/html/1309.2573v2#S3.SS1).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial RingTheory.Sequence reesAlgebra
open TauCeti TauCeti.NodeAlgebra TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

namespace QPainleve

variable {R : Type*} [CommRing R] (t : R)

local notation "x" => (X : R[X])
local notation "I" => (Ideal.span {x, C t} : Ideal R[X])
local notation "f" => (C x * X - C (C t))
local notation "B" => AdjoinRoot f
local notation "N" => NodeAlgebra R t
local notation "xB" => AdjoinRoot.of f x
local notation "yB" => AdjoinRoot.root f

private def pivotNodeToChart (i : Fin 2) : N →ₐ[R] B :=
  lift t (if i = 0 then xB else yB) (if i = 0 then yB else xB) (by
    have h : xB * yB = algebraMap R B t := by
      -- The base scalar enters the quotient as a constant polynomial.
      change xB * yB = AdjoinRoot.of f (C t)
      exact AdjoinRoot.algebraMap_mul_root_eq x (C t)
    fin_cases i
    · simpa using h
    · simpa [mul_comm] using h)

/-- The chart equation `xY = t` is the node equation over the base `R`.
The polynomial variable of the base affine line is coordinate `i`. -/
def elementaryTransformNodeEquiv (i : Fin 2) : B ≃ₐ[R] N := by
  let g := AdjoinRoot.liftAlgHom f (aeval (coord t i)) (coord t (1 - i)) (by
    simpa only [eval₂_sub, eval₂_mul, eval₂_C, eval₂_X, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, aeval_X, aeval_C, sub_eq_zero] using coord_mul_coord_one_sub t i)
  refine AlgEquiv.ofAlgHom g (pivotNodeToChart t i) ?_ ?_
  · apply NodeAlgebra.hom_ext
    · fin_cases i <;> simp [g, pivotNodeToChart]
    · fin_cases i <;> simp [g, pivotNodeToChart]
  · fin_cases i <;> ext <;> simp [g, pivotNodeToChart]

/-- The base affine-line variable becomes the chosen coordinate on the node. -/
@[simp]
theorem elementaryTransformNodeEquiv_of (i : Fin 2) (p : R[X]) :
    elementaryTransformNodeEquiv t i (AdjoinRoot.of f p) = aeval (coord t i) p := by
  simp [elementaryTransformNodeEquiv]

/-- The root, which is the ratio of the base parameter to the affine-line
variable, becomes the other coordinate on the node. -/
@[simp]
theorem elementaryTransformNodeEquiv_root (i : Fin 2) :
    elementaryTransformNodeEquiv t i yB = coord t (1 - i) := by
  simp [elementaryTransformNodeEquiv]

private theorem isWeaklyRegular_pivot (ht : IsSMulRegular R t) :
    IsWeaklyRegular R[X] [x, C t] := by
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff,
    TauCeti.isSMulRegular_quotSMulTop_iff]
  refine ⟨isRegular_X.left, fun p q h ↦ ?_⟩
  rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top,
    Ideal.mem_span_singleton, X_dvd_iff]
  have hc := congrArg (fun p : R[X] ↦ p.coeff 0) h
  simp only [smul_eq_mul, coeff_C_mul, coeff_X_mul_zero] at hc
  exact ht (hc.symm.trans (mul_zero _).symm)

private theorem isWeaklyRegular_pivot_swap (ht : IsSMulRegular R t) :
    IsWeaklyRegular R[X] [C t, x] := by
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
  refine ⟨fun p q h ↦ ?_, ?_⟩
  · ext n
    exact ht (by
      simpa only [smul_eq_mul, coeff_C_mul] using congrArg (fun p : R[X] ↦ p.coeff n) h)
  · have h := (isWeaklyRegular_pivot t ht).isSMulRegular_quotSMulTop_pow_swap 1 1
    rw [pow_one (C t), pow_one x] at h
    exact h

local notation "Bl" => Proj (grade I)
local notation "NodeSpec" => Spec (CommRingCat.of N)
local notation "Specₐ" g:max => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom g))
local notation "e(" i ")" => elementaryTransformNodeEquiv t i
local notation "hX" => (Ideal.subset_span (by simp : x ∈ ({x, C t} : Set R[X])))
local notation "hC" => (Ideal.subset_span (by simp : C t ∈ ({x, C t} : Set R[X])))

/-- Embed the common node chart into the blowup of `(x,t)`, using either
node coordinate for the original affine-line coordinate. -/
def elementaryTransformNodeChart (ht : IsSMulRegular R t) (i : Fin 2) : NodeSpec ⟶ Bl :=
  Specₐ (e(i)).toAlgHom ≫ affineBlowupChartOfSpanPair rfl (isWeaklyRegular_pivot t ht)

instance (ht : IsSMulRegular R t) (i : Fin 2) :
    IsOpenImmersion (elementaryTransformNodeChart t ht i) := by
  unfold elementaryTransformNodeChart
  have : IsIso (Specₐ (e(i)).toAlgHom) :=
    (Scheme.Spec.mapIso (e(i)).toRingEquiv.toCommRingCatIso.op).isIso_hom
  infer_instance

/-- In either identification, the node chart is the standard chart of `x` in
the Rees blowup. -/
@[simp]
theorem opensRange_elementaryTransformNodeChart (ht : IsSMulRegular R t) (i : Fin 2) :
    (elementaryTransformNodeChart t ht i).opensRange =
      Proj.basicOpen (grade I) (monomialDegreeOne hX) := by
  unfold elementaryTransformNodeChart
  have : IsIso (Specₐ (e(i)).toAlgHom) :=
    (Scheme.Spec.mapIso (e(i)).toRingEquiv.toCommRingCatIso.op).isIso_hom
  rw [Scheme.Hom.opensRange_comp_of_isIso, opensRange_affineBlowupChartOfSpanPair]

local notation "g" => (C (C t : R[X]) * X - C x)
local notation "B'" => AdjoinRoot g
local notation "zB" => AdjoinRoot.root g

/-- The other chart has equation `tZ = x`, so its coordinate ring is the
polynomial ring in `Z` over the base. -/
def elementaryTransformOuterEquiv : B' ≃ₐ[R] R[X] := by
  let φ := AdjoinRoot.liftAlgHom g (aeval (C t * x)) x (by simp)
  refine AlgEquiv.ofAlgHom φ (aeval zB) ?_ ?_
  · apply Polynomial.algHom_ext
    simp [φ]
  · ext
    · suffices algebraMap R B' t * zB = AdjoinRoot.of g x by
        simpa [φ] using this
      -- View the scalar as a coefficient of the chart equation.
      change AdjoinRoot.of g (C t) * zB = AdjoinRoot.of g x
      exact AdjoinRoot.algebraMap_mul_root_eq (C t) x
    · simp [φ]

/-- The original affine-line coordinate is `tZ` on the outer chart. -/
@[simp]
theorem elementaryTransformOuterEquiv_of (p : R[X]) :
    elementaryTransformOuterEquiv t (AdjoinRoot.of g p) = aeval (C t * x) p := by
  simp [elementaryTransformOuterEquiv]

/-- The root, representing the ratio `x/t`, is the variable on the outer chart. -/
@[simp]
theorem elementaryTransformOuterEquiv_root : elementaryTransformOuterEquiv t zB = x := by
  simp [elementaryTransformOuterEquiv]

private theorem pivot_span_swap : Ideal.span {C t, x} = I := by rw [Set.pair_comm]

local notation "hI" => pivot_span_swap t
local notation "e'" => elementaryTransformOuterEquiv t

/-- The chart of the base parameter in the blowup of `(x,t)`, with affine-line
variable `Z = x/t`. -/
def elementaryTransformOuterChart (ht : IsSMulRegular R t) : Spec (.of R[X]) ⟶ Bl :=
  Specₐ (e').toAlgHom ≫ affineBlowupChartOfSpanPair hI (isWeaklyRegular_pivot_swap t ht)

instance (ht : IsSMulRegular R t) : IsOpenImmersion (elementaryTransformOuterChart t ht) := by
  unfold elementaryTransformOuterChart
  have : IsIso (Specₐ (e').toAlgHom) :=
    (Scheme.Spec.mapIso (e').toRingEquiv.toCommRingCatIso.op).isIso_hom
  infer_instance

/-- The outer chart is the standard chart of `t` in the Rees blowup. -/
@[simp]
theorem opensRange_elementaryTransformOuterChart (ht : IsSMulRegular R t) :
    (elementaryTransformOuterChart t ht).opensRange =
      Proj.basicOpen (grade I) (monomialDegreeOne hC) := by
  unfold elementaryTransformOuterChart
  have : IsIso (Specₐ (e').toAlgHom) :=
    (Scheme.Spec.mapIso (e').toRingEquiv.toCommRingCatIso.op).isIso_hom
  rw [Scheme.Hom.opensRange_comp_of_isIso, opensRange_affineBlowupChartOfSpanPair]

/-- The node chart and the outer chart cover the blowup. -/
theorem sup_opensRange_elementaryTransformCharts (ht : IsSMulRegular R t) (i : Fin 2) :
    (elementaryTransformNodeChart t ht i).opensRange ⊔
      (elementaryTransformOuterChart t ht).opensRange = ⊤ := by
  simpa only [opensRange_elementaryTransformNodeChart, opensRange_elementaryTransformOuterChart,
    opensRange_affineBlowupChartOfSpanPair] using
    sup_opensRange_affineBlowupChartOfSpanPair rfl
      (isWeaklyRegular_pivot t ht) (isWeaklyRegular_pivot_swap t ht)

local notation "π" => Proj.toSpecCoeff (grade I)

/-- The two projections from the node chart to the original affine-line
patches are given by the two node coordinates. -/
@[reassoc]
theorem elementaryTransformNodeChart_toSpec (ht : IsSMulRegular R t) (i : Fin 2) :
    elementaryTransformNodeChart t ht i ≫ π = Specₐ (aeval (R := R) (coord t i)) := by
  rw [toSpecCoeff_reesAlgebra, RingEquiv.toCommRingCatIso_hom, elementaryTransformNodeChart,
    Category.assoc, affineBlowupChartOfSpanPair_toSpecZero,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact elementaryTransformNodeEquiv_of t i p

/-- The blowup projection on the outer chart sends the original coordinate `x`
to `tZ`. -/
@[reassoc]
theorem elementaryTransformOuterChart_toSpec (ht : IsSMulRegular R t) :
    elementaryTransformOuterChart t ht ≫ π = Specₐ (aeval (R := R) (C t * x)) := by
  rw [toSpecCoeff_reesAlgebra, RingEquiv.toCommRingCatIso_hom, elementaryTransformOuterChart,
    Category.assoc, affineBlowupChartOfSpanPair_toSpecZero,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact elementaryTransformOuterEquiv_of t p

/-- On the node chart the overlap with the outer chart is obtained by inverting
the other node coordinate. -/
@[simp]
theorem elementaryTransformNodeChart_preimage_basicOpen (ht : IsSMulRegular R t) (i : Fin 2) :
    elementaryTransformNodeChart t ht i ⁻¹ᵁ
        Proj.basicOpen (grade I) (monomialDegreeOne hC) =
      (PrimeSpectrum.basicOpen (coord t (1 - i)) : (NodeSpec).Opens) := by
  rw [elementaryTransformNodeChart,
    Scheme.Hom.comp_preimage, affineBlowupChartOfSpanPair_preimage_basicOpen,
    SpecMap_preimage_basicOpen, CommRingCat.ofHom_apply]
  -- Read the bundled coefficient-ring map as the chart equivalence.
  change PrimeSpectrum.basicOpen (e(i) yB) = _
  rw [elementaryTransformNodeEquiv_root]

/-- On the outer chart the overlap with the node chart is the punctured
affine line in the variable `Z`. -/
@[simp]
theorem elementaryTransformOuterChart_preimage_basicOpen (ht : IsSMulRegular R t) :
    elementaryTransformOuterChart t ht ⁻¹ᵁ
        Proj.basicOpen (grade I) (monomialDegreeOne hX) =
      (PrimeSpectrum.basicOpen x : (Spec (.of R[X])).Opens) := by
  rw [elementaryTransformOuterChart,
    Scheme.Hom.comp_preimage, affineBlowupChartOfSpanPair_preimage_basicOpen,
    SpecMap_preimage_basicOpen, CommRingCat.ofHom_apply]
  -- Read the bundled coefficient-ring map as the chart equivalence.
  change PrimeSpectrum.basicOpen (e' zB) = _
  rw [elementaryTransformOuterEquiv_root]

/-- On the common chart, the exceptional ideal of the blowup in which `x`
corresponds to coordinate `i` is generated by that coordinate. -/
@[simp]
theorem affineBlowupExceptionalIdeal_comap_elementaryTransformNodeChart
    (ht : IsSMulRegular R t) (i : Fin 2) :
    (affineBlowupExceptionalIdeal R[X] I).comap (elementaryTransformNodeChart t ht i) =
      ofIdealTop ((Ideal.span {coord t i}).map (Scheme.ΓSpecIso (.of N)).inv.hom) := by
  rw [elementaryTransformNodeChart, comap_comp,
    affineBlowupExceptionalIdeal_comap_chartOfSpanPair, comap_ofIdealTop_map_ΓSpecIso_inv,
    Ideal.map_span, Set.image_singleton]
  -- The image of the generator is computed in the coordinate ring.
  change ofIdealTop ((Ideal.span {e(i) xB}).map _) = _
  rw [elementaryTransformNodeEquiv_of, aeval_X]

/-- On the outer chart the exceptional ideal is generated by the base
parameter. -/
@[simp]
theorem affineBlowupExceptionalIdeal_comap_elementaryTransformOuterChart
    (ht : IsSMulRegular R t) :
    (affineBlowupExceptionalIdeal R[X] I).comap (elementaryTransformOuterChart t ht) =
      ofIdealTop ((Ideal.span {C t}).map (Scheme.ΓSpecIso (.of R[X])).inv.hom) := by
  rw [elementaryTransformOuterChart, comap_comp,
    affineBlowupExceptionalIdeal_comap_chartOfSpanPair, comap_ofIdealTop_map_ΓSpecIso_inv,
    Ideal.map_span, Set.image_singleton]
  -- The image of the generator is computed in the coordinate ring.
  change ofIdealTop ((Ideal.span {e' (AdjoinRoot.of g (C t))}).map _) = _
  rw [elementaryTransformOuterEquiv_of, aeval_C, Polynomial.algebraMap_eq]

local notation "L(" i ")" => Localization.Away (coord t (1 - i))
local notation "ι(" i ")" => Spec.map (CommRingCat.ofHom (algebraMap N (L(i))))

/-- The transition from the node open to the punctured outer chart sends `Z`
to the reciprocal of the other node coordinate. The two maps into the Rees blowup agree
on this overlap. -/
@[reassoc]
theorem elementaryTransformNodeChart_overlap (ht : IsSMulRegular R t) (i : Fin 2) :
    ι(i) ≫ elementaryTransformNodeChart t ht i =
      Specₐ (aeval (R := R) (IsLocalization.Away.invSelf (S := L(i)) (coord t (1 - i)))) ≫
        elementaryTransformOuterChart t ht := by
  -- The two maps lift the same affine projection with Cartier extended center.
  apply projReesAlgebra_hom_ext
  · rw [← toSpecCoeff_reesAlgebra I, Category.assoc, Category.assoc,
      elementaryTransformNodeChart_toSpec, elementaryTransformOuterChart_toSpec]
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have he :
        (Algebra.algHom R N (L(i))).comp (aeval (coord t i)) =
          (aeval (IsLocalization.Away.invSelf (S := L(i)) (coord t (1 - i)))).comp
            (aeval (C t * x)) := by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply, aeval_X, map_mul, aeval_C]
      rw [IsScalarTower.algebraMap_apply R N (L(i)), ← coord_mul_coord_one_sub t i, map_mul]
      rw [mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
      rfl
    exact congrArg (fun a : R[X] →ₐ[R] L(i) ↦ Specₐ a) he
  · rw [Category.assoc, comap_comp _ (ι(i)),
      comap_comp _ (elementaryTransformNodeChart t ht i), ← affineBlowupExceptionalIdeal_def]
    exact (isEffectiveCartier_affineBlowupExceptionalIdeal.comap
      (elementaryTransformNodeChart t ht i)).comap (ι(i))

end QPainleve

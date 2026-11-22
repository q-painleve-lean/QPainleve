/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.LinearAlgebra.BilinearForm.BaseChange
public import TauCeti.LinearAlgebra.BilinearForm.Characteristic
public import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
public import TauCeti.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
import TauCeti.LinearAlgebra.BilinearForm.LinearIndependent
import TauCeti.LinearAlgebra.BilinearForm.Modular
import TauCeti.LinearAlgebra.Submodule.Compl

/-!
# Orthogonal reduction at a primitive isotropic vector

For an isotropic vector `δ` in an integral lattice, the form descends to `δᗮ / ℤδ`.
If `δ` pairs to one with a vector `f`, this quotient is isometric to the orthogonal
complement of the plane spanned by `δ` and `f`. This gives the rank, unimodularity and
signature of the quotient. A characteristic `δ` makes the quotient even.

The quotient construction uses Mathlib's `LinearMap.IsRefl.liftQ₂`. The plane splitting
uses Tau Ceti's Gram matrix criteria for linear independence and `1`-modularity, and
`LinearMap.BilinForm.isCompl_orthogonal_of_restrict_bijective`.
The quotient isometry uses `Submodule.isCompl_comap_subtype_iff` and
`Submodule.quotientEquivOfIsCompl` on the orthogonal complement of `δ`.
-/

public section

open Submodule LinearMap
open scoped TensorProduct

namespace LinearMap.BilinForm

section Quotient

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (B : LinearMap.BilinForm R M)

/-- The orthogonal quotient `Sᗮ / (S ∩ Sᗮ)`; for isotropic `S` the denominator is `S`. -/
abbrev OrthogonalQuotient (S : Submodule R M) :=
  B.orthogonal S ⧸ S.comap (B.orthogonal S).subtype

/-- The form on the orthogonal quotient induced by a symmetric form. -/
def orthogonalQuotientForm (hB : B.IsSymm) (S : Submodule R M) :
    LinearMap.BilinForm R (B.OrthogonalQuotient S) :=
  (hB.restrict _).isRefl.liftQ₂ (B.restrict (B.orthogonal S)) _ fun x hx ↦ by
    ext y
    exact (B.mem_orthogonal_iff.mp y.property) x hx

/-- The induced form pairs two classes by pairing their representatives. -/
@[simp]
theorem orthogonalQuotientForm_mk (hB : B.IsSymm) (S : Submodule R M)
    (x y : B.orthogonal S) :
    B.orthogonalQuotientForm hB S (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      B x y := (rfl)

/-- The induced form on the orthogonal quotient is symmetric. -/
theorem isSymm_orthogonalQuotientForm (hB : B.IsSymm) (S : Submodule R M) :
    (B.orthogonalQuotientForm hB S).IsSymm := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := (S.comap (B.orthogonal S).subtype).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (S.comap (B.orthogonal S).subtype).mkQ_surjective y
  simpa only [mkQ_apply, orthogonalQuotientForm_mk] using hB.eq x.val y.val

end Quotient

local notation "plane[" R ", " δ ", " f "]" => span R ({δ, f} : Set _)

section Plane

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {B : LinearMap.BilinForm R M} (hB : B.IsSymm) {δ f : M}

include hB in
private theorem isotropicPlane_gram (hδ : B δ δ = 0) (hδf : B δ f = 1) (i j : Fin 2) :
    B (![δ, f] i) (![δ, f] j) = (1 : R) * (!![0, 1; 1, B f f] : Matrix (Fin 2) (Fin 2) R) i j := by
  fin_cases i <;> fin_cases j <;> simp [hδ, hδf, hB.eq f δ]

private noncomputable def isotropicPlaneBasis (hδ : B δ δ = 0) (hδf : B δ f = 1) :
    Module.Basis (Fin 2) R (plane[R, δ, f]) :=
  (Module.Basis.span (linearIndependent_of_isUnit_det (nonZeroDivisors R).one_mem
    (isotropicPlane_gram hB hδ hδf) (by simp [Matrix.det_fin_two_of]))).map
    (LinearEquiv.ofEq _ _ (by rw [Matrix.range_cons_cons_empty]))

/-- An isotropic vector and a vector pairing to one with it span a unimodular plane, which
splits off orthogonally. -/
theorem IsSymm.isCompl_span_pair_orthogonal_of_isotropic (hB : B.IsSymm)
    (hδ : B δ δ = 0) (hδf : B δ f = 1) :
    IsCompl (plane[R, δ, f]) (B.orthogonal (plane[R, δ, f])) := by
  have hperf := isModular_one_iff.mp (isModular_restrict_span_range (nonZeroDivisors R).one_mem
    (isotropicPlane_gram hB hδ hδf) (by simp [Matrix.det_fin_two_of]))
  rw [Matrix.range_cons_cons_empty] at hperf
  exact B.isCompl_orthogonal_of_restrict_bijective _ (hB.restrict _) hperf.bijective_left

private theorem orthogonal_plane_le_orthogonal_line :
    B.orthogonal (plane[R, δ, f]) ≤ B.orthogonal (R ∙ δ) :=
  B.orthogonal_le (span_mono (Set.singleton_subset_iff.mpr (by simp)))

include hB in
private theorem isCompl_line_orthogonalPlane (hδ : B δ δ = 0) (hδf : B δ f = 1) :
    IsCompl ((R ∙ δ).comap (B.orthogonal (R ∙ δ)).subtype)
      ((B.orthogonal (plane[R, δ, f])).comap (B.orthogonal (R ∙ δ)).subtype) := by
  have hline : R ∙ δ ≤ B.orthogonal (R ∙ δ) := by
    simp [span_singleton_le_iff_mem, orthogonal, hδ]
  rw [Submodule.isCompl_comap_subtype_iff, inf_eq_right.mpr hline,
    inf_eq_right.mpr orthogonal_plane_le_orthogonal_line]
  refine ⟨(hB.isCompl_span_pair_orthogonal_of_isotropic hδ hδf).disjoint.mono_left
    (span_mono (by simp)), ?_⟩
  intro x hx
  have hδx := B.mem_orthogonal_iff.mp hx δ (mem_span_singleton_self δ)
  have hmem : x - B f x • δ ∈ B.orthogonal (plane[R, δ, f]) := by
    simp [orthogonal, sub_right, hδx, hδ, ← hB.eq δ f, hδf]
  exact mem_sup.mpr ⟨B f x • δ, smul_mem _ _ (mem_span_singleton_self δ), _, hmem,
    by rw [add_comm, sub_add_cancel]⟩

/-- The orthogonal complement of `span {δ, f}` maps isometrically onto `δᗮ / Rδ` by taking
quotient classes. -/
noncomputable def IsSymm.isometryEquivOrthogonalQuotient (hB : B.IsSymm)
    (hδ : B δ δ = 0) (hδf : B δ f = 1) :
    (B.restrict (B.orthogonal (plane[R, δ, f]))).IsometryEquiv
      (B.orthogonalQuotientForm hB (R ∙ δ)) where
  toLinearEquiv := (comapSubtypeEquivOfLe orthogonal_plane_le_orthogonal_line).symm.trans
    (quotientEquivOfIsCompl _ _ (isCompl_line_orthogonalPlane hB hδ hδf)).symm
  map_app' x y := orthogonalQuotientForm_mk B hB (R ∙ δ)
    ⟨x.val, orthogonal_plane_le_orthogonal_line x.property⟩
    ⟨y.val, orthogonal_plane_le_orthogonal_line y.property⟩

/-- The plane-complement isometry sends a vector to its quotient class. -/
@[simp]
theorem IsSymm.isometryEquivOrthogonalQuotient_apply (hB : B.IsSymm)
    (hδ : B δ δ = 0) (hδf : B δ f = 1) (x : B.orthogonal (plane[R, δ, f])) :
    hB.isometryEquivOrthogonalQuotient hδ hδf x =
      Submodule.Quotient.mk ⟨x.val, B.orthogonal_le (span_mono (by simp)) x.property⟩ := (rfl)

/-- A perfect symmetric form induces a perfect pairing on the quotient by an isotropic vector
that pairs to one with some vector. -/
theorem IsSymm.isPerfPair_orthogonalQuotientForm (hB : B.IsSymm) [B.IsPerfPair]
    (hδ : B δ δ = 0) (hδf : B δ f = 1) :
    (B.orthogonalQuotientForm hB (R ∙ δ)).IsPerfPair := by
  have hsplit := hB.isCompl_span_pair_orthogonal_of_isotropic hδ hδf
  have hsep : B.SeparatingRight := (inferInstance : B.IsPerfPair).separatingRight
  have hC := B.isPerfPair_restrict_of_isCompl_orthogonal hB (B.orthogonal (plane[R, δ, f])) (by
    rw [B.orthogonal_orthogonal_of_isCompl hB.isRefl hsep _ hsplit]
    exact hsplit.symm)
  let e := hB.isometryEquivOrthogonalQuotient hδ hδf
  exact LinearMap.IsPerfPair.congr _ e.toLinearEquiv.symm e.toLinearEquiv.symm _
    (LinearMap.ext₂ fun x y ↦ e.map_app y x)

end Plane

section Integral

variable {M : Type*} [AddCommGroup M]
variable {B : LinearMap.BilinForm ℤ M} (hB : B.IsSymm) {δ f : M}

/-- The quotient of the isotropic vector's orthogonal complement by its line has rank two
less than the ambient lattice. -/
theorem IsSymm.finrank_orthogonalQuotient_add_two (hB : B.IsSymm)
    [Module.Finite ℤ M] [Module.IsTorsionFree ℤ M]
    (hδ : B δ δ = 0) (hδf : B δ f = 1) :
    Module.finrank ℤ (B.OrthogonalQuotient (ℤ ∙ δ)) + 2 = Module.finrank ℤ M := by
  have hP : Module.finrank ℤ (plane[ℤ, δ, f]) = 2 := by
    rw [Module.finrank_eq_card_basis (isotropicPlaneBasis hB hδ hδf), Fintype.card_fin]
  have hsplit := (Submodule.prodEquivOfIsCompl _ _
    (hB.isCompl_span_pair_orthogonal_of_isotropic hδ hδf)).finrank_eq
  rw [Module.finrank_prod, hP, (hB.isometryEquivOrthogonalQuotient hδ hδf).toLinearEquiv.finrank_eq]
    at hsplit
  simpa only [Nat.add_comm] using hsplit

/-- The quotient of the orthogonal complement of a characteristic vector has even norms. -/
theorem IsCharacteristic.even_orthogonalQuotientForm (hchar : B.IsCharacteristic δ)
    (hB : B.IsSymm) (x : B.OrthogonalQuotient (ℤ ∙ δ)) :
    Even (B.orthogonalQuotientForm hB (ℤ ∙ δ) x x) := by
  obtain ⟨y, rfl⟩ := ((ℤ ∙ δ).comap (B.orthogonal (ℤ ∙ δ)).subtype).mkQ_surjective x
  have hy : B δ y = 0 := B.mem_orthogonal_iff.mp y.property δ (mem_span_singleton_self δ)
  rw [mkQ_apply, orthogonalQuotientForm_mk, even_iff_two_dvd]
  simpa [hy] using dvd_neg.mpr (isCharacteristic_iff.mp hchar y)

section Signature

variable (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

include hB in
private theorem sig_isotropicPlane (hδ : B δ δ = 0) (hδf : B δ f = 1) :
    let Q := ((B.restrict (plane[ℤ, δ, f])).baseChange K).toQuadraticMap
    sigPos Q = 1 ∧ sigNeg Q = 1 := by
  let P := plane[ℤ, δ, f]
  let d : P := ⟨δ, subset_span (by simp)⟩
  let t : P := ⟨f, subset_span (by simp)⟩
  let Q := ((B.restrict P).baseChange K).toQuadraticMap
  suffices sigPos Q = 1 ∧ sigNeg Q = 1 from this
  have hfinite : Module.Finite ℤ P := Module.Finite.of_basis (isotropicPlaneBasis hB hδ hδf)
  have hfree : Module.Free ℤ P := Module.Free.of_basis (isotropicPlaneBasis hB hδ hδf)
  -- The vectors `(±1 - f²)δ + 2f` have squares `±4`.
  have hnorm (a : ℤ) :
      Q ((1 : K) ⊗ₜ[ℤ] ((a - B f f) • d + (2 : ℤ) • t)) = (4 : K) * a := by
    have hdd : B.restrict P d d = 0 := hδ
    have hdt : B.restrict P d t = 1 := hδf
    have htd : B.restrict P t d = 1 := (hB.eq f δ).trans hδf
    have htt : B.restrict P t t = B f f := rfl
    have hZ : B.restrict P ((a - B f f) • d + (2 : ℤ) • t)
        ((a - B f f) • d + (2 : ℤ) • t) = 4 * a := by
      simp only [add_left, add_right, smul_left, smul_right, hdd, hdt, htd, htt]
      ring
    simp only [Q, BilinMap.toQuadraticMap_apply, baseChange_tmul, one_mul, hZ]
    simp [Algebra.smul_def]
  have hpos : 0 < sigPos Q := by
    refine Nat.pos_of_ne_zero fun h ↦ ?_
    have hh := (QuadraticForm.forall_nonpos_iff_sigPos_eq_zero Q).mpr h
      ((1 : K) ⊗ₜ[ℤ] ((1 - B f f) • d + (2 : ℤ) • t))
    norm_num [hnorm] at hh
  have hneg : 0 < sigNeg Q := by
    refine Nat.pos_of_ne_zero fun h ↦ ?_
    have hh := (QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero Q).mpr h
      ((1 : K) ⊗ₜ[ℤ] ((-1 - B f f) • d + (2 : ℤ) • t))
    norm_num [hnorm] at hh
  have hrank : Module.finrank K (K ⊗[ℤ] P) = 2 := by
    rw [Module.finrank_baseChange, Module.finrank_eq_card_basis (isotropicPlaneBasis hB hδ hδf),
      Fintype.card_fin]
  have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  omega

private noncomputable def isotropicPlaneProdIsometry (hδ : B δ δ = 0) (hδf : B δ f = 1) :
    ((B.restrict (plane[ℤ, δ, f])).prod
      (B.restrict (B.orthogonal (plane[ℤ, δ, f])))).IsometryEquiv B where
  toLinearEquiv := Submodule.prodEquivOfIsCompl _ _
    (hB.isCompl_span_pair_orthogonal_of_isotropic hδ hδf)
  map_app' x y := by
    have hxy := B.mem_orthogonal_iff.mp y.2.property x.1 x.1.property
    have hyx := B.mem_orthogonal_iff.mp x.2.property y.1 y.1.property
    simp [prod_apply, restrict_apply, add_right, hxy, hB.isRefl.eq_zero hyx]

/-- Orthogonal reduction at an isotropic vector pairing to one removes one positive and
one negative direction from the scalar-extended form. -/
theorem IsSymm.sig_orthogonalQuotientForm (hB : B.IsSymm) [Module.Finite ℤ M]
    (hδ : B δ δ = 0) (hδf : B δ f = 1) :
    let Q := ((B.orthogonalQuotientForm hB (ℤ ∙ δ)).baseChange K).toQuadraticMap
    sigPos Q + 1 = sigPos (B.baseChange K).toQuadraticMap ∧
      sigNeg Q + 1 = sigNeg (B.baseChange K).toQuadraticMap := by
  let P := plane[ℤ, δ, f]
  let C := B.restrict (B.orthogonal P)
  have he : ((B.baseChange K).toQuadraticMap).Equivalent
      (((B.restrict P).baseChange K).toQuadraticMap.prod (C.baseChange K).toQuadraticMap) := by
    rw [← toQuadraticMap_prod]
    exact Equivalent.toQuadraticMap
      ⟨((isotropicPlaneProdIsometry hB hδ hδf).baseChange K).symm.trans
        (TauCeti.bilinFormBaseChangeProdIsometry K _ _)⟩
  have hq := Equivalent.toQuadraticMap (B₁ := C.baseChange K)
    ⟨(hB.isometryEquivOrthogonalQuotient hδ hδf).baseChange K⟩
  obtain ⟨hp, hn⟩ := sig_isotropicPlane hB K hδ hδf
  constructor
  · rw [he.sigPos_eq, QuadraticForm.sigPos_prod, hp, hq.sigPos_eq, Nat.add_comm]
  · rw [he.sigNeg_eq, QuadraticForm.sigNeg_prod, hn, hq.sigNeg_eq, Nat.add_comm]

end Signature

end Integral

end LinearMap.BilinForm

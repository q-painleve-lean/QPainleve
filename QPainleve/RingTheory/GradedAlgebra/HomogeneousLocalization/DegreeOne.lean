/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic
import TauCeti.RingTheory.GradedAlgebra.Degree.One

/-!
# Homogeneous localization at a degree-one element

Dehomogenization at a degree-one denominator sends each homogeneous element of
degree `n` to the fraction with denominator its `n`th power. If the graded algebra
is generated in degree one, the degree-one fractions determine maps out of the
chart ring, including their action on degree-zero coefficients.
-/

public noncomputable section

open DirectSum

namespace HomogeneousLocalization.Away

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] {f : A} (hf : f ∈ 𝒜 1)

private def numerator (n : ℕ) : 𝒜 n →+ Away 𝒜 f :=
  (Away.mkLinearMap hf n).toAddMonoidHom.comp
    (LinearEquiv.ofEq (𝒜 n) (𝒜 (n • 1)) (by rw [smul_eq_mul, mul_one])).toAddMonoidHom

private theorem numerator_apply (n : ℕ) (a : 𝒜 n) :
    numerator hf n a =
      Away.mk 𝒜 hf n a (by simpa only [smul_eq_mul, mul_one] using a.property) := by
  -- Identify the numerator module with degree `n • 1` as required by the localization API.
  change Away.mkLinearMap hf n (LinearEquiv.ofEq _ _ _ a) = _
  apply val_injective
  simp only [Away.mkLinearMap_apply, Away.val_mk, LinearEquiv.coe_ofEq_apply]

private theorem numerator_one :
    numerator hf 0 (@GradedMonoid.GOne.one ℕ (fun i ↦ ↥(𝒜 i)) _ _) = 1 := by
  apply val_injective
  rw [numerator_apply, Away.val_mk, val_one]
  simp

private theorem numerator_mul {i j : ℕ} (a : 𝒜 i) (b : 𝒜 j) :
    numerator hf (i + j) (@GradedMonoid.GMul.mul ℕ (fun i ↦ ↥(𝒜 i)) _ _ i j a b) =
      numerator hf i a * numerator hf j b := by
  apply val_injective
  simp only [numerator_apply, Away.val_mk, val_mul, Localization.mk_mul, SetLike.coe_gMul]
  congr 1
  exact Subtype.ext (pow_add f i j)

/-- Send a homogeneous element `a` of degree `n` to `a/fⁿ` in the degree-zero localization. -/
def dehomogenize : A →+* Away 𝒜 f :=
  (DirectSum.toSemiring (numerator hf) (numerator_one hf) (numerator_mul hf)).comp
    (decomposeRingEquiv 𝒜).toRingHom

/-- The value of dehomogenization on a homogeneous element. -/
theorem dehomogenize_apply_of_mem {n : ℕ} {a : A} (ha : a ∈ 𝒜 n) :
    dehomogenize hf a = Away.mk 𝒜 hf n a (by simpa only [smul_eq_mul, mul_one] using ha) := by
  have h : (decomposeRingEquiv 𝒜).toRingHom a = of (fun i ↦ ↥(𝒜 i)) n ⟨a, ha⟩ :=
    decompose_of_mem 𝒜 ha
  simp only [dehomogenize, RingHom.comp_apply, h, DirectSum.toSemiring_of, numerator_apply]

@[simp]
theorem dehomogenize_self : dehomogenize hf f = 1 := by
  rw [dehomogenize_apply_of_mem hf hf, Away.mk_self]

/-- Every homogeneous fraction with degree-one denominator is obtained by dehomogenization. -/
theorem surjective_dehomogenize : Function.Surjective (dehomogenize hf) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf z
  exact ⟨a, dehomogenize_apply_of_mem hf (by simpa only [smul_eq_mul, mul_one] using ha)⟩

/-- On a standard chart of a graded algebra generated in degree one, maps of rings
are determined by the fractions with degree-one numerator and denominator. -/
theorem ringHom_ext_of_degreeOne {B : Type*} [Semiring B] {g h : Away 𝒜 f →+* B}
    (hgen : Algebra.adjoin (𝒜 0) (𝒜 1 : Set A) = ⊤)
    (he : ∀ a : 𝒜 1, g (dehomogenize hf a) = h (dehomogenize hf a)) : g = h := by
  have hp {n : ℕ} {a : A} (hn : 0 < n) (ha : a ∈ 𝒜 n) :
      g (dehomogenize hf a) = h (dehomogenize hf a) :=
    RingHom.eqOn_sclosure (f := g.comp (dehomogenize hf)) (g := h.comp (dehomogenize hf))
      (fun x hx ↦ he ⟨x, hx⟩) (TauCeti.GradedAlgebra.mem_closure_grade_one 𝒜 hn hgen ha)
  refine RingHom.ext fun z ↦ ?_
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf z
  have ha' : a ∈ 𝒜 n := by simpa only [smul_eq_mul, mul_one] using ha
  rw [← dehomogenize_apply_of_mem hf ha']
  rcases n.eq_zero_or_pos with rfl | hn
  · have haf : a * f ∈ 𝒜 1 := by simpa using SetLike.mul_mem_graded ha' hf
    simpa only [map_mul, dehomogenize_self, map_one, mul_one] using hp Nat.one_pos haf
  · exact hp hn ha'

end HomogeneousLocalization.Away

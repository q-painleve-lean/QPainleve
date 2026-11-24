/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Fiber
public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Basic
import TauCeti.AlgebraicGeometry.Blowup.BaseChange

/-!
# Initial forms on the exceptional divisor

The intersection of a strict transform with the exceptional divisor lies in the
projective vanishing locus of the initial form of the local defining equation.
The comparison uses the Rees symbol map and the description of the strict
transform by schematic closure from [Stacks, Lemma 31.34.2](https://stacks.math.columbia.edu/tag/080E).
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry reesAlgebra

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I D : X.IdealSheafData)
  (U : X.affineOpens) {f : Γ(X, U.val)} {n : ℕ}

local notation "R" => (X.presheaf.obj (op U.val))
local notation "J" => I.ideal U
local notation "π" => Proj.toSpecCoeff (grade J)
local notation "hU" => (U.property : IsAffineOpen U.val)
local notation "ι" => I.blowupChart hU

-- Choose the additive group used by the associated graded ring in the Proj model.
local instance {A : Type u} [CommRing A] (L : Ideal A) :
    AddSubgroupClass (Submodule (A ⧸ L) L.AssociatedGraded) L.AssociatedGraded :=
  @Submodule.addSubgroupClass (A ⧸ L) L.AssociatedGraded
    (Ideal.Quotient.commRing L).toRing (DirectSum.commRing L.GradedPiece).toAddCommGroup
    Algebra.toModule

private theorem toSpecCoeff_preimage_basicOpen_rees (a : R) :
    π ⁻¹ᵁ (PrimeSpectrum.basicOpen a : (Spec R).Opens) =
      Proj.basicOpen (grade J) (algebraMap R (_root_.reesAlgebra J) a) := by
  rw [Proj.toSpecCoeff_def]
  erw [Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen, Proj.toSpecZero_preimage_basicOpen]
  rfl

private theorem monomial_mem_of_off_center (hf : f ∈ J ^ n) (z : Proj (grade J))
    (hz : π z ∈ PrimeSpectrum.zeroLocus ({f} : Set R))
    (hI : π z ∉ PrimeSpectrum.zeroLocus (J : Set R)) :
    (⟨Polynomial.monomial n f, monomial_mem.mpr hf⟩ : _root_.reesAlgebra J) ∈
      z.asHomogeneousIdeal := by
  obtain ⟨a, ha, haz⟩ := Set.not_subset.mp hI
  have hzero (b : R) : algebraMap R (_root_.reesAlgebra J) b ∈ z.asHomogeneousIdeal ↔
      b ∈ (π z).asIdeal := by
    apply not_iff_not.mp
    rw [← Proj.mem_basicOpen, ← toSpecCoeff_preimage_basicOpen_rees I U]
    exact PrimeSpectrum.mem_basicOpen _ _
  let F : _root_.reesAlgebra J := ⟨Polynomial.monomial n f, monomial_mem.mpr hf⟩
  let A := monomialDegreeOne ha
  have hmul : F * algebraMap R (_root_.reesAlgebra J) a ^ n =
      algebraMap R (_root_.reesAlgebra J) f * A ^ n := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap,
      Polynomial.algebraMap_apply, F, A, coe_monomialDegreeOne]
    rw [← Polynomial.monomial_zero_left, ← Polynomial.monomial_zero_left,
      Polynomial.monomial_pow, Polynomial.monomial_pow, Polynomial.monomial_mul_monomial,
      Polynomial.monomial_mul_monomial]
    simp [mul_comm]
  have hprime : (z.asHomogeneousIdeal.toIdeal).IsPrime := z.isPrime
  exact (hprime.mem_or_mem (hmul ▸ Ideal.mul_mem_right _ _ ((hzero f).mpr
    (hz (Set.mem_singleton f))))).resolve_right
      (fun h ↦ haz ((hzero a).mp (hprime.mem_of_pow_mem _ h)))

variable [IsLocallyNoetherian X]

/-- On an affine open where the divisor is defined by `f`, its strict transform
vanishes on the Rees monomial of `f` in any degree for which `f ∈ I^n`. -/
theorem preimage_support_ker_blowupMap_subset_compl_basicOpen_monomial
    (hD : D.ideal U = Ideal.span {f}) (hf : f ∈ J ^ n) :
    ι ⁻¹' ((I.blowupMap D.subschemeι).ker.support : Set I.blowup) ⊆
      (Proj.basicOpen (grade J)
        (⟨Polynomial.monomial n f, monomial_mem.mpr hf⟩ : _root_.reesAlgebra J) : Set _)ᶜ := by
  let p := pullback.snd D.subschemeι I.blowupToBase
  let q := pullback.fst D.subschemeι I.blowupToBase
  let W := (q ≫ D.subschemeι) ⁻¹ᵁ I.support.compl
  let g := W.ι ≫ p
  have hker : (I.blowupMap D.subschemeι).ker = g.ker := I.ker_blowupMap D.subschemeι
  have hproj := I.blowupChart_blowupToBase hU
  have : IsLocallyNoetherian I.blowup := LocallyOfFiniteType.isLocallyNoetherian I.blowupToBase
  have : IsClosedImmersion p := MorphismProperty.of_isPullback
    (P := @IsClosedImmersion) (IsPullback.of_hasPullback D.subschemeι I.blowupToBase) inferInstance
  have : IsLocallyNoetherian (pullback D.subschemeι I.blowupToBase) :=
    LocallyOfFiniteType.isLocallyNoetherian p
  have : QuasiCompact g := inferInstanceAs (QuasiCompact (W.ι ≫ p))
  have hsupport (K : X.IdealSheafData) (z : Proj (grade J)) :
      I.blowupToBase (ι z) ∈ K.support ↔
        π z ∈ PrimeSpectrum.zeroLocus (K.ideal U : Set R) := by
    have hx : I.blowupToBase (ι z) = IsAffineOpen.fromSpec hU (π z) :=
      congrArg (fun g : Proj (grade J) ⟶ X ↦ g z) hproj
    rw [hx, K.mem_support_iff_of_mem ((IsAffineOpen.range_fromSpec hU).le (Set.mem_range_self _)),
      ← Set.mem_preimage, IsAffineOpen.fromSpec_preimage_zeroLocus hU]
    rfl
  let c := I.blowupChart (U := U.val) hU
  have : IsOpenImmersion c := MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (I.isPullback_blowupChart_fromSpec hU) (IsAffineOpen.isOpenImmersion_fromSpec hU)
  have hopen := c.isOpenEmbedding
  rw [hker, g.support_ker,
    hopen.isOpenMap.preimage_closure_eq_closure_preimage c.continuous]
  apply closure_minimal _ (Opens.isOpen _).isClosed_compl
  rintro z ⟨w, hw⟩
  have hz : I.blowupToBase (ι z) = D.subschemeι (q w.val) := by
    rw [← hw]
    exact congrArg (fun k : pullback D.subschemeι I.blowupToBase ⟶ X ↦ k w.val)
      pullback.condition.symm
  have hD' : I.blowupToBase (ι z) ∈ D.support := by
    rw [hz, ← SetLike.mem_coe, ← D.range_subschemeι]
    exact Set.mem_range_self _
  have hI : I.blowupToBase (ι z) ∉ I.support := by
    rw [hz]
    exact w.property
  rw [hsupport, hD, PrimeSpectrum.zeroLocus_span] at hD'
  simpa only [Set.mem_compl_iff, SetLike.mem_coe, Proj.mem_basicOpen, not_not] using
    monomial_mem_of_off_center I U hf z hD' ((hsupport I z).not.mp hI)

/-- A point of the projectivized associated graded ring mapping into the strict
transform annihilates the symbol of the local equation. In the degree of the
equation's order, this is its initial form on the exceptional divisor. -/
theorem preimage_support_ker_blowupMap_subset_compl_basicOpen_initialForm
    (hD : D.ideal U = Ideal.span {f}) (hf : f ∈ J ^ n) :
    (QPainleve.affineBlowupAssociatedGradedι J ≫ ι) ⁻¹'
        ((I.blowupMap D.subschemeι).ker.support : Set I.blowup) ⊆
      (Proj.basicOpen (Ideal.AssociatedGraded.grade J)
        (Ideal.AssociatedGraded.mk J n ⟨f, hf⟩) : Set _)ᶜ := by
  have h := I.preimage_support_ker_blowupMap_subset_compl_basicOpen_monomial D U hD hf
  intro z hz
  have hm : QPainleve.affineBlowupAssociatedGradedι J z ∉ Proj.basicOpen (grade J)
      (⟨Polynomial.monomial n f, monomial_mem.mpr hf⟩ : _root_.reesAlgebra J) := h hz
  rw [← Scheme.Hom.mem_preimage, QPainleve.affineBlowupAssociatedGradedι_preimage_basicOpen,
    toAssociatedGraded_monomial] at hm
  exact hm

end AlgebraicGeometry.Scheme.IdealSheafData

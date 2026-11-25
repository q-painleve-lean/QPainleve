/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.InitialForm
public import Mathlib.Algebra.QuadraticDiscriminant

import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Quadratic
import TauCeti.AlgebraicGeometry.Pullback.Carrier
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# The quadratic tangent cone from exceptional attachments

For a double point on a surface, the points where the strict transform meets the
exceptional line are zeros of a binary quadratic. If there are two distinct
attachments in characteristic different from two, the quadratic is nondegenerate.
This is the tangent-form condition in [Stacks, Lemma 53.19.3]
(https://stacks.math.columbia.edu/tag/0C49).
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open TauCeti.AlgebraicGeometry QPainleve RingTheory.Sequence reesAlgebra

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open Opposite projectiveLine

variable {X : Scheme.{u}} (I D : X.IdealSheafData)
  (U : X.affineOpens) {x y f a b c : Γ(X, U.val)}

local notation "R" => (X.presheaf.obj (op U.val))
local notation "J" => I.ideal U
local notation "K" => R ⧸ J
local notation "hU" => (U.property : IsAffineOpen U.val)

local notation "P" => _root_.SymmetricAlgebra K (Fin 2 → K)
local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule K (Fin 2 → K)
local notation "C" => RingHom.comp (algebraMap K P) (Ideal.Quotient.mk J)
local notation "j[" h "," g "]" =>
  (Iso.inv (affineBlowupExceptionalIsoProjectiveLine h g) ≫
    subschemeι (affineBlowupExceptionalIdeal R J))
local notation "ι" => I.blowupChart hU

private theorem parameterAlgebraEquiv_binary_quadratic
    (hxy : IsWeaklyRegular R [x, y]) (hJ : Ideal.ofList [x, y] = J)
    (hf : f ∈ J ^ 2) (heq : f = a * x ^ 2 + b * x * y + c * y ^ 2) :
    affineBlowupParameterAlgebraEquiv hxy hJ
      (C a * coord K 0 ^ 2 + C b * coord K 0 * coord K 1 + C c * coord K 1 ^ 2) =
      Ideal.AssociatedGraded.mk J 2 ⟨f, hf⟩ := by
  have hmap (r : R) : affineBlowupParameterAlgebraEquiv hxy hJ (C r) =
      Ideal.AssociatedGraded.mk J 0 ⟨r, Ideal.mem_pow_zero J r⟩ := by
    rw [RingHom.comp_apply, AlgEquiv.commutes, Ideal.AssociatedGraded.algebraMap_quotient_mk,
      Ideal.AssociatedGraded.mk_zero]
  simp only [pow_two, map_add, map_mul, affineBlowupParameterAlgebraEquiv_coord,
    hmap a, hmap b, hmap c, Ideal.AssociatedGraded.mk_mul_mk]
  rw [← map_add, ← map_add]
  congr 1
  apply Subtype.ext
  simpa only [Submodule.coe_add, List.getElem_cons_zero, List.getElem_cons_succ,
    Fin.val_zero, Fin.val_one, pow_two] using heq.symm

private theorem range_exceptional_projectiveLine
    (hxy : IsWeaklyRegular R [x, y]) (hJ : Ideal.ofList [x, y] = J)
    (hcover : (I.support : Set X) ⊆ U.val) :
    Set.range (j[hxy,hJ] ≫ ι) = ((I.comap I.blowupToBase).support : Set I.blowup) := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have hq : Set.range q = PrimeSpectrum.zeroLocus (J : Set R) := by
    -- The underlying map of the quotient spectrum contracts prime ideals.
    change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) = _
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  have H := I.isPullback_blowupChart_projectiveLine hU hxy hJ
  refine (Scheme.Pullback.range_fst_of_isPullback H).trans ?_
  rw [Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, hq, IsAffineOpen.fromSpec_image_zeroLocus hU, ← I.supportSet_inter U,
    Set.inter_eq_left.mpr (show I.supportSet ⊆ U.val from hcover), support_comap,
    Closeds.coe_preimage]
  rfl

variable [IsLocallyNoetherian X]

/-- If an order-two equation has two distinct strict-transform points on the
exceptional line of a regular pair, its tangent discriminant is nonzero in the
residue field. The two points can belong to the same irreducible component. -/
theorem discrim_notMem_of_two_exceptional_attachments
    (hxy : IsWeaklyRegular R [x, y]) (hJ : Ideal.ofList [x, y] = J)
    [Ideal.IsMaximal J] [NeZero (2 : K)] (hcover : (I.support : Set X) ⊆ U.val)
    (hD : D.ideal U = Ideal.span {f}) (hf₃ : f ∉ J ^ 3)
    (heq : f = a * x ^ 2 + b * x * y + c * y ^ 2)
    (hattach : ¬ (((I.blowupMap D.subschemeι).ker.support : Set I.blowup) ∩
      ((I.comap I.blowupToBase).support : Set I.blowup)).Subsingleton) :
    discrim a b c ∉ J := by
  let : Field K := Ideal.Quotient.field J
  have hspan : Ideal.span {x, y} = J := by simpa [Ideal.span_insert] using hJ
  have hf : f ∈ J ^ 2 := hspan ▸ Ideal.mem_span_pair_sq.mpr ⟨a, b, c, heq.symm⟩
  let q := C a * coord K 0 ^ 2 + C b * coord K 0 * coord K 1 + C c * coord K 1 ^ 2
  have hq : affineBlowupParameterAlgebraEquiv hxy hJ q = Ideal.AssociatedGraded.mk J 2 ⟨f, hf⟩ :=
    parameterAlgebraEquiv_binary_quadratic I U hxy hJ hf heq
  have hq₀ : q ≠ 0 := by
    intro h
    apply hf₃
    rw [h, map_zero] at hq
    exact (Ideal.AssociatedGraded.mk_eq_zero_iff (I := J) ⟨f, hf⟩).mp hq.symm
  intro hd
  have hd' : discrim (Ideal.Quotient.mk J a) (Ideal.Quotient.mk J b)
      (Ideal.Quotient.mk J c) = 0 := by
    simpa only [discrim, map_sub, map_pow, map_ofNat, map_mul] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr hd : Ideal.Quotient.mk J (discrim a b c) = 0)
  have hzero : ((Proj.basicOpen 𝒜 q : Set (projectiveLine K))ᶜ).Subsingleton :=
    subsingleton_compl_basicOpen_of_discrim_eq_zero hd' hq₀
  let s : _root_.reesAlgebra J := ⟨Polynomial.monomial 2 f, monomial_mem.mpr hf⟩
  have hpre : j[hxy,hJ] ⁻¹ᵁ Proj.basicOpen (grade J) s = Proj.basicOpen 𝒜 q :=
    preimage_basicOpen_affineBlowupExceptionalIsoProjectiveLine_of_symbol hxy hJ s q
      (hq.trans (toAssociatedGraded_monomial hf).symm)
  have hmem (z : projectiveLine K)
      (hz : (j[hxy,hJ] ≫ ι) z ∈ (I.blowupMap D.subschemeι).ker.support) :
      z ∈ ((Proj.basicOpen 𝒜 q : Set (projectiveLine K))ᶜ) := by
    have hh : j[hxy,hJ] z ∉ Proj.basicOpen (grade J) s :=
      I.preimage_support_ker_blowupMap_subset_compl_basicOpen_monomial D U hD hf hz
    rwa [← Scheme.Hom.mem_preimage, hpre] at hh
  apply hattach
  rw [← range_exceptional_projectiveLine I U hxy hJ hcover]
  rintro _ ⟨hp, z, rfl⟩ _ ⟨hp', z', rfl⟩
  exact congrArg (j[hxy,hJ] ≫ ι) (hzero (hmem z hp) (hmem z' hp'))

end AlgebraicGeometry.Scheme.IdealSheafData

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Cohomology.Cech.Top
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Canonical
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent
import Mathlib.RingTheory.FiniteType
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.BasicOpen
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.TopDual
import TauCeti.CategoryTheory.Limits.Lattice

/-!
# The coordinate residue on the projective plane

On the full standard overlap, the residue of a section of `𝒪(-3)` is the
coefficient of `(X₀ X₁ X₂)⁻¹`. This coefficient is independent of the chosen
homogeneous fraction and is zero on sections from any double overlap.

The fraction calculation uses the description of the standard opens in the
[Stacks Project, Lemma 30.8.1](https://stacks.math.columbia.edu/tag/01XT).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite MvPolynomial Finset
open Scheme.Modules
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R]

local notation "A" => MvPolynomial (Fin 3) R
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 3) R
local notation "P" => Proj 𝒜
local notation "T" => twistingSheaf 𝒜 (-3)
local notation "Ω₂" => Functor.obj (SheafOfModules.exteriorPower (Scheme.sheaf P) 2)
  (Scheme.relativeDifferentials R P)

attribute [local instance] planeOver

private def coordProduct (s : Finset (Fin 3)) : A := ∏ i ∈ s, X i

private def coordExponent (s : Finset (Fin 3)) : Fin 3 →₀ ℕ :=
  ∑ i ∈ s, Finsupp.single i 1

private theorem coordProduct_mem (s : Finset (Fin 3)) : coordProduct R s ∈ 𝒜 s.card := by
  simpa only [coordProduct, sum_const, nsmul_eq_mul, mul_one, Nat.cast_id] using
    SetLike.prod_mem_graded 𝒜 (fun _ : Fin 3 ↦ 1) (fun i ↦ (X i : A))
      (F := s) fun i _ ↦ (mem_homogeneousSubmodule ..).mpr (isHomogeneous_X R i)

private theorem coordProduct_eq_monomial (s : Finset (Fin 3)) :
    coordProduct R s = monomial (coordExponent s) 1 :=
  (MvPolynomial.monomial_sum_one s _).symm

private theorem basicOpen_coordProduct (s : Finset (Fin 3)) :
    basicOpen 𝒜 (coordProduct R s) = s.inf (fun i ↦ basicOpen 𝒜 (X i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coordProduct]
  | insert i s hi ih =>
    rw [coordProduct, prod_insert hi, basicOpen_mul, inf_insert, ← coordProduct, ih]

/-- The intersection of the three standard affine opens of the polynomial projective plane. -/
def polynomialPlaneOverlap : (P).Opens :=
  basicOpen 𝒜 (coordProduct R univ)

private theorem overlap_le_basicOpen_pow (k : ℕ) :
    polynomialPlaneOverlap R ≤ basicOpen 𝒜 (coordProduct R univ ^ k) :=
  fun x hx hk ↦ hx (x.isPrime.mem_of_pow_mem k hk)

private theorem coordProduct_univ_pow_mem (k : ℕ) :
    coordProduct R univ ^ k ∈ 𝒜 (k * 3) := by
  simpa only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using
    SetLike.pow_mem_graded k (coordProduct_mem R univ)

private def planeFraction {k j : ℕ} (h : (j : ℤ) = (k * 3 : ℕ) - 3)
    (p : A) (hp : p ∈ 𝒜 j) : Γ(T, polynomialPlaneOverlap R) :=
  twistingSheaf.const h p (coordProduct R univ ^ k) hp (coordProduct_univ_pow_mem R k)
    _ (overlap_le_basicOpen_pow R k)

private theorem exists_planeFraction (s : Γ(T, polynomialPlaneOverlap R)) :
    ∃ (k j : ℕ) (h : (j : ℤ) = (k * 3 : ℕ) - 3) (p : A) (hp : p ∈ 𝒜 j),
      s = planeFraction R h p hp := by
  obtain ⟨k, j, h, p, hp, he⟩ := twistingSheaf.exists_eq_const_basicOpen
    (coordProduct_mem R univ) (by simp) s
  refine ⟨k, j, ?_, p, hp, he⟩
  simpa only [sub_eq_add_neg, Finset.card_univ, Fintype.card_fin] using h

private def fractionCoeff (k : ℕ) (p : A) : R :=
  p.coeff ((k - 1) • coordExponent univ)

private theorem fractionCoeff_mul_coordProduct_pow (k l : ℕ) (hk : 0 < k) (p : A) :
    fractionCoeff R (k + l) (coordProduct R univ ^ l * p) = fractionCoeff R k p := by
  have h : k + l - 1 = (k - 1) + l := by omega
  simp only [fractionCoeff, coordProduct_eq_monomial, monomial_pow, one_pow, h,
    add_comm (k - 1) l, add_smul, coeff_monomial_mul, one_mul]

private theorem fractionCoeff_eq_of_planeFraction_eq {k l j j' : ℕ}
    {h : (j : ℤ) = (k * 3 : ℕ) - 3} {h' : (j' : ℤ) = (l * 3 : ℕ) - 3}
    {p q : A} {hp : p ∈ 𝒜 j} {hq : q ∈ 𝒜 j'}
    (he : planeFraction R h p hp = planeFraction R h' q hq) :
    fractionCoeff R k p = fractionCoeff R l q := by
  have hg : coordProduct R univ ∈ HomogeneousIdeal.irrelevant 𝒜 :=
    HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 (by simp) (coordProduct_mem R univ)
  obtain ⟨N, hN⟩ := (twistingSheaf.const_eq_const_iff hg h h' hp
    (coordProduct_univ_pow_mem R k) hq (coordProduct_univ_pow_mem R l)
    (overlap_le_basicOpen_pow R k) (overlap_le_basicOpen_pow R l)).mp he
  rw [mul_sub, sub_eq_zero, ← mul_assoc, ← pow_add, ← mul_assoc, ← pow_add] at hN
  have heq := congrArg (fractionCoeff R (k + (N + l))) hN
  have hk : 0 < k := by omega
  have hl : 0 < l := by omega
  rw [fractionCoeff_mul_coordProduct_pow R k (N + l) hk] at heq
  rwa [show k + (N + l) = l + (N + k) by omega,
    fractionCoeff_mul_coordProduct_pow R l (N + k) hl] at heq

private def residueValue (s : Γ(T, polynomialPlaneOverlap R)) : R :=
  fractionCoeff R (exists_planeFraction R s).choose
    (exists_planeFraction R s).choose_spec.choose_spec.choose_spec.choose

private theorem residueValue_planeFraction {k j : ℕ} (h : (j : ℤ) = (k * 3 : ℕ) - 3)
    (p : A) (hp : p ∈ 𝒜 j) :
    residueValue R (planeFraction R h p hp) = fractionCoeff R k p := by
  unfold residueValue
  let hs := exists_planeFraction R (planeFraction R h p hp)
  exact fractionCoeff_eq_of_planeFraction_eq R
    (Exists.choose_spec (Exists.choose_spec (Exists.choose_spec
      (Exists.choose_spec (Exists.choose_spec hs))))).symm

private theorem planeFraction_mul_coordProduct_pow {k j : ℕ} (h : (j : ℤ) = (k * 3 : ℕ) - 3)
    (p : A) (hp : p ∈ 𝒜 j) (l : ℕ)
    (h' : ((l * 3 + j : ℕ) : ℤ) = ((k + l) * 3 : ℕ) - 3) :
    planeFraction R h' (coordProduct R univ ^ l * p)
        (SetLike.mul_mem_graded (coordProduct_univ_pow_mem R l) hp) =
      planeFraction R h p hp := by
  apply twistingSheaf.const_ext
  rw [pow_add]
  ring

private theorem residueValue_add (s t : Γ(T, polynomialPlaneOverlap R)) :
    residueValue R (s + t) = residueValue R s + residueValue R t := by
  obtain ⟨k, j, h, p, hp, rfl⟩ := exists_planeFraction R s
  obtain ⟨l, j', h', q, hq, rfl⟩ := exists_planeFraction R t
  let p' := coordProduct R univ ^ l * p
  let q' := coordProduct R univ ^ k * q
  have hp' : p' ∈ 𝒜 (l * 3 + j) :=
    SetLike.mul_mem_graded (coordProduct_univ_pow_mem R l) hp
  have hq' : q' ∈ 𝒜 (l * 3 + j) := by
    convert SetLike.mul_mem_graded (coordProduct_univ_pow_mem R k) hq using 1
    congr 1
    omega
  have h'' : ((l * 3 + j : ℕ) : ℤ) = ((k + l) * 3 : ℕ) - 3 := by omega
  have hpEq : planeFraction R h'' p' hp' = planeFraction R h p hp :=
    planeFraction_mul_coordProduct_pow R h p hp l h''
  have hqEq : planeFraction R h'' q' hq' = planeFraction R h' q hq := by
    apply twistingSheaf.const_ext
    simp only [q', pow_add]
    ring
  rw [← hpEq, ← hqEq]
  have hadd : planeFraction R h'' p' hp' + planeFraction R h'' q' hq' =
      planeFraction R h'' (p' + q') (add_mem hp' hq') :=
    twistingSheaf.const_add ..
  rw [hadd]
  simp only [residueValue_planeFraction, fractionCoeff, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply]

private theorem smul_planeFraction (r : R) {k j : ℕ} (h : (j : ℤ) = (k * 3 : ℕ) - 3)
    (p : A) (hp : p ∈ 𝒜 j) :
    ((P).baseRingToStructurePresheaf R).app (op (polynomialPlaneOverlap R)) r •
      planeFraction R h p hp = planeFraction R h (r • p) (Submodule.smul_mem _ r hp) := by
  apply twistingSheaf.ext
  intro x
  have hx :
      ((((P).baseRingToStructurePresheaf R).app (op (polynomialPlaneOverlap R)) r).val x).val =
        Localization.mk (algebraMap R A r) 1 := by
    rw [Scheme.baseRingToStructurePresheaf_app, CommRingCat.comp_apply]
    have hglobal : (CommRingCat.ofHom (baseRingToGlobalSections R (P))) r =
        (toSpecCoeff 𝒜).appTop ((Scheme.ΓSpecIso (.of R)).inv r) :=
      baseRingToGlobalSections_apply R (P) r
    rw [hglobal]
    exact val_toSpecCoeff_appTop_apply 𝒜 r (⟨x.val, trivial⟩ : (⊤ : (P).Opens))
  simp only [planeFraction, twistingSheaf.smul_apply, twistingSheaf.const_apply]
  rw [hx, Localization.mk_mul, one_mul, Algebra.smul_def]

private def overlapResidue :
    ((sectionsBasePresheafFunctor R).obj (T)).obj (op (polynomialPlaneOverlap R)) →ₗ[R] R where
  toFun := residueValue R
  map_add' := residueValue_add R
  map_smul' r s := by
    obtain ⟨k, j, h, p, hp, rfl⟩ := exists_planeFraction R s
    refine (congrArg (residueValue R) (smul_planeFraction R r h p hp)).trans ?_
    simp only [residueValue_planeFraction, fractionCoeff, AddMonoidAlgebra.coeff_smul,
      RingHom.id_apply, Finsupp.smul_apply]

private theorem coordProduct_univ_eq_mul_erase (i : Fin 3) :
    coordProduct R univ = X i * coordProduct R (univ.erase i) := by
  simp only [coordProduct, mul_prod_erase _ _ (mem_univ i)]

private theorem overlap_le_face (i : Fin 3) :
    polynomialPlaneOverlap R ≤ basicOpen 𝒜 (coordProduct R (univ.erase i)) := by
  rw [polynomialPlaneOverlap, coordProduct_univ_eq_mul_erase R i, basicOpen_mul]
  exact inf_le_right

private theorem coordExponent_univ_apply (i : Fin 3) : coordExponent univ i = 1 := by
  simp [coordExponent, Finsupp.single_apply]

private theorem fractionCoeff_X_pow_mul (i : Fin 3) (k : ℕ) (hk : 0 < k) (p : A) :
    fractionCoeff R k (X i ^ k * p) = 0 := by
  have hlt : ¬ k ≤ k - 1 := by omega
  simp [fractionCoeff, MvPolynomial.X, monomial_pow, coeff_monomial_mul',
    coordExponent_univ_apply, hlt]

private theorem overlapResidue_restrict_face (i : Fin 3)
    (s : Γ(T, basicOpen 𝒜 (coordProduct R (univ.erase i)))) :
    overlapResidue R ((T).presheaf.map (homOfLE (overlap_le_face R i)).op s) = 0 := by
  have hi : (univ.erase i).card = 2 := by simp
  obtain ⟨k, j, h, p, hp, he⟩ :=
    twistingSheaf.exists_eq_const_basicOpen (coordProduct_mem R (univ.erase i))
      (by rw [hi]; decide) s
  have hdeg : ((k + j : ℕ) : ℤ) = (k * 3 : ℕ) - 3 := by rw [hi] at h; omega
  have hX : (X i : A) ^ k ∈ 𝒜 k := by
    simpa using SetLike.pow_mem_graded k
      ((mem_homogeneousSubmodule ..).mpr (isHomogeneous_X R i))
  have hres :
      (T).presheaf.map (homOfLE (overlap_le_face R i)).op
          s = planeFraction R hdeg (X i ^ k * p) (SetLike.mul_mem_graded hX hp) := by
    rw [he]
    -- Pass the proof selecting the denominator explicitly to the restriction formula.
    refine (twistingSheaf.res_const h p _ hp _ _ _).trans ?_
    apply twistingSheaf.const_ext
    rw [coordProduct_univ_eq_mul_erase R i, mul_pow]
    ring
  rw [hres]
  exact (residueValue_planeFraction R hdeg _ _).trans
    (fractionCoeff_X_pow_mul R i k (by omega) p)

/-- The section of `𝒪(-3)` given by `1 / (X₀ X₁ X₂)` on the full standard overlap. -/
def polynomialPlaneInverseCoordinateProduct : Γ(T, polynomialPlaneOverlap R) :=
  planeFraction R (k := 1) (j := 0) (by decide) 1 (SetLike.one_mem_graded 𝒜)

private theorem overlapResidue_inverseCoordinateProduct :
    overlapResidue R (polynomialPlaneInverseCoordinateProduct R) = 1 := by
  exact (residueValue_planeFraction R (k := 1) (j := 0) _ _ _).trans (by
    simp [fractionCoeff])

private abbrev planeOrder : Fin (2 + 1) ≃o ULift.{u} (Fin 3) :=
  ULift.orderIso.symm

private def planeCover (i : ULift.{u} (Fin 3)) : (P).Opens :=
  basicOpen 𝒜 (X i.down)

private theorem affine_planeCover (s : Finset (ULift.{u} (Fin 3))) (hs : s.Nonempty) :
    IsAffineOpen (s.inf (planeCover R)) := by
  classical
  -- The lifted index type only places the coordinates in the universe of the base ring.
  change IsAffineOpen (s.inf ((fun i : Fin 3 ↦ basicOpen 𝒜 (X i)) ∘ ULift.down))
  rw [← Finset.inf_image, ← basicOpen_coordProduct]
  exact isAffineOpen_basicOpen 𝒜 _ (coordProduct_mem R _) (card_pos.mpr (hs.image _))

private theorem iSup_planeCover : ⨆ i, planeCover R i = ⊤ := by
  rw [← (ULift.orderIso.toEquiv).symm.iSup_comp]
  exact iSup_basicOpen_eq_top _ _ (MvPolynomial.irrelevant_eq_span_X (Fin 3) R).le

private theorem planeOverlap_eq_product :
    polynomialPlaneOverlap R = ∏ᶜ (planeCover R ∘ planeOrder) := by
  rw [polynomialPlaneOverlap, basicOpen_coordProduct,
    CategoryTheory.Limits.CompleteLattice.finite_product_eq_finset_image_inf]
  rw [Finset.inf_image]
  rfl

private theorem planeFace_eq_product (i : Fin 3) :
    basicOpen 𝒜 (coordProduct R (univ.erase i)) =
      ∏ᶜ fun j : Fin 2 ↦ (planeCover R ∘ planeOrder) (i.succAbove j) := by
  rw [basicOpen_coordProduct,
    CategoryTheory.Limits.CompleteLattice.finite_product_eq_finset_image_inf]
  have hi : univ.image i.succAbove = univ.erase i := by
    ext j
    simp
  rw [Finset.inf_image, ← hi, Finset.inf_image]
  rfl

private def planeOverlapToProduct (M : (P).Modules) :
    ((sectionsBasePresheafFunctor R).obj M).obj (op (polynomialPlaneOverlap R)) ⟶
      ((sectionsBasePresheafFunctor R).obj M).obj (op (∏ᶜ (planeCover R ∘ planeOrder))) :=
  ((sectionsBasePresheafFunctor R).obj M).map (eqToHom (planeOverlap_eq_product R).symm).op

/-- The degree-two Čech class of a section on the overlap of the three standard affine
charts, ordered by their homogeneous coordinate indices. -/
def polynomialPlaneCechClass (M : (P).Modules) [M.IsQuasicoherent] :
    ((sectionsBasePresheafFunctor R).obj M).obj (op (polynomialPlaneOverlap R)) →ₗ[R]
      Cohomology M 2 :=
  (topCechCohomologyClass (R := R) planeOrder (planeCover R) M (affine_planeCover R)
    (iSup_planeCover R)).comp (planeOverlapToProduct R M).hom

private def overlapResidueHom :
    ((sectionsBasePresheafFunctor R).obj (T)).obj (op (polynomialPlaneOverlap R)) ⟶
      ModuleCat.of R R :=
  ModuleCat.ofHom
    (X := ((sectionsBasePresheafFunctor R).obj (T)).obj (op (polynomialPlaneOverlap R)))
    (Y := ModuleCat.of R R) (overlapResidue R)

private def residueOnProduct :
    ((sectionsBasePresheafFunctor R).obj (T)).obj
      (op (∏ᶜ (planeCover R ∘ planeOrder))) ⟶ ModuleCat.of R R :=
  ((sectionsBasePresheafFunctor R).obj (T)).map (eqToHom (planeOverlap_eq_product R)).op ≫
    overlapResidueHom R

private theorem residueOnProduct_comp_face (i : Fin 3) :
    ((sectionsBasePresheafFunctor R).obj (T)).map
        (Pi.lift fun j : Fin 2 ↦ Pi.π (planeCover R ∘ planeOrder) (i.succAbove j)).op ≫
      residueOnProduct R = 0 := by
  let Q := (sectionsBasePresheafFunctor R).obj (T)
  let a := eqToHom (planeOverlap_eq_product R)
  let b := eqToHom (planeFace_eq_product R i)
  let c := Pi.lift (fun j : Fin 2 ↦ Pi.π (planeCover R ∘ planeOrder) (i.succAbove j))
  let d := homOfLE (overlap_le_face R i)
  have h : a ≫ c = d ≫ b := Subsingleton.elim _ _
  have hkill : Q.map d.op ≫ overlapResidueHom R = 0 := by
    apply ModuleCat.hom_ext
    ext s
    exact overlapResidue_restrict_face R i s
  -- The two maps on the ordered Čech terms are restrictions along these inclusions.
  change Q.map c.op ≫ (Q.map a.op ≫ overlapResidueHom R) = 0
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp, h, op_comp, Functor.map_comp,
    Category.assoc, hkill, comp_zero]

private def polynomialPlaneTwistingTrace : Cohomology (T) 2 →ₗ[R] R :=
  topCechCohomologyDesc planeOrder (planeCover R) (T) (affine_planeCover R)
    (iSup_planeCover R) (residueOnProduct R) (residueOnProduct_comp_face R)

private theorem planeOverlapToProduct_comp_residue :
    planeOverlapToProduct R (T) ≫ residueOnProduct R = overlapResidueHom R := by
  let Q := (sectionsBasePresheafFunctor R).obj (T)
  let a := eqToHom (planeOverlap_eq_product R)
  let b := eqToHom (planeOverlap_eq_product R).symm
  have hab : a ≫ b = 𝟙 _ := Subsingleton.elim _ _
  -- The product of opens and the standard overlap are the same open.
  change Q.map b.op ≫ (Q.map a.op ≫ overlapResidueHom R) = _
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp, hab, op_id]
  exact (congrArg (fun f ↦ f ≫ overlapResidueHom R) (Q.map_id _)).trans (Category.id_comp _)

private theorem polynomialPlaneTwistingTrace_cechClass
    (s : ((sectionsBasePresheafFunctor R).obj (T)).obj (op (polynomialPlaneOverlap R))) :
    polynomialPlaneTwistingTrace R (polynomialPlaneCechClass R (T) s) = overlapResidue R s := by
  let x := (planeOverlapToProduct R (T)) s
  have hx : (residueOnProduct R) x = overlapResidue R s :=
    ConcreteCategory.congr_hom (planeOverlapToProduct_comp_residue R) s
  have h := topCechCohomologyDesc_class planeOrder (planeCover R) (T)
    (affine_planeCover R) (iSup_planeCover R) (residueOnProduct R)
    (residueOnProduct_comp_face R) x
  -- Compare the two applications on the bundled module of sections.
  change topCechCohomologyDesc planeOrder (planeCover R) (T) (affine_planeCover R)
    (iSup_planeCover R) (residueOnProduct R) (residueOnProduct_comp_face R)
    (topCechCohomologyClass (R := R) planeOrder (planeCover R) (T)
      (affine_planeCover R) (iSup_planeCover R) x) = overlapResidue R s
  exact h.trans hx

private theorem nonempty_linearEquiv_cohomology_two_twistingSheaf_neg_three :
    Nonempty (Cohomology (T) 2 ≃ₗ[R] R) := by
  classical
  let b := Pi.basisFun R (Fin 3)
  let e := b.polynomialProjIso
  let S := TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Fin 3 → R)
  let M := twistingSheaf S (-3)
  let : e.hom.IsOver (Spec (.of R)) := ⟨b.polynomialProjIso_hom_over⟩
  obtain ⟨f⟩ := b.nonempty_linearEquiv_cohomology_top_twistingSheaf_dual (-3)
    (n := 1) (j := 0) (Fintype.card_fin 3) (by norm_num)
  exact ⟨(cohomologyBaseLinearEquivOfIso R (b.polynomialProjIsoPullbackTwistingSheafIso
    (-3)).symm 2).trans <| (e.hom.cohomologyPullbackBaseLinearEquivOfIsIso R M 2).trans <|
      f.trans <| (LinearEquiv.arrowCongr
        (TauCeti.SymmetricAlgebra.homogeneousSubmoduleZeroEquiv R (Fin 3 → R))
        (LinearEquiv.refl R R)).trans (LinearMap.ringLmapEquivSelf R R R)⟩

private theorem bijective_polynomialPlaneTwistingTrace :
    Function.Bijective (polynomialPlaneTwistingTrace R) := by
  let f := polynomialPlaneTwistingTrace R
  let x := polynomialPlaneCechClass R (T) (polynomialPlaneInverseCoordinateProduct R)
  have hx : f x = 1 := (polynomialPlaneTwistingTrace_cechClass R _).trans
    (overlapResidue_inverseCoordinateProduct R)
  obtain ⟨e⟩ := nonempty_linearEquiv_cohomology_two_twistingSheaf_neg_three R
  exact OrzechProperty.bijective_of_surjective_of_injective e.toLinearMap f e.injective
    (fun r ↦ ⟨r • x, by rw [LinearMap.map_smul, hx, smul_eq_mul, mul_one]⟩)

/-- The normalized trace on the second cohomology of the twist `𝒪(-3)`
on the polynomial projective plane. -/
def polynomialPlaneTwistingTraceEquiv : Cohomology (T) 2 ≃ₗ[R] R :=
  LinearEquiv.ofBijective (polynomialPlaneTwistingTrace R)
    (bijective_polynomialPlaneTwistingTrace R)

/-- The Čech class of `1 / (X₀ X₁ X₂)` has trace one. -/
@[simp]
theorem polynomialPlaneTwistingTraceEquiv_inverseCoordinateProduct :
    polynomialPlaneTwistingTraceEquiv R
      (polynomialPlaneCechClass R (T) (polynomialPlaneInverseCoordinateProduct R) :
        Cohomology (T) 2) = 1 :=
  (polynomialPlaneTwistingTrace_cechClass R _).trans (overlapResidue_inverseCoordinateProduct R)

/-- The trace on the canonical bundle of the polynomial projective plane, normalized
in its standard coordinates by the comparison with `𝒪(-3)`. -/
def polynomialPlaneCanonicalTrace :
    Cohomology (Ω₂) 2 ≃ₗ[R] R :=
  (cohomologyBaseLinearEquivOfIso R (differentialFormsTwoIsoTwistingSheaf R) 2).trans
    (polynomialPlaneTwistingTraceEquiv R)

/-- In canonical-bundle cohomology, the class corresponding to the reciprocal
coordinate product still has trace one. -/
@[simp]
theorem polynomialPlaneCanonicalTrace_inverseCoordinateProduct :
    polynomialPlaneCanonicalTrace R
      ((cohomologyBaseLinearEquivOfIso R (differentialFormsTwoIsoTwistingSheaf R) 2).symm
        (polynomialPlaneCechClass R (T) (polynomialPlaneInverseCoordinateProduct R))) = 1 := by
  simp only [polynomialPlaneCanonicalTrace, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    polynomialPlaneTwistingTraceEquiv_inverseCoordinateProduct]

end AlgebraicGeometry.Proj

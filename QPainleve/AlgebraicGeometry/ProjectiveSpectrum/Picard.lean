/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Chart
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.LineBundle.Class

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Chart.Sections
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Integral
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
import TauCeti.AlgebraicGeometry.CartierDivisor.Excision
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.LineBundle.Affine.Picard
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.TwistingSheaf
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.GlobalSections
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.TensorProduct
import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# The Picard group of projective space

The complement of a coordinate hyperplane is an affine space with trivial Picard group.
Picard excision therefore reduces the calculation to the single hyperplane divisor.
The coordinate equation identifies its class with the twisting sheaf `𝒪(1)`.

The argument uses the divisor class group description of projective space in
Hartshorne, *Algebraic Geometry*, Proposition II.6.4. The Picard-group statement
is also the field case of the Stacks Project, [Lemma 31.29.5]
(https://stacks.math.columbia.edu/tag/0BXJ). The proof applies Tau Ceti's Picard excision
theorem `LineBundleClass.pullback_eq_one_iff_mem_closure_of_isOpenImmersion`.
-/

public noncomputable section

open CategoryTheory Opposite HomogeneousLocalization Order MonoidalCategory
open TauCeti TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {k : Type u} [Field k] {n : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k
local notation "P" => Proj 𝒜
local notation "U[" i "]" => basicOpen 𝒜 (MvPolynomial.X i)

@[instance_reducible, local instance]
private def chartSectionsAlgebra (i : Fin (n + 1)) : Algebra k Γ(P, U[i]) :=
  letI : (P).Over (Spec (.of k)) := ⟨toSpecCoeff 𝒜⟩
  (((P).baseRingToStructurePresheaf k).app (op U[i])).hom.toAlgebra

private theorem coordinate_mem_one (i : Fin (n + 1)) : MvPolynomial.X i ∈ 𝒜 1 :=
  (MvPolynomial.mem_homogeneousSubmodule ..).mpr (MvPolynomial.isHomogeneous_X k i)

private abbrev coordinateChart (i : Fin (n + 1)) : (Proj 𝒜).affineOpens :=
  ⟨U[i], isAffineOpen_basicOpen 𝒜 _ (coordinate_mem_one i) one_pos⟩

private theorem iSup_coordinateChart : (⨆ i : Fin (n + 1), (coordinateChart (k := k) i).val) = ⊤ :=
  iSup_basicOpen_eq_top _ _ (MvPolynomial.irrelevant_eq_span_X _ _).le

private def coordinateToUnitLinear (j : Fin (n + 1)) (U : (Proj 𝒜).Opens) :
    Γ(twistingSheaf 𝒜 (-1), U) →ₗ[Γ(P, U)] Γ(P, U) :=
  (sectionsLinearEquivTwistingSheafZero 𝒜 U).symm.toLinearMap.comp <|
    twistingSheaf.mul 𝒜 U 1 (-1)
      (toTwistingSheaf 𝒜 rfl U ⟨MvPolynomial.X j, coordinate_mem_one j⟩)

private def coordinateToUnit (j : Fin (n + 1)) :
    twistingSheaf 𝒜 (-1) ⟶ 𝟙_ (Proj 𝒜).Modules where
  val :=
    { app := fun V ↦ by
        let φ := ModuleCat.ofHom (coordinateToUnitLinear (k := k) j V.unop)
        exact φ
      naturality := by
        intro V W f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro t
        rfl }

/-- The scheme-theoretic coordinate hyperplane, cut out by multiplication by `Xⱼ`
from `𝒪(-1)` into the structure sheaf. -/
def coordinateHyperplaneIdeal (j : Fin (n + 1)) : (Proj 𝒜).IdealSheafData :=
  (coordinateToUnit (k := k) j).imageIdealSheaf

private theorem coordinateToUnit_app (j : Fin (n + 1)) (U : (Proj 𝒜).Opens)
    (s : Γ(twistingSheaf 𝒜 (-1), U)) :
    (coordinateToUnit (k := k) j).app U s = coordinateToUnitLinear j U s := (rfl)

private theorem coordinateToUnit_app_chartGenerator (i j : Fin (n + 1)) :
    (coordinateToUnit (k := k) j).app U[i]
      (twistingSheaf.chartGenerator (-1) _ (coordinate_mem_one i) U[i] le_rfl) =
        polynomialCoordinateRatio i j le_rfl := by
  apply (sectionsLinearEquivTwistingSheafZero 𝒜 U[i]).injective
  rw [coordinateToUnit_app, coordinateToUnitLinear, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  apply twistingSheaf.ext
  intro x
  -- Both sections are represented by the fraction `Xⱼ / Xᵢ` at each point of the chart.
  change (twistingSheaf.mul 𝒜 U[i] 1 (-1)
      (toTwistingSheaf 𝒜 rfl U[i] ⟨MvPolynomial.X j, coordinate_mem_one j⟩)
      (twistingSheaf.chartGenerator (-1) _ (coordinate_mem_one i) U[i] le_rfl)).val x = _
  rw [twistingSheaf.mul_apply, twistingSheaf.chartGenerator_apply,
    polynomialCoordinateRatio_self_open, TauCeti.MvPolynomial.awayXRatio_def,
    sectionsLinearEquivTwistingSheafZero_apply_apply, val_awayToSection_mk_apply,
    toTwistingSheaf_apply_apply, Localization.mk_mul]
  norm_num

/-- In the chart `D₊(Xᵢ)`, the coordinate hyperplane `Xⱼ = 0` has principal ideal
generated by the normalized coordinate `Xⱼ / Xᵢ`. -/
theorem coordinateHyperplaneIdeal_ideal (i j : Fin (n + 1)) (hU : IsAffineOpen U[i]) :
    (coordinateHyperplaneIdeal (k := k) j).ideal ⟨U[i], hU⟩ =
      Ideal.span {awayToSection 𝒜 (MvPolynomial.X i) (TauCeti.MvPolynomial.awayXRatio i j)} := by
  -- Use the restriction of multiplication by the coordinate on this affine chart.
  rw [← polynomialCoordinateRatio_self_open]
  change (coordinateHyperplaneIdeal (k := k) j).ideal (coordinateChart i) =
    Ideal.span {polynomialCoordinateRatio i j le_rfl}
  rw [coordinateHyperplaneIdeal, Scheme.Modules.Hom.imageIdealSheaf_ideal]
  ext r
  -- The coordinate chart is the affine open attached to the indicated standard open.
  change r ∈ (coordinateToUnit (k := k) j).imageIdeal U[i] ↔
    r ∈ (Ideal.span {polynomialCoordinateRatio i j le_rfl} : Ideal Γ(P, U[i]))
  rw [Scheme.Modules.Hom.mem_imageIdeal, Ideal.mem_span_singleton]
  let e := twistingSheaf.chartSectionsLinearEquiv (-1) _ (coordinate_mem_one i) U[i] le_rfl
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨a, rfl⟩ := e.surjective s
    rw [twistingSheaf.chartSectionsLinearEquiv_apply, coordinateToUnit_app, map_smul,
      ← coordinateToUnit_app, coordinateToUnit_app_chartGenerator]
    exact ⟨a, mul_comm a (polynomialCoordinateRatio (R := k) i j le_rfl)⟩
  · rintro ⟨a, rfl⟩
    refine ⟨e a, ?_⟩
    rw [twistingSheaf.chartSectionsLinearEquiv_apply, coordinateToUnit_app, map_smul,
      ← coordinateToUnit_app, coordinateToUnit_app_chartGenerator]
    exact mul_comm a (polynomialCoordinateRatio (R := k) i j le_rfl)

/-- The coordinate hyperplane is supported on the complement of the corresponding affine chart. -/
@[simp]
theorem coe_support_coordinateHyperplaneIdeal (j : Fin (n + 1)) :
    ((coordinateHyperplaneIdeal (k := k) j).support : Set P) = (U[j] : Set P)ᶜ := by
  ext x
  have ht : x ∈ (⊤ : (Proj 𝒜).Opens) := trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_coordinateChart (k := k) (n := n)).symm ▸ ht)
  rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem hi,
    coordinateHyperplaneIdeal_ideal, ← polynomialCoordinateRatio_self_open, Scheme.zeroLocus_span]
  -- The basic open of the local equation is the intersection of the two coordinate charts.
  have h : (Proj 𝒜).basicOpen (polynomialCoordinateRatio (R := k) i j le_rfl) =
      U[i] ⊓ U[j] := by
    rw [polynomialCoordinateRatio_self_open, TauCeti.MvPolynomial.awayXRatio_def,
      basicOpen_awayToSection_mk, basicOpen_mul]
  rw [Scheme.zeroLocus_singleton]
  rw [Set.mem_compl_iff, h]
  exact not_congr ⟨fun hx ↦ hx.2, fun hx ↦ ⟨hi, hx⟩⟩

private theorem isReduced_coordinateHyperplane (j : Fin (n + 1)) :
    IsReduced (coordinateHyperplaneIdeal (k := k) j).subscheme := by
  rw [Scheme.IdealSheafData.isReduced_subscheme_iff_radical_eq]
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top coordinateChart iSup_coordinateChart
  intro i
  apply Ideal.radical_eq_iff.mpr
  rw [coordinateHyperplaneIdeal_ideal, ← polynomialCoordinateRatio_self_open]
  by_cases h : j = i
  · subst j
    rw [polynomialCoordinateRatio_self, Ideal.span_singleton_one]
    exact Ideal.radical_eq_iff.mp (Ideal.radical_top _)
  · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq h
    let e := (polynomialChartSectionsEquiv k i).symm.toRingEquiv
    have hprime : (Ideal.span {MvPolynomial.X a} : Ideal (MvPolynomial (Fin n) k)).IsPrime := by
      simpa only [Set.image_singleton] using
        MvPolynomial.span_X_image_isPrime (R := k) ({a} : Set (Fin n))
    have he : (Ideal.span {MvPolynomial.X a}).comap e.toRingHom =
        Ideal.span {polynomialCoordinateRatio (R := k) i (i.succAbove a) le_rfl} := by
      have heq : (Ideal.span {polynomialCoordinateRatio (R := k) i (i.succAbove a) le_rfl}).map
          e.toRingHom = Ideal.span {MvPolynomial.X a} := by
        rw [Ideal.map_span, Set.image_singleton, polynomialCoordinateRatio_self_open,
          ← polynomialChartSectionsEquiv_X]
        exact congrArg (fun f ↦ Ideal.span {f})
          ((polynomialChartSectionsEquiv k i).symm_apply_apply (MvPolynomial.X a))
      rw [← heq]
      exact Ideal.comap_map_of_bijective e.toRingHom e.bijective
    rw [← he]
    exact (hprime.comap e.toRingHom).isRadical

private theorem coordinateHyperplane_prime (j : Fin (n + 1)) :
    (Ideal.span {MvPolynomial.X j} : Ideal (MvPolynomial (Fin (n + 1)) k)).IsPrime := by
  simpa only [Set.image_singleton] using
    MvPolynomial.span_X_image_isPrime (R := k) ({j} : Set (Fin (n + 1)))

private def hyperplaneGenericPoint [NeZero n] (j : Fin (n + 1)) : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := ⟨Ideal.span {MvPolynomial.X j},
    Ideal.isHomogeneous_span_singleton 𝒜 ⟨1, coordinate_mem_one j⟩⟩
  isPrime := coordinateHyperplane_prime j
  not_irrelevant_le := by
    intro h
    let a : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    have he : j.succAbove a ≠ j := Fin.succAbove_ne _ _
    have heval := MvPolynomial.span_X_image_eq_ker_aeval_ite_mem (R := k)
      ({j} : Set (Fin (n + 1)))
    have hmem : MvPolynomial.X (j.succAbove a) ∈
        (Ideal.span {MvPolynomial.X j} : Ideal (MvPolynomial (Fin (n + 1)) k)) :=
      h (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 one_pos (coordinate_mem_one (j.succAbove a)))
    rw [Set.image_singleton] at heval
    rw [heval, RingHom.mem_ker] at hmem
    simp [he] at hmem

private theorem coe_support_coordinateHyperplaneIdeal_eq_closure [NeZero n] (j : Fin (n + 1)) :
    ((coordinateHyperplaneIdeal (k := k) j).support : Set P) =
      closure {(hyperplaneGenericPoint (k := k) j : P)} := by
  rw [coe_support_coordinateHyperplaneIdeal]
  ext x
  -- The topology of the scheme is the topology on homogeneous prime ideals.
  let y : ProjectiveSpectrum 𝒜 := x
  have h : MvPolynomial.X j ∈ y.asHomogeneousIdeal ↔
      y ∈ closure {hyperplaneGenericPoint (k := k) j} := by
    rw [← ProjectiveSpectrum.le_iff_mem_closure]
    exact (Ideal.span_singleton_le_iff_mem _).symm
  exact (not_not.trans h)

/-- A coordinate hyperplane in positive-dimensional projective space is integral. -/
theorem isIntegral_subscheme_coordinateHyperplaneIdeal [NeZero n] (j : Fin (n + 1)) :
    IsIntegral (coordinateHyperplaneIdeal (k := k) j).subscheme := by
  let I := coordinateHyperplaneIdeal (k := k) j
  let x : P := hyperplaneGenericPoint (k := k) j
  have hsupport : I.support = ⟨closure {x}, isClosed_closure⟩ :=
    SetLike.coe_injective (coe_support_coordinateHyperplaneIdeal_eq_closure j)
  have hrad := (Scheme.IdealSheafData.isReduced_subscheme_iff_radical_eq I).mp
    (isReduced_coordinateHyperplane j)
  have heq : Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩ = I := by
    rw [← hsupport, Scheme.IdealSheafData.vanishingIdeal_support, hrad]
  have hX : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {x}, isClosed_closure⟩).subscheme := inferInstance
  rwa [heq] at hX

private abbrev polynomialTwistingBundle (m : ℤ) : InvertibleSheaf (Proj 𝒜) :=
  ⟨twistingSheaf 𝒜 m, isInvertible_twistingSheaf_of_iSup_eq_top
    (fun i : ULift.{u} (Fin (n + 1)) ↦ MvPolynomial.X i.down)
    (fun i ↦ coordinate_mem_one i.down)
    (by simpa only [iSup_ulift] using iSup_coordinateChart (k := k) (n := n)) m⟩

private theorem mono_coordinateToUnit (j : Fin (n + 1)) : Mono (coordinateToUnit (k := k) j) := by
  have := isIntegral_polynomialProj (R := k) (σ := Fin (n + 1))
  refine (polynomialTwistingBundle (k := k) (n := n) (-1)).mono_of_ne_zero_to_unit
    (coordinateToUnit j) ?_
  intro h
  have he := coordinateToUnit_app_chartGenerator (k := k) j j
  have hz : (coordinateToUnit (k := k) j).app U[j]
      (twistingSheaf.chartGenerator (-1) _ (coordinate_mem_one j) U[j] le_rfl) = 0 :=
    (congrArg (fun f : twistingSheaf 𝒜 (-1) ⟶ 𝟙_ (Proj 𝒜).Modules ↦
      f.app U[j] (twistingSheaf.chartGenerator (-1) _
        (coordinate_mem_one j) U[j] le_rfl)) h)
  have : Nontrivial Γ(P, U[j]) := (polynomialChartSectionsEquiv k j).injective.nontrivial
  have h01 : (0 : Γ(P, U[j])) = 1 :=
    hz.symm.trans (he.trans (polynomialCoordinateRatio_self j le_rfl))
  exact zero_ne_one h01

/-- Each coordinate hyperplane is an effective Cartier divisor. -/
theorem isEffectiveCartier_coordinateHyperplaneIdeal (j : Fin (n + 1)) :
    (coordinateHyperplaneIdeal (k := k) j).IsEffectiveCartier :=
  letI : Mono ((coordinateToUnit (k := k) j) :
    (polynomialTwistingBundle (-1)).obj ⟶ 𝟙_ (Proj 𝒜).Modules) := mono_coordinateToUnit j
  (polynomialTwistingBundle (k := k) (n := n) (-1)).isEffectiveCartier_imageIdealSheaf
    (coordinateToUnit j)

private theorem uniqueFactorizationMonoid_stalk_polynomialProj (x : P) :
    UniqueFactorizationMonoid ((Proj 𝒜).presheaf.stalk x) := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_coordinateChart (k := k) (n := n)).symm ▸ (show x ∈ (⊤ : (Proj 𝒜).Opens) from trivial))
  have : UniqueFactorizationMonoid Γ(P, U[i]) :=
    (polynomialChartSectionsEquiv k i).toMulEquiv.uniqueFactorizationMonoid inferInstance
  let := ((Proj 𝒜).presheaf.germ U[i] x hi).hom.toAlgebra
  have := (coordinateChart (k := k) i).property.isLocalization_stalk ⟨x, hi⟩
  exact UniqueFactorizationMonoid.of_isLocalization
    ((coordinateChart (k := k) i).property.primeIdealOf ⟨x, hi⟩).asIdeal.primeCompl _

private theorem subsingleton_picard_coordinateChart (i : Fin (n + 1)) :
    Subsingleton (LineBundleClass U[i].toScheme) := by
  let e := basicOpenIsoSpec 𝒜 _ (coordinate_mem_one i) one_pos
  have : UniqueFactorizationMonoid (Away 𝒜 (MvPolynomial.X i)) :=
    (awayCoordinateAlgEquiv (k := k) i).symm.toMulEquiv.uniqueFactorizationMonoid inferInstance
  have : IsDomain (Away 𝒜 (MvPolynomial.X i)) :=
    (awayCoordinateAlgEquiv (k := k) i).injective.isDomain
      (awayCoordinateAlgEquiv (k := k) i).toRingHom
  let : StrongNormalizationMonoid (Away 𝒜 (MvPolynomial.X i)) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let : NormalizedGCDMonoid (Away 𝒜 (MvPolynomial.X i)) :=
    UniqueFactorizationMonoid.toNormalizedGCDMonoid _
  have := LineBundleClass.subsingleton_spec (Away 𝒜 (MvPolynomial.X i))
  exact (LineBundleClass.pullbackEquiv e.symm).injective.subsingleton

private theorem isNoetherian_polynomialProj : IsNoetherian (Proj 𝒜) := by
  apply (isNoetherian_iff _).2
  refine ⟨(isLocallyNoetherian_iff_of_iSup_eq_top iSup_coordinateChart).2 fun i ↦ ?_, ?_⟩
  · exact isNoetherianRing_of_ringEquiv _ (polynomialChartSectionsEquiv k i).toRingEquiv
  · constructor
    have he : (⋃ i : Fin (n + 1), (U[i] : Set P)) = Set.univ := by
      simpa only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top] using
        congrArg (fun U : (Proj 𝒜).Opens ↦ (U : Set P)) (iSup_coordinateChart (k := k) (n := n))
    rw [← he]
    exact isCompact_iUnion fun i ↦ (coordinateChart (k := k) i).property.isCompact

open LineBundleClass in
private theorem exists_zpow_polynomialTwistingBundle [NeZero n] (a : LineBundleClass (Proj 𝒜)) :
    ∃ m : ℤ, mk (polynomialTwistingBundle 1) ^ m = a := by
  classical
  have := isIntegral_polynomialProj (R := k) (σ := Fin (n + 1))
  have := isNoetherian_polynomialProj (k := k) (n := n)
  have := uniqueFactorizationMonoid_stalk_polynomialProj (k := k) (n := n)
  let i : Fin (n + 1) := 0
  let I := coordinateHyperplaneIdeal (k := k) i
  have := isIntegral_subscheme_coordinateHyperplaneIdeal (k := k) i
  let hI := isEffectiveCartier_coordinateHyperplaneIdeal (k := k) i
  let η : CodimensionOnePoint (Proj 𝒜) :=
    ⟨I.subschemeι (genericPoint I.subscheme), hI.coheight_subschemeι_genericPoint⟩
  have hmem (x : CodimensionOnePoint (Proj 𝒜)) :
      (x : P) ∉ Set.range (U[i]).ι ↔ x = η := by
    rw [Scheme.Opens.range_ι, ← Set.mem_compl_iff, ← coe_support_coordinateHyperplaneIdeal]
    exact (hI.mem_support_iff_eq_subschemeι_genericPoint x.property).trans
      ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  have hset : {primeDivisorClass x | (x : CodimensionOnePoint (Proj 𝒜))
      (_ : (x : P) ∉ Set.range (U[i]).ι)} = {primeDivisorClass η} := by
    ext b
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [(hmem x).mp hx]
      exact Set.mem_singleton _
    · intro hb
      exact ⟨η, (hmem η).mpr rfl, (Set.mem_singleton_iff.mp hb).symm⟩
  have hc : primeDivisorClass η = mk (polynomialTwistingBundle (k := k) (n := n) 1) := by
    have : Mono (coordinateToUnit (k := k) i) := mono_coordinateToUnit i
    rw [primeDivisorClass_def, mk_toInvertibleSheaf_congr _ hI
      I.vanishingIdeal_closure_subschemeι_genericPoint]
    have he : mk hI.toInvertibleSheaf = mk (polynomialTwistingBundle (-1)) :=
      (polynomialTwistingBundle (k := k) (n := n) (-1)).mk_toInvertibleSheaf_imageIdealSheaf
        (coordinateToUnit i)
    have hz : mk (polynomialTwistingBundle (k := k) (n := n) (-1)) =
        mk (polynomialTwistingBundle 1) ^ (-1 : ℤ) :=
      lineBundleClass_twistingSheaf_eq_zpow
        (fun i : ULift.{u} (Fin (n + 1)) ↦ (MvPolynomial.X i.down : MvPolynomial (Fin (n + 1)) k))
        (fun i ↦ coordinate_mem_one i.down)
        (by simpa only [iSup_ulift] using iSup_coordinateChart (k := k) (n := n)) (-1)
    rw [he, hz, zpow_neg_one, inv_inv]
  have := subsingleton_picard_coordinateChart (k := k) i
  have h : pullback (U[i]).ι a = 1 := Subsingleton.elim _ _
  rw [pullback_eq_one_iff_mem_closure_of_isOpenImmersion, hset, hc,
    ← Subgroup.zpowers_eq_closure, Subgroup.mem_zpowers_iff] at h
  exact h

/-- The invertible sheaf `𝒪(m)` on the projective spectrum of a symmetric algebra. -/
def symmetricAlgebraTwistingBundle (k M : Type u) [CommRing k] [AddCommMonoid M] [Module k M]
    (m : ℤ) : InvertibleSheaf (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k M)) :=
  ⟨twistingSheaf _ m, inferInstance⟩

/-- The underlying module sheaf of the bundled twist is the native twisting sheaf. -/
@[simp]
theorem symmetricAlgebraTwistingBundle_obj (R M : Type u) [CommRing R] [AddCommMonoid M]
    [Module R M] (m : ℤ) :
    (symmetricAlgebraTwistingBundle R M m).obj =
      twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M) m :=
  (rfl)

end AlgebraicGeometry.Proj

namespace Module.Basis

open AlgebraicGeometry AlgebraicGeometry.Proj LineBundleClass

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k M : Type u} [Field k] [AddCommMonoid M] [Module k M] {n : ℕ}

local notation "𝒮" => TauCeti.SymmetricAlgebra.homogeneousSubmodule k M

private theorem pullbackEquiv_polynomialProjIso_twist (b : Basis (Fin (n + 2)) k M) (m : ℤ) :
    pullbackEquiv (polynomialProjIso b)
        (LineBundleClass.mk (symmetricAlgebraTwistingBundle k M m)) =
      LineBundleClass.mk (polynomialTwistingBundle m) := by
  rw [pullbackEquiv_apply, pullback_mk, mk_eq_mk_iff]
  refine ⟨?_⟩
  rw [InvertibleSheaf.pullback_obj_obj, symmetricAlgebraTwistingBundle_obj]
  exact b.polynomialProjIsoPullbackTwistingSheafIso m

private theorem mk_symmetricAlgebraTwistingBundle_eq_zpow (m : ℤ) :
    LineBundleClass.mk (symmetricAlgebraTwistingBundle k M m) =
      LineBundleClass.mk (symmetricAlgebraTwistingBundle k M 1) ^ m :=
  lineBundleClass_twistingSheaf_eq_zpow (SymmetricAlgebra.ι k M)
    (TauCeti.SymmetricAlgebra.ι_mem_homogeneousSubmodule k M)
    (TauCeti.SymmetricAlgebra.iSup_basicOpen_ι_eq_top k M id (by simp)) m

private theorem exists_zpow_symmetricAlgebraTwistingBundle (b : Basis (Fin (n + 2)) k M)
    (a : LineBundleClass (Proj 𝒮)) :
    ∃ m : ℤ, LineBundleClass.mk (symmetricAlgebraTwistingBundle k M 1) ^ m = a := by
  let e := pullbackEquiv (polynomialProjIso b)
  obtain ⟨m, hm⟩ := exists_zpow_polynomialTwistingBundle (e a)
  refine ⟨m, e.injective ?_⟩
  rw [map_zpow, pullbackEquiv_polynomialProjIso_twist]
  exact hm

private theorem mk_symmetricAlgebraTwistingBundle_ne_one_of_neg
    (b : Basis (Fin (n + 2)) k M) {m : ℤ} (hm : m < 0) :
    LineBundleClass.mk (symmetricAlgebraTwistingBundle k M m) ≠ 1 := by
  intro h
  obtain ⟨e⟩ := mk_eq_one_iff.mp h
  have : Nontrivial M := ⟨⟨b 0, 0, b.ne_zero 0⟩⟩
  have : Module.Free k M := Module.Free.of_basis b
  have : IsIntegral (Proj 𝒮) := inferInstance
  have : Nonempty (⊤ : (Proj 𝒮).Opens) := ⟨⟨genericPoint (Proj 𝒮), trivial⟩⟩
  have : Subsingleton Γ((symmetricAlgebraTwistingBundle k M m).obj, ⊤) := by
    rw [symmetricAlgebraTwistingBundle_obj]
    exact ⟨fun s t ↦ (TauCeti.SymmetricAlgebra.twistingSheaf_top_eq_zero_of_neg hm b s).trans
      (TauCeti.SymmetricAlgebra.twistingSheaf_top_eq_zero_of_neg hm b t).symm⟩
  let e' := ((Scheme.Modules.toPresheaf (Proj 𝒮)).mapIso e).app (op ⊤)
  have hinj : Function.Injective (fun x : Γ(Proj 𝒮, ⊤) ↦
      (e.inv.app ⊤ x : Γ(twistingSheaf 𝒮 m, ⊤))) :=
    (ConcreteCategory.bijective_of_isIso e'.inv).injective
  have he : Subsingleton Γ(Proj 𝒮, ⊤) := hinj.subsingleton
  exact zero_ne_one (he.elim 0 1)

/-- The Picard group of projective space of positive dimension over a field is the integers.
The inverse takes `m` to the class of `𝒪(m)`. -/
def picardTwistEquiv (b : Basis (Fin (n + 2)) k M) :
    Additive (LineBundleClass (Proj 𝒮)) ≃+ ℤ := by
  let f : Multiplicative ℤ →* LineBundleClass (Proj 𝒮) :=
    MonoidHom.mk' (fun m ↦ LineBundleClass.mk (symmetricAlgebraTwistingBundle k M 1) ^ m.toAdd)
      (fun m l ↦ zpow_add _ m.toAdd l.toAdd)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).2
    intro m hm
    have he : LineBundleClass.mk (symmetricAlgebraTwistingBundle k M 1) ^ m.toAdd = 1 := hm
    by_contra h
    have hne : m.toAdd ≠ 0 := h
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact mk_symmetricAlgebraTwistingBundle_ne_one_of_neg b hneg
        ((mk_symmetricAlgebraTwistingBundle_eq_zpow _).trans he)
    · exact mk_symmetricAlgebraTwistingBundle_ne_one_of_neg b (neg_lt_zero.mpr hpos)
        (by rw [mk_symmetricAlgebraTwistingBundle_eq_zpow, zpow_neg, he, inv_one])
  have hs : Function.Surjective f := fun a ↦ by
    obtain ⟨m, hm⟩ := exists_zpow_symmetricAlgebraTwistingBundle b a
    exact ⟨Multiplicative.ofAdd m, hm⟩
  exact (MulEquiv.ofBijective f ⟨hf, hs⟩).toAdditive.symm

/-- Under the inverse Picard identification, an integer gives the class of its twist. -/
@[simp]
theorem picardTwistEquiv_symm_apply (b : Basis (Fin (n + 2)) k M) (m : ℤ) :
    (b.picardTwistEquiv.symm m).toMul =
      LineBundleClass.mk (symmetricAlgebraTwistingBundle k M m) :=
  (mk_symmetricAlgebraTwistingBundle_eq_zpow m).symm

/-- The class of `𝒪(m)` has coordinate `m` in the Picard group. -/
@[simp]
theorem picardTwistEquiv_apply_twist (b : Basis (Fin (n + 2)) k M) (m : ℤ) :
    b.picardTwistEquiv
      (Additive.ofMul (LineBundleClass.mk (symmetricAlgebraTwistingBundle k M m))) = m := by
  rw [← b.picardTwistEquiv_symm_apply m]
  exact b.picardTwistEquiv.apply_symm_apply m

end Module.Basis

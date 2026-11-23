/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Cohomology.TracePairing
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Trace
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Cohomology
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Integral
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.TopDual
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.TwistingSheaf
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

/-!
# Top-degree Serre duality on the projective plane

The pairing on a line bundle is evaluation followed by the coordinate-normalized trace
on the top forms. It is perfect by the top-degree surjectivity of evaluation by a nonzero
section and the dimension calculation for complementary twists of the structure sheaf.

* [Stacks Project, Lemma 48.27.1(6–7)](https://stacks.math.columbia.edu/tag/0FVV)
  for the duality statement.
* [Stacks Project, Lemma 30.8.1](https://stacks.math.columbia.edu/tag/01XT)
  for the twist cohomology, used through Tau Ceti's
  `Module.Basis.nonempty_linearEquiv_cohomology_top_twistingSheaf_dual` and
  `SymmetricAlgebra.cohomologyZeroTwistingSheafLinearEquiv`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonoidalClosed
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules LineBundleClass

namespace AlgebraicGeometry.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra planeOver planeSmooth

variable (k : Type u)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 3) k
local notation "P" => Proj 𝒜
local notation "Ω₂" => Functor.obj (SheafOfModules.exteriorPower (Scheme.sheaf P) 2)
  (Scheme.relativeDifferentials k P)

variable [CommRing k] in
/-- The pairing of a second cohomology class with a section of the canonical twist
of the dual line bundle on the polynomial projective plane. It uses the normalized
trace on the canonical bundle and the morphism represented by the section. -/
def polynomialPlaneCanonicalPairing (L : InvertibleSheaf P) :
    Cohomology L.obj 2 →ₗ[k] Γ((ihom L.obj).obj Ω₂, ⊤) →ₗ[k] k :=
  cohomologyTracePairing k 2 (polynomialPlaneCanonicalTrace k).toLinearMap

variable [CommRing k] in
/-- The projective-plane pairing evaluates the section and then takes the normalized trace. -/
@[simp]
theorem polynomialPlaneCanonicalPairing_apply (L : InvertibleSheaf P) (x : Cohomology L.obj 2)
    (s : Γ((ihom L.obj).obj Ω₂, ⊤)) :
    polynomialPlaneCanonicalPairing k L x s =
      polynomialPlaneCanonicalTrace k
        (cohomologyMapBaseLinear k P (internalHomSectionsEquiv s) 2 x) :=
  cohomologyTracePairing_apply k 2 (polynomialPlaneCanonicalTrace k).toLinearMap x s

variable [Field k]

private theorem plane_over_eq_toSpecCoeff :
    P ↘ Spec (.of k) = toSpecCoeff 𝒜 := by
  rfl

private def planeCanonicalBundle : InvertibleSheaf P :=
  ⟨Ω₂, by
    rw [← differentialForms_def k P 2]
    exact isInvertible_differentialForms k P 2⟩

private theorem nonempty_iso_internalHom_planeCanonicalTwist
    (L : InvertibleSheaf P) (m : ℤ)
    (e : L.obj ≅ (polynomialTwistingBundle m).obj) :
    Nonempty ((ihom L.obj).obj Ω₂ ≅ twistingSheaf 𝒜 (-3 - m)) := by
  let K := planeCanonicalBundle k
  let F := L.dual.tensorProduct K
  have hK : mk K = mk (polynomialTwistingBundle (-3)) := by
    apply mk_eq_mk_iff.mpr
    rw [polynomialTwistingBundle_obj]
    exact ⟨differentialFormsTwoIsoTwistingSheaf k⟩
  have hF : mk F = mk (polynomialTwistingBundle (-3 - m)) := by
    rw [mk_tensorProduct, ← inv_mk, hK, mk_eq_mk_iff.mpr ⟨e⟩,
      mk_polynomialTwistingBundle_eq_zpow (-3 - m), mk_polynomialTwistingBundle_eq_zpow (-3),
      mk_polynomialTwistingBundle_eq_zpow m, ← zpow_neg, ← zpow_add]
    congr 1
    omega
  obtain ⟨eF⟩ := mk_eq_mk_iff.mp hF
  rw [← polynomialTwistingBundle_obj]
  exact ⟨((asIso (dualTensorIhom L.obj)).app K.obj).symm ≪≫
    (eqToIso (congrArg (· ⊗ K.obj) (InvertibleSheaf.dual_obj L))).symm ≪≫
    (InvertibleSheaf.tensorProductObjIso L.dual K).symm ≪≫ eF⟩

private theorem cohomologyTwoTwist_finrank_eq_cohomologyZeroTwist (m : ℤ) :
    Module.finrank k (Cohomology (twistingSheaf 𝒜 m) 2) =
      Module.finrank k (Cohomology (twistingSheaf 𝒜 (-3 - m)) 0) := by
  let b := Pi.basisFun k (Fin 3)
  let e₂ := b.cohomologyPolynomialTwistingSheafLinearEquiv (plane_over_eq_toSpecCoeff k) m 2
  let e₀ := b.cohomologyPolynomialTwistingSheafLinearEquiv (plane_over_eq_toSpecCoeff k) (-3 - m) 0
  refine e₂.finrank_eq.trans (Eq.trans ?_ e₀.finrank_eq.symm)
  by_cases hm : -3 < m
  · have := b.subsingleton_cohomology_twistingSheaf_of_neg_card_lt (m := m)
      (by rw [Fintype.card_fin]; exact hm) (q := 2) (by decide)
    have := SymmetricAlgebra.subsingleton_cohomology_zero_twistingSheaf_of_neg
      (n := -3 - m) (by omega) b
    rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]
  · let j := (-3 - m).toNat
    have hj : (j : ℤ) = -3 - m := Int.toNat_of_nonneg (by omega)
    obtain ⟨e⟩ := b.nonempty_linearEquiv_cohomology_top_twistingSheaf_dual m
      (n := 1) (j := j) (Fintype.card_fin 3) (by rw [hj, Fintype.card_fin]; omega)
    have := Module.Finite.of_basis (b.symmetricAlgebraHomogeneous j)
    rw [e.finrank_eq, Subspace.dual_finrank_eq, ← hj]
    exact (SymmetricAlgebra.cohomologyZeroTwistingSheafLinearEquiv j b).finrank_eq.symm

/-- The normalized top-degree Serre pairing is perfect for every line bundle on the
projective plane over an infinite field. -/
theorem isPerfPair_polynomialPlaneCanonicalPairing [Infinite k] (L : InvertibleSheaf P) :
    (polynomialPlaneCanonicalPairing k L).IsPerfPair := by
  obtain ⟨m, ⟨e⟩⟩ := exists_iso_polynomialTwistingBundle L
  obtain ⟨eΩ⟩ := nonempty_iso_internalHom_planeCanonicalTwist k L m e
  let Liso : L.obj ≅ twistingSheaf 𝒜 m :=
    e ≪≫ eqToIso (polynomialTwistingBundle_obj m)
  let b := Pi.basisFun k (Fin 3)
  let e₂ := cohomologyBaseLinearEquivOfIso (X := P) k Liso 2
  let e₀ := (cohomologyZeroBaseLinearEquiv k P ((ihom L.obj).obj Ω₂)).symm.trans
    (cohomologyBaseLinearEquivOfIso k eΩ 0)
  let e₂' := b.cohomologyPolynomialTwistingSheafLinearEquiv (plane_over_eq_toSpecCoeff k) m 2
  let e₀' := b.cohomologyPolynomialTwistingSheafLinearEquiv (plane_over_eq_toSpecCoeff k) (-3 - m) 0
  have := b.finite_cohomology_top_twistingSheaf m (n := 1) (Fintype.card_fin 3)
  have := Module.Finite.equiv (e₂.trans e₂').symm
  have := SymmetricAlgebra.finite_cohomology_zero_twistingSheaf (-3 - m) b
  have := Module.Finite.equiv (e₀.trans e₀').symm
  have hdim : Module.finrank k Γ((ihom L.obj).obj Ω₂, ⊤) =
      Module.finrank k (Module.Dual k (Cohomology L.obj 2)) :=
    e₀.finrank_eq.trans ((cohomologyTwoTwist_finrank_eq_cohomologyZeroTwist k m).symm.trans
      (e₂.finrank_eq.symm.trans Subspace.dual_finrank_eq.symm))
  have : IsIntegral P := isIntegral_polynomialProj (R := k) (σ := Fin 3)
  let eP := b.polynomialProjIso
  have : eP.hom.IsOver (Spec (.of k)) := ⟨by
    rw [SymmetricAlgebra.over_eq_projToSpec, plane_over_eq_toSpecCoeff]
    exact b.polynomialProjIso_hom_over⟩
  have : (P).IsProjectiveOver k := Scheme.IsProjectiveOver.of_isClosedImmersion k eP.hom
  have hdimP : topologicalKrullDim P ≤ (2 : ℕ) :=
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension (P ↘ Spec (.of k)) (n := 2)).le
  have htr : (polynomialPlaneCanonicalTrace k).toLinearMap ≠ 0 := by
    intro he
    have h := DFunLike.congr_fun he ((polynomialPlaneCanonicalTrace k).symm 1)
    exact one_ne_zero ((LinearEquiv.apply_symm_apply _ _).symm.trans h)
  have hi := InvertibleSheaf.cohomologyTracePairing_injective_flip k L
    (planeCanonicalBundle k) hdimP _ htr
  have hp := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (polynomialPlaneCanonicalPairing k L).flip)).mp hi
  exact (LinearMap.IsPerfPair.of_bijective _ ⟨hi, hp⟩).flip

end AlgebraicGeometry.Proj

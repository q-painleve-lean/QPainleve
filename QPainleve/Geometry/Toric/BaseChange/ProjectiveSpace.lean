/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import QPainleve.Geometry.Toric.BaseChange.Fan.Map
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.Geometry.Toric.Algebraic.Fan.ProjectiveSpace.Coordinates
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Grading
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic
import TauCeti.RingTheory.Localization.Away.Basic

/-!
# Toric projective space over a ring

The fan of projective space realizes the projective spectrum of the symmetric
algebra over any commutative ring. On the chart omitting a ray, the ratio of a
homogeneous coordinate by the omitted coordinate is the monomial of its ratio
character. These chart isomorphisms glue on the common faces.
-/

public section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization Multiplicative AddMonoidAlgebra

namespace TauCeti.Toric

universe u

section Charts

variable (R : Type u) [CommRing R]

/-! ### Ratios of homogeneous coordinates -/

section Ratio

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [Fintype ι] (b : Module.Basis ι ℤ N) {i : N →+ V} (hi : IsIntegralLattice i)
  {σ : PointedCone ℝ V}

/-- The monomial of the homogeneous-coordinate ratio `X_j / X_k` on the affine chart of a cone
contained in the maximal cone omitting the ray `k`. -/
noncomputable def projectiveFanRatioMonomial {k : Option ι}
    (hσ : σ ≤ projectiveSpaceCone b i {k}ᶜ) (j : Option ι) : affineChartRing R hi σ :=
  AddMonoidAlgebra.single ⟨projectiveSpaceRatioCharacter b j k,
    dualSemigroup_anti hi hσ
      (projectiveSpaceRatioCharacter_mem_dualSemigroup b hi j k (by simp))⟩ 1

variable {b hi}

/-- The ratio monomial `X_j / X_k` is the monomial of the ratio character. -/
theorem projectiveFanRatioMonomial_def {k : Option ι}
    (hσ : σ ≤ projectiveSpaceCone b i {k}ᶜ) (j : Option ι) :
    projectiveFanRatioMonomial R b hi hσ j =
      AddMonoidAlgebra.single ⟨projectiveSpaceRatioCharacter b j k,
        dualSemigroup_anti hi hσ
          (projectiveSpaceRatioCharacter_mem_dualSemigroup b hi j k (by simp))⟩ 1 :=
  (rfl)

/-- The ratio `X_k / X_k` is `1`. -/
@[simp]
theorem projectiveFanRatioMonomial_self {k : Option ι}
    (hσ : σ ≤ projectiveSpaceCone b i {k}ᶜ) : projectiveFanRatioMonomial R b hi hσ k = 1 := by
  rw [projectiveFanRatioMonomial, AddMonoidAlgebra.one_def]
  congr
  ext1
  simp

/-- The ratio monomials multiply as the ratios do: `(X_k / X_l) (X_j / X_k) = X_j / X_l`. -/
theorem projectiveFanRatioMonomial_mul {k l : Option ι}
    (hk : σ ≤ projectiveSpaceCone b i {k}ᶜ) (hl : σ ≤ projectiveSpaceCone b i {l}ᶜ)
    (j : Option ι) :
    projectiveFanRatioMonomial R b hi hl k * projectiveFanRatioMonomial R b hi hk j =
      projectiveFanRatioMonomial R b hi hl j := by
  rw [projectiveFanRatioMonomial, projectiveFanRatioMonomial, projectiveFanRatioMonomial,
    AddMonoidAlgebra.single_mul_single, one_mul]
  congr
  exact Subtype.ext ((add_comm _ _).trans (projectiveSpaceRatioCharacter_add b j k l))

/-- On a cone contained in the maximal cones omitting `k` and `l`, the ratio `X_l / X_k` is a
unit. -/
theorem isUnit_projectiveFanRatioMonomial {k l : Option ι}
    (hk : σ ≤ projectiveSpaceCone b i {k}ᶜ) (hl : σ ≤ projectiveSpaceCone b i {l}ᶜ) :
    IsUnit (projectiveFanRatioMonomial R b hi hk l) :=
  .of_mul_eq_one (projectiveFanRatioMonomial R b hi hl k) <| by
    rw [mul_comm, projectiveFanRatioMonomial_mul R hk hl, projectiveFanRatioMonomial_self R]

/-- Restricting a ratio monomial to a face gives the same ratio monomial. -/
@[simp]
theorem faceAffineChartRingMap_projectiveFanRatioMonomial {τ : PointedCone ℝ V}
    {k : Option ι} (hτσ : τ.IsFaceOf σ) (hσ : σ ≤ projectiveSpaceCone b i {k}ᶜ)
    (j : Option ι) :
    faceAffineChartRingMap R hi hτσ (projectiveFanRatioMonomial R b hi hσ j) =
      projectiveFanRatioMonomial R b hi (hτσ.le.trans hσ) j := by
  rw [projectiveFanRatioMonomial, faceAffineChartRingMap_single]
  rfl

end Ratio

/-! ### Homogeneous coordinates on the affine charts -/

section HomogeneousCoordinates

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [Fintype ι] (b : Module.Basis ι ℤ N) {i : N →+ V} (hi : IsIntegralLattice i)
  {σ : PointedCone ℝ V}

local notation "𝒜" => SymmetricAlgebra.homogeneousSubmodule R (Option ι → R)
local notation "X" j => _root_.SymmetricAlgebra.ι R (Option ι → R) (Pi.single j 1)

/-- The homogeneous coordinates on the affine chart of a cone contained in the maximal cone
omitting the ray `k`, normalized by `X_k = 1`: the coordinate `X_j` is the monomial of the ratio
`X_j / X_k`. -/
noncomputable def projectiveFanHomogeneousCoordinates {k : Option ι}
    (hσ : σ ≤ projectiveSpaceCone b i {k}ᶜ) :
    _root_.SymmetricAlgebra R (Option ι → R) →ₐ[R] affineChartRing R hi σ :=
  _root_.SymmetricAlgebra.lift
    ((Pi.basisFun R (Option ι)).constr R (projectiveFanRatioMonomial R b hi hσ))

variable {b hi}

/-- The homogeneous coordinate `X_j` is the monomial of the ratio `X_j / X_k`. -/
@[simp]
theorem projectiveFanHomogeneousCoordinates_coord [DecidableEq ι] {k : Option ι}
    (hσ : σ ≤ projectiveSpaceCone b i {k}ᶜ) (j : Option ι) :
    projectiveFanHomogeneousCoordinates R b hi hσ (X j) =
      projectiveFanRatioMonomial R b hi hσ j := by
  rw [projectiveFanHomogeneousCoordinates, _root_.SymmetricAlgebra.lift_ι_apply,
    ← Pi.basisFun_apply R, Module.Basis.constr_basis]

/-- On a cone contained in the maximal cone omitting `l`, the homogeneous coordinate `X_l` is
invertible. -/
theorem isUnit_projectiveFanHomogeneousCoordinates_coord [DecidableEq ι] {k l : Option ι}
    (hk : σ ≤ projectiveSpaceCone b i {k}ᶜ) (hl : σ ≤ projectiveSpaceCone b i {l}ᶜ) :
    IsUnit (projectiveFanHomogeneousCoordinates R b hi hk (X l)) := by
  rw [projectiveFanHomogeneousCoordinates_coord R]
  exact isUnit_projectiveFanRatioMonomial R hk hl

/-- Changing the normalizing coordinate from `X_k` to `X_l` multiplies the linear homogeneous
coordinates by the ratio `X_k / X_l`. -/
theorem projectiveFanHomogeneousCoordinates_ι_eq_mul {k l : Option ι}
    (hk : σ ≤ projectiveSpaceCone b i {k}ᶜ) (hl : σ ≤ projectiveSpaceCone b i {l}ᶜ)
    (m : Option ι → R) :
    projectiveFanHomogeneousCoordinates R b hi hl (_root_.SymmetricAlgebra.ι R _ m) =
      projectiveFanRatioMonomial R b hi hl k *
        projectiveFanHomogeneousCoordinates R b hi hk (_root_.SymmetricAlgebra.ι R _ m) := by
  classical
  have h : (projectiveFanHomogeneousCoordinates R b hi hl).toLinearMap ∘ₗ
      _root_.SymmetricAlgebra.ι R _ =
      LinearMap.mulLeft R (projectiveFanRatioMonomial R b hi hl k) ∘ₗ
        (projectiveFanHomogeneousCoordinates R b hi hk).toLinearMap ∘ₗ
          _root_.SymmetricAlgebra.ι R _ :=
    (Pi.basisFun R (Option ι)).ext fun j ↦ by
      simp [projectiveFanRatioMonomial_mul R hk hl]
  exact LinearMap.congr_fun h m

/-- Changing the normalizing coordinate from `X_k` to `X_l` multiplies the homogeneous
polynomials of degree `n` by the `n`-th power of the ratio `X_k / X_l`. -/
theorem projectiveFanHomogeneousCoordinates_eq_pow_mul {k l : Option ι}
    (hk : σ ≤ projectiveSpaceCone b i {k}ᶜ) (hl : σ ≤ projectiveSpaceCone b i {l}ᶜ) {n : ℕ}
    {a : _root_.SymmetricAlgebra R (Option ι → R)} (ha : a ∈ 𝒜 n) :
    projectiveFanHomogeneousCoordinates R b hi hl a =
      projectiveFanRatioMonomial R b hi hl k ^ n *
        projectiveFanHomogeneousCoordinates R b hi hk a :=
  AlgHom.apply_eq_pow_mul_of_forall_ι_eq _ _ _
    (projectiveFanHomogeneousCoordinates_ι_eq_mul R hk hl) ha

/-- Restricting the homogeneous coordinates of a chart to a face gives the homogeneous
coordinates of the face. -/
@[simp]
theorem faceAffineChartRingMap_comp_projectiveFanHomogeneousCoordinates
    {τ : PointedCone ℝ V} {k : Option ι} (hτσ : τ.IsFaceOf σ)
    (hσ : σ ≤ projectiveSpaceCone b i {k}ᶜ) :
    (faceAffineChartRingMap R hi hτσ).comp (projectiveFanHomogeneousCoordinates R b hi hσ) =
      projectiveFanHomogeneousCoordinates R b hi (hτσ.le.trans hσ) :=
  _root_.SymmetricAlgebra.algHom_ext <| (Pi.basisFun R (Option ι)).ext fun j ↦ by
    classical
    simp

/-! ### The chart of a maximal cone -/

variable [DecidableEq ι] (b hi) (k : Option ι)

omit [Fintype ι] in
/-- The homogeneous coordinate `X_j` has degree one. -/
private theorem coord_mem (j : Option ι) : (X j) ∈ 𝒜 1 :=
  SymmetricAlgebra.ι_mem_homogeneousSubmodule R _ _

/-- The fraction `X_j / X_k` in the ring of the standard chart `D₊(X_k)`. -/
private noncomputable def awayRatio (j : Option ι) : Away 𝒜 (X k) :=
  Away.mk 𝒜 (coord_mem R k) 1 (X j) (by simp)

omit [Fintype ι] in
private theorem val_awayRatio (j : Option ι) :
    (awayRatio R k j).val =
      IsLocalization.Away.invSelf (X k) * algebraMap _ (Localization.Away (X k)) (X j) := by
  rw [awayRatio, Away.val_mk, Localization.mk_eq_mk', ← pow_one (IsLocalization.Away.invSelf _),
    ← TauCeti.Localization.mk'_pow_eq_invSelf_pow_mul]

omit [Fintype ι] in
private theorem awayRatio_self : awayRatio R k k = 1 :=
  Away.mk_self _ _

/-- The characters of the maximal cone omitting `k` act on the chart `D₊(X_k)`: a character with
exponents `a_j` along the rays `j ≠ k` goes to `∏ (X_j / X_k) ^ a_j`. -/
private noncomputable def awayMonoidHom :
    Multiplicative (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)) →* Away 𝒜 (X k) where
  toFun m := ∏ j, awayRatio R k j.val ^ projectiveSpaceDualSemigroupEquiv b hi k (toAdd m) j
  map_one' := by simp
  map_mul' m m' := by
    simp only [toAdd_mul, map_add, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

/-- The homomorphism from the coordinate ring of the maximal cone omitting `k` to the ring of the
chart `D₊(X_k)`. -/
private noncomputable def toAway :
    affineChartRing R hi (projectiveSpaceCone b i {k}ᶜ) →ₐ[R] Away 𝒜 (X k) :=
  AddMonoidAlgebra.lift R _ _ (awayMonoidHom R b hi k)

private theorem awayMonoidHom_apply
    (m : dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)) :
    awayMonoidHom R b hi k (ofAdd m) =
      ∏ j, awayRatio R k j.val ^ projectiveSpaceDualSemigroupEquiv b hi k m j :=
  (rfl)

omit [DecidableEq ι] in
private theorem projectiveFanRatioMonomial_eq_single {j : Option ι} (hj : j ≠ k) :
    projectiveFanRatioMonomial R b hi le_rfl j =
      AddMonoidAlgebra.single (projectiveSpaceChartCharacter b hi k ⟨j, hj⟩) 1 := by
  rw [projectiveFanRatioMonomial]
  exact congrArg (fun m ↦ AddMonoidAlgebra.single m 1)
    (Subtype.ext (coe_projectiveSpaceChartCharacter b hi k ⟨j, hj⟩).symm)

private theorem toAway_projectiveFanRatioMonomial (j : Option ι) :
    toAway R b hi k (projectiveFanRatioMonomial R b hi le_rfl j) = awayRatio R k j := by
  by_cases hj : j = k
  · subst hj
    rw [projectiveFanRatioMonomial_self R, map_one, awayRatio_self R]
  · rw [projectiveFanRatioMonomial_eq_single R b hi k hj, toAway, AddMonoidAlgebra.lift_single,
      one_smul, awayMonoidHom_apply R, projectiveSpaceDualSemigroupEquiv_chartCharacter,
      Finset.prod_eq_single ⟨j, hj⟩ (fun l _ hl ↦ by simp [hl]) (by simp)]
    simp

/-- The homomorphism from the ring of the chart `D₊(X_k)` to the coordinate ring of the maximal
cone omitting `k`, given by the homogeneous coordinates with `X_k = 1`. -/
private noncomputable def ofAway :
    Away 𝒜 (X k) →ₐ[R] affineChartRing R hi (projectiveSpaceCone b i {k}ᶜ) where
  __ := Away.lift 𝒜 (projectiveFanHomogeneousCoordinates R b hi (le_refl _)).toRingHom
    (isUnit_projectiveFanHomogeneousCoordinates_coord R le_rfl le_rfl)
  commutes' c := by
    rw [HomogeneousLocalization.algebraMap_eq_comp, RingHom.comp_apply,
      ← HomogeneousLocalization.algebraMap_eq]
    exact (Away.lift_algebraMap _ _ _).trans (by simp)

private theorem ofAway_mk {n : ℕ} {a : _root_.SymmetricAlgebra R (Option ι → R)}
    (ha : a ∈ 𝒜 (n • 1)) :
    ofAway R b hi k (Away.mk 𝒜 (coord_mem R k) n a ha) =
      projectiveFanHomogeneousCoordinates R b hi le_rfl a := by
  simp [ofAway]

/-- A product of powers of the ratios `X_j / X_k` is the monomial of the corresponding sum of
ratio characters. -/
private theorem prod_projectiveFanRatioMonomial_pow (a : {j : Option ι // j ≠ k} → ℕ) :
    ∏ j, projectiveFanRatioMonomial R b hi le_rfl j.val ^ a j =
      AddMonoidAlgebra.single ((projectiveSpaceDualSemigroupEquiv b hi k).symm a) 1 := by
  rw [← toAdd_ofAdd ((projectiveSpaceDualSemigroupEquiv b hi k).symm a),
    projectiveSpaceDualSemigroupEquiv_symm_apply, ← AddMonoidAlgebra.of_apply, ofAdd_sum, map_prod]
  -- The general formula sums over `univ` built from classical decidable equality.
  refine Finset.prod_congr (by congr!) fun j _ ↦ ?_
  rw [projectiveFanRatioMonomial_eq_single R b hi k j.property, ofAdd_nsmul, map_pow,
    AddMonoidAlgebra.of_apply]
  rfl

private theorem ofAway_comp_toAway : (ofAway R b hi k).comp (toAway R b hi k) = AlgHom.id R _ := by
  refine AddMonoidAlgebra.algHom_ext (fun m ↦ ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, toAway, AddMonoidAlgebra.lift_single, one_smul,
    awayMonoidHom_apply R, map_prod]
  simp_rw [map_pow, awayRatio, ofAway_mk R, projectiveFanHomogeneousCoordinates_coord R]
  rw [prod_projectiveFanRatioMonomial_pow R, AddEquiv.symm_apply_apply, AlgHom.id_apply]

private theorem toAway_comp_ofAway : (toAway R b hi k).comp (ofAway R b hi k) = AlgHom.id R _ := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (coord_mem R k) z
  rw [AlgHom.comp_apply, ofAway_mk R, AlgHom.id_apply, Away.val_mk, Localization.mk_eq_mk',
    TauCeti.Localization.mk'_pow_eq_invSelf_pow_mul]
  let f := IsScalarTower.toAlgHom R (_root_.SymmetricAlgebra R (Option ι → R))
    (Localization.Away (X k))
  let g := (IsScalarTower.toAlgHom R (Away 𝒜 (X k)) (Localization.Away (X k))).comp
    ((toAway R b hi k).comp (projectiveFanHomogeneousCoordinates R b hi le_rfl))
  refine AlgHom.apply_eq_pow_mul_of_forall_ι_eq f g _ (fun m ↦ ?_) (by simpa using ha)
  have h : g.toLinearMap ∘ₗ _root_.SymmetricAlgebra.ι R _ =
      LinearMap.mulLeft R (IsLocalization.Away.invSelf (X k)) ∘ₗ f.toLinearMap ∘ₗ
        _root_.SymmetricAlgebra.ι R _ :=
    (Pi.basisFun R (Option ι)).ext fun j ↦ by
      simp [g, f, toAway_projectiveFanRatioMonomial R, HomogeneousLocalization.algebraMap_apply,
        val_awayRatio R]
  exact LinearMap.congr_fun h m

/-- **The affine chart of the maximal cone omitting `k` is the standard chart `D₊(X_k)` of
projective space**: the ring of `D₊(X_k)`, the degree-zero part of the localization of the
homogeneous coordinate ring away from `X_k`, is the coordinate ring of the cone. A fraction
`a / X_kⁿ` goes to the value of `a` at the homogeneous coordinates with `X_k = 1`. -/
noncomputable def projectiveFanAwayEquiv :
    Away 𝒜 (X k) ≃ₐ[R] affineChartRing R hi (projectiveSpaceCone b i {k}ᶜ) :=
  AlgEquiv.ofAlgHom (ofAway R b hi k) (toAway R b hi k) (ofAway_comp_toAway R b hi k)
    (toAway_comp_ofAway R b hi k)

/-- The isomorphism `projectiveFanAwayEquiv` sends `a / X_kⁿ` to the value of `a` at the
homogeneous coordinates with `X_k = 1`. -/
@[simp]
theorem projectiveFanAwayEquiv_mk {n : ℕ} {a : _root_.SymmetricAlgebra R (Option ι → R)}
    (ha : a ∈ 𝒜 (n • 1)) :
    projectiveFanAwayEquiv R b hi k
        (Away.mk 𝒜 (SymmetricAlgebra.ι_mem_homogeneousSubmodule R _ _) n a ha) =
      projectiveFanHomogeneousCoordinates R b hi le_rfl a :=
  ofAway_mk R b hi k ha

/-- The isomorphism `projectiveFanAwayEquiv` is the homomorphism `Away.lift` induced by the
homogeneous coordinates with `X_k = 1`. -/
theorem projectiveFanAwayEquiv_toRingHom :
    (projectiveFanAwayEquiv R b hi k).toAlgHom.toRingHom =
      Away.lift 𝒜 (projectiveFanHomogeneousCoordinates R b hi le_rfl).toRingHom
        (isUnit_projectiveFanHomogeneousCoordinates_coord R le_rfl le_rfl) :=
  (rfl)

end HomogeneousCoordinates

/-! ### The morphism to `Proj` -/

end Charts

section Scheme

variable (R : Type u) [CommRing R] {N : Type u} {ι : Type} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ N) {i : N →+ V} (hi : IsIntegralLattice i)
  {σ : PointedCone ℝ V}

local notation "𝒜" => SymmetricAlgebra.homogeneousSubmodule R (Option ι → R)
local notation "X" j => _root_.SymmetricAlgebra.ι R (Option ι → R) (Pi.single j 1)

/-- The morphism from the affine toric scheme of a cone contained in the maximal cone omitting
`k` to projective space `Proj R[X_j]`: the point with the homogeneous coordinates of the chart,
read on the standard chart `D₊(X_k)`. By `projectiveFanChartToProj_eq` it does not depend
on `k`. -/
noncomputable def projectiveFanChartToProj {k : Option ι}
    (hσ : σ ≤ projectiveSpaceCone b i {k}ᶜ) : affineChart R hi σ ⟶ Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom
    (Away.lift 𝒜 (projectiveFanHomogeneousCoordinates R b hi hσ).toRingHom
      (isUnit_projectiveFanHomogeneousCoordinates_coord R hσ hσ))) ≫
    Proj.awayι 𝒜 (X k) (SymmetricAlgebra.ι_mem_homogeneousSubmodule R _ _) one_pos

variable {b hi}

/-- The morphism `projectiveFanChartToProj` does not depend on the normalizing coordinate. -/
theorem projectiveFanChartToProj_eq {k l : Option ι}
    (hk : σ ≤ projectiveSpaceCone b i {k}ᶜ) (hl : σ ≤ projectiveSpaceCone b i {l}ᶜ) :
    projectiveFanChartToProj R b hi hk = projectiveFanChartToProj R b hi hl := by
  rw [projectiveFanChartToProj, projectiveFanChartToProj,
    Proj.SpecMap_awayLift_awayι_eq _ _ one_pos
      (SymmetricAlgebra.ι_mem_homogeneousSubmodule R _ _) one_pos _
      (isUnit_projectiveFanHomogeneousCoordinates_coord R hk hl)]
  congr 3
  exact (Away.lift_eq_of_forall_mem _ _ (isUnit_projectiveFanRatioMonomial R hl hk).unit
    (fun n a ha ↦ by simpa using projectiveFanHomogeneousCoordinates_eq_pow_mul R hk hl ha)
    (SymmetricAlgebra.ι_mem_homogeneousSubmodule R _ _) _ _).symm

/-- Restricting `projectiveFanChartToProj` to the chart of a face gives the morphism of the
face. -/
@[reassoc (attr := simp)]
theorem faceAffineChartMap_comp_projectiveFanChartToProj {τ : PointedCone ℝ V}
    {k : Option ι} (hτσ : τ.IsFaceOf σ) (hσ : σ ≤ projectiveSpaceCone b i {k}ᶜ) :
    faceAffineChartMap R hi hτσ ≫ projectiveFanChartToProj R b hi hσ =
      projectiveFanChartToProj R b hi (hτσ.le.trans hσ) := by
  rw [faceAffineChartMap_def, projectiveFanChartToProj, projectiveFanChartToProj,
    ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    RingHom.comp_homogeneousLocalizationAwayLift]
  congr 4
  exact congrArg AlgHom.toRingHom
    (faceAffineChartRingMap_comp_projectiveFanHomogeneousCoordinates R hτσ hσ)

/-- On the chart of the maximal cone omitting `k`, the morphism to `Proj` is the spectrum of the
isomorphism `projectiveFanAwayEquiv` followed by the standard chart `D₊(X_k)`. -/
theorem projectiveFanChartToProj_self (k : Option ι) :
    projectiveFanChartToProj R b hi (le_refl (projectiveSpaceCone b i {k}ᶜ)) =
      Spec.map (CommRingCat.ofHom (projectiveFanAwayEquiv R b hi k).toAlgHom.toRingHom) ≫
        Proj.awayι 𝒜 (X k) (SymmetricAlgebra.ι_mem_homogeneousSubmodule R _ _) one_pos := by
  rw [projectiveFanChartToProj, projectiveFanAwayEquiv_toRingHom R]

/-- The chart-ring isomorphism `projectiveFanAwayEquiv` is an isomorphism in `CommRingCat`. -/
private instance isIso_ofHom_projectiveFanAwayEquiv (k : Option ι) :
    IsIso (CommRingCat.ofHom (projectiveFanAwayEquiv R b hi k).toAlgHom.toRingHom) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (projectiveFanAwayEquiv R b hi k).bijective

/-- The affine chart of the maximal cone omitting `k` is an open subscheme of projective space. -/
instance isOpenImmersion_projectiveFanChartToProj (k : Option ι) :
    IsOpenImmersion (projectiveFanChartToProj R b hi (le_refl (projectiveSpaceCone b i {k}ᶜ))) := by
  rw [projectiveFanChartToProj_self R]
  infer_instance

/-- The affine chart of the maximal cone omitting `k` is the standard open `D₊(X_k)` of projective
space. -/
theorem opensRange_projectiveFanChartToProj (k : Option ι) :
    (projectiveFanChartToProj R b hi (le_refl (projectiveSpaceCone b i {k}ᶜ))).opensRange =
      Proj.basicOpen 𝒜 (X k) := by
  simp only [projectiveFanChartToProj_self R, Scheme.Hom.opensRange_comp_of_isIso,
    Proj.opensRange_awayι]

/-- In the chart of the maximal cone omitting `k`, the standard open `D₊(X_l)` of projective space
is the locus where the ratio `X_l / X_k` does not vanish. -/
theorem projectiveFanChartToProj_preimage_basicOpen (k l : Option ι) :
    projectiveFanChartToProj R b hi (le_refl (projectiveSpaceCone b i {k}ᶜ)) ⁻¹ᵁ
        Proj.basicOpen 𝒜 (X l) =
      PrimeSpectrum.basicOpen (projectiveFanRatioMonomial R b hi le_rfl l) := by
  rw [projectiveFanChartToProj_self R, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen 𝒜 (SymmetricAlgebra.ι_mem_homogeneousSubmodule R _ _) one_pos
      (SymmetricAlgebra.ι_mem_homogeneousSubmodule R _ _) one_pos,
    SpecMap_preimage_basicOpen]
  simp only [AlgHom.toRingHom_eq_coe, AlgEquiv.toAlgHom_toRingHom, ConcreteCategory.hom_ofHom,
    RingHom.coe_coe, projectiveFanAwayEquiv_mk R, pow_one,
    projectiveFanHomogeneousCoordinates_coord R]
  -- The two sides differ only in the ring structure of the coordinate ring seen through
  -- `CommRingCat.of`.
  rfl

end Scheme

/-! ### The toric scheme of the fan of projective space -/

namespace Fan

variable (R : Type u) [CommRing R] {N : Type u} {ι : Type} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ N) {i : N →+ V} (hi : IsIntegralLattice i)

local notation "𝒜" => SymmetricAlgebra.homogeneousSubmodule R (Option ι → R)
local notation "X" j => _root_.SymmetricAlgebra.ι R (Option ι → R) (Pi.single j 1)

private noncomputable def coneToProj (σ : (projectiveSpace b hi).cones) :
    affineChart R (projectiveSpace b hi).lattice σ.val ⟶ Proj 𝒜 :=
  projectiveFanChartToProj R b hi
    (exists_le_projectiveSpaceCone_compl b hi σ.property).choose_spec

private theorem faceAffineChartMap_comp_coneToProj {τ σ : (projectiveSpace b hi).cones}
    (h : τ ≤ σ) :
    faceAffineChartMap R (projectiveSpace b hi).lattice
        ((projectiveSpace b hi).isFaceOf_of_le σ.property τ.property h) ≫ coneToProj R b hi σ =
      coneToProj R b hi τ :=
  (faceAffineChartMap_comp_projectiveFanChartToProj R
    ((projectiveSpace b hi).isFaceOf_of_le σ.property τ.property h)
    (exists_le_projectiveSpaceCone_compl b hi σ.property).choose_spec).trans
    (projectiveFanChartToProj_eq R _ _)

/-- The toric scheme of the fan of projective space maps to the projective
spectrum by the homogeneous coordinates on its affine charts. -/
noncomputable def finiteFanSchemeToProjectiveSpace :
    (projectiveSpace b hi).finiteFanScheme R ⟶ Proj 𝒜 :=
  (projectiveSpace b hi).finiteFanSchemeDesc R (coneToProj R b hi)
    (faceAffineChartMap_comp_coneToProj R b hi)

variable {b hi}

/-- On the chart of a cone contained in the maximal cone omitting `k`, the morphism to `Proj` is
given by the homogeneous coordinates normalized by `X_k = 1`. -/
@[reassoc]
theorem affineChartι_comp_finiteFanSchemeToProjectiveSpace (σ : (projectiveSpace b hi).cones)
    {k : Option ι} (hσ : σ.val ≤ projectiveSpaceCone b i {k}ᶜ) :
    (projectiveSpace b hi).affineChartι R σ ≫ finiteFanSchemeToProjectiveSpace R b hi =
      projectiveFanChartToProj R b hi hσ := by
  unfold finiteFanSchemeToProjectiveSpace
  exact ((projectiveSpace b hi).affineChartι_finiteFanSchemeDesc R (coneToProj R b hi)
    (faceAffineChartMap_comp_coneToProj R b hi) σ).trans
    (projectiveFanChartToProj_eq R (b := b) (hi := hi)
      (exists_le_projectiveSpaceCone_compl b hi σ.property).choose_spec hσ)

/-- The morphism from the toric scheme of the fan of projective space to `Proj` is a morphism over
`Spec R`. -/
instance isOver_finiteFanSchemeToProjectiveSpace :
    (finiteFanSchemeToProjectiveSpace R b hi).IsOver (Spec (.of R)) where
  comp_over := by
    refine finiteFanScheme_hom_ext R _ fun σ ↦ ?_
    obtain ⟨k, hk⟩ := exists_le_projectiveSpaceCone_compl b hi σ.property
    rw [affineChartι_comp_finiteFanSchemeToProjectiveSpace_assoc R σ hk,
      SymmetricAlgebra.over_eq_projToSpec, projectiveFanChartToProj, Category.assoc,
      SymmetricAlgebra.awayι_projToSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      finiteFanScheme_over R _, affineChartι_finiteFanSchemeToSpec R]
    congr 2
    ext c
    simp [← HomogeneousLocalization.algebraMap_eq]

omit [DecidableEq ι] in
/-- Every point of the toric scheme of the fan of projective space lies in the chart of a maximal
cone. -/
private theorem exists_affineChartι_projectiveSpaceMaximalCone_apply_eq
    (x : (projectiveSpace b hi).finiteFanScheme R) :
    ∃ k y, (projectiveSpace b hi).affineChartι R (projectiveSpaceMaximalCone b hi k) y = x := by
  obtain ⟨σ, y, rfl⟩ := (projectiveSpace b hi).exists_affineChartι_apply_eq R x
  obtain ⟨k, hk⟩ := exists_le_projectiveSpaceCone_compl b hi σ.property
  have hσk := (projectiveSpace b hi).isFaceOf_of_le (projectiveSpaceMaximalCone b hi k).property
      σ.property hk
  exact ⟨k, faceAffineChartMap R _ hσk y, by
    rw [← Scheme.Hom.comp_apply, faceAffineChartMap_comp_affineChartι R]⟩

/-- A point of the chart of the maximal cone omitting `k` that lies over the standard open
`D₊(X_l)` lies in the chart of the maximal cone omitting `l`: it lies in the chart of the
common face, cut out by the ratio `X_l / X_k`. -/
private theorem affineChartι_mem_range_of_mem_basicOpen {k : Option ι}
    (y : affineChart R hi (projectiveSpaceCone b i {k}ᶜ)) {l : Option ι}
    (hy : projectiveFanChartToProj R b hi le_rfl y ∈ Proj.basicOpen 𝒜 (X l)) :
    (projectiveSpace b hi).affineChartι R (projectiveSpaceMaximalCone b hi k) y ∈
      Set.range ((projectiveSpace b hi).affineChartι R (projectiveSpaceMaximalCone b hi l)) := by
  let Φ := projectiveSpace b hi
  let m : dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ) :=
    ⟨projectiveSpaceRatioCharacter b l k,
      projectiveSpaceRatioCharacter_mem_dualSemigroup b hi l k (by simp)⟩
  have hk := (projectiveSpaceMaximalCone b hi k).property
  have hl := (projectiveSpaceMaximalCone b hi l).property
  have hy' : y ∈ Set.range (faceAffineChartMap R hi
      (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.property))) := by
    rw [range_faceAffineChartMap R hi (Φ.isToricCone hk).fg m]
    exact (projectiveFanChartToProj_preimage_basicOpen R k l).le hy
  obtain ⟨z, rfl⟩ := hy'
  have hT := projectiveSpaceCone_inf_ker_ratioCharacter b hi k l
  have hTmem : projectiveSpaceCone b i {k}ᶜ ⊓
      PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)) ∈ Φ.cones := by
    rw [hT]
    exact Φ.inf_mem hk hl
  have hTl := Φ.isFaceOf_of_le hl hTmem (hT ▸ inf_le_right)
  refine ⟨faceAffineChartMap R hi hTl z, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    faceAffineChartMap_comp_affineChartι R (τ := ⟨_, hTmem⟩)
      (σ := projectiveSpaceMaximalCone b hi l),
    faceAffineChartMap_comp_affineChartι R (τ := ⟨_, hTmem⟩)
      (σ := projectiveSpaceMaximalCone b hi k)]

/-- The morphism from the toric scheme of the fan of projective space to `Proj` is injective. -/
private theorem finiteFanSchemeToProjectiveSpace_injective :
    Function.Injective (finiteFanSchemeToProjectiveSpace R b hi) := by
  intro x y hxy
  obtain ⟨k, x, rfl⟩ := exists_affineChartι_projectiveSpaceMaximalCone_apply_eq R x
  obtain ⟨l, y, rfl⟩ := exists_affineChartι_projectiveSpaceMaximalCone_apply_eq R y
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    affineChartι_comp_finiteFanSchemeToProjectiveSpace R _ le_rfl,
    affineChartι_comp_finiteFanSchemeToProjectiveSpace R _ le_rfl] at hxy
  have hx : projectiveFanChartToProj R b hi le_rfl x ∈ Proj.basicOpen 𝒜 (X l) := by
    rw [hxy, ← opensRange_projectiveFanChartToProj R (b := b) (hi := hi) l]
    exact ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := affineChartι_mem_range_of_mem_basicOpen R x hx
  have h := congrArg (finiteFanSchemeToProjectiveSpace R b hi) hz
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    affineChartι_comp_finiteFanSchemeToProjectiveSpace R _ le_rfl,
    affineChartι_comp_finiteFanSchemeToProjectiveSpace R _ le_rfl] at h
  rw [← hz, (projectiveFanChartToProj R b hi
    (le_refl (projectiveSpaceCone b i {l}ᶜ))).isOpenEmbedding.injective (h.trans hxy)]

/-- The morphism from the toric scheme of the fan of projective space to `Proj` is surjective: the
standard opens `D₊(X_k)` cover projective space. -/
private theorem finiteFanSchemeToProjectiveSpace_surjective :
    Function.Surjective (finiteFanSchemeToProjectiveSpace R b hi) := by
  intro p
  have hp : p ∈ (⊤ : (Proj 𝒜).Opens) := trivial
  rw [← SymmetricAlgebra.iSup_basicOpen_ι_eq_top R (Option ι → R) (fun j ↦ Pi.single j 1)
    (by rw [← funext (Pi.basisFun_apply R (Option ι)), (Pi.basisFun R (Option ι)).span_eq])] at hp
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  rw [← opensRange_projectiveFanChartToProj R (b := b) (hi := hi) k] at hk
  obtain ⟨y, rfl⟩ := hk
  exact ⟨(projectiveSpace b hi).affineChartι R (projectiveSpaceMaximalCone b hi k) y, by
    rw [← Scheme.Hom.comp_apply, affineChartι_comp_finiteFanSchemeToProjectiveSpace R _ le_rfl]⟩

/-- The morphism from the toric scheme of the fan of projective space to `Proj` is an open
immersion: it is injective, and an open immersion on the chart of every maximal cone. -/
instance isOpenImmersion_finiteFanSchemeToProjectiveSpace :
    IsOpenImmersion (finiteFanSchemeToProjectiveSpace R b hi) :=
  .of_forall_source_exists _ (finiteFanSchemeToProjectiveSpace_injective R) fun x ↦ by
    obtain ⟨k, y, rfl⟩ := exists_affineChartι_projectiveSpaceMaximalCone_apply_eq R x
    refine ⟨_, (projectiveSpace b hi).affineChartι R (projectiveSpaceMaximalCone b hi k),
      inferInstance, ⟨y, rfl⟩, ?_⟩
    rw [affineChartι_comp_finiteFanSchemeToProjectiveSpace R _ le_rfl]
    infer_instance

/-- **The toric scheme of the fan of projective space is projective space** `Proj R[X_j]`. -/
instance isIso_finiteFanSchemeToProjectiveSpace : IsIso (finiteFanSchemeToProjectiveSpace R b hi) :=
  (isIso_iff_isOpenImmersion_and_surjective _).2
    ⟨inferInstance, ⟨finiteFanSchemeToProjectiveSpace_surjective R⟩⟩

end Fan

end TauCeti.Toric

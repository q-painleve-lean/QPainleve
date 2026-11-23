/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import QPainleve.Algebra.MonoidAlgebra.BinomialTwist
public import QPainleve.Geometry.Toric.Fan.Mutation.Basic
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Basic

/-!
# Toric mutation away from the pivot fiber

In a cone on the nonnegative side of the pivot character the regular denominator
is the binomial itself. On the other side, the denominator is divided by the pivot
monomial and the exponents are pulled back by the lattice transvection. These are
the affine chart formulas for the elementary transformation in Gross, Hacking and
Keel, [*Birational geometry of cluster algebras*][GHK], §3.1 and the proof of Theorem 5.6.

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open AddMonoidAlgebra Multiplicative

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

variable (Φ : Fan i) (b : Module.Basis (Fin 2) ℤ N) {v : N}
  (hv : v ≠ 0) (hpos : PointedCone.hull ℝ {i v} ∈ Φ.cones)
  (hneg : PointedCone.hull ℝ {i (-v)} ∈ Φ.cones)

local notation "m" => (LinearMap.toAddMonoidHom (Module.Basis.detDualEquiv b v))
local notation "τ(" σ ")" => (Subtype.val (mutationFanConeEquiv Φ b hv hpos hneg σ))

/-- The pivot character, signed so that it can be regular on the specified half-plane.
The negative side uses the inverse of the pivot character. -/
def mutationChartCharacter (side : Bool) : N →+ ℤ :=
  if side then -m else m

/-- The nonnegative half-plane uses the pivot character itself. -/
@[simp]
theorem mutationChartCharacter_false :
    mutationChartCharacter b (v := v) false = m := (rfl)

/-- The nonpositive half-plane uses the inverse pivot character. -/
@[simp]
theorem mutationChartCharacter_true :
    mutationChartCharacter b (v := v) true = -m := (rfl)

/-- The signed pivot character vanishes exactly when the pivot is zero. -/
@[simp]
theorem mutationChartCharacter_eq_zero_iff (side : Bool) :
    mutationChartCharacter b (v := v) side = 0 ↔ v = 0 := by
  have hm : m = 0 ↔ v = 0 := by
    constructor
    · intro h
      apply b.detDualEquiv.injective
      rw [map_zero]
      exact LinearMap.toAddMonoidHom_injective h
    · rintro rfl
      rw [map_zero]
      rfl
  cases side <;> simp [hm]

private theorem mutationChartCharacter_at_pivot (side : Bool) :
    mutationChartCharacter b (v := v) side v = 0 := by
  cases side <;> simp only [mutationChartCharacter_false, mutationChartCharacter_true,
    AddMonoidHom.neg_apply, LinearMap.toAddMonoidHom_coe, Module.Basis.detDualEquiv_self, neg_zero]

/-- A cone on either side of the pivot line admits a regular signed pivot character. -/
theorem exists_mutationChartCharacter_mem_dualSemigroup (σ : Φ.cones)
    (h : (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0) :
    ∃ side : Bool, mutationChartCharacter b (v := v) side ∈ dualSemigroup Φ.lattice σ.val := by
  rcases h with h | h
  · exact ⟨false, (mem_dualSemigroup Φ.lattice _).mpr fun _ hx ↦ h _ hx⟩
  · refine ⟨true, (mem_dualSemigroup Φ.lattice _).mpr ?_⟩
    intro x hx
    simpa only [mutationChartCharacter, ite_true, map_neg, LinearMap.neg_apply, neg_nonneg]
      using h x hx

private def chartLinearEquiv (side : Bool) : V ≃ₗ[ℝ] V :=
  if side then LinearEquiv.transvection (f := -(Φ.lattice.realCharacter m))
    (v := i v) (by simp only [LinearMap.neg_apply, IsIntegralLattice.realCharacter_apply,
      LinearMap.toAddMonoidHom_coe, Module.Basis.detDualEquiv_self, Int.cast_zero, neg_zero])
  else LinearEquiv.refl ℝ V

private def chartLatticeEquiv (side : Bool) : N ≃+ N :=
  if side then
    (LinearEquiv.transvection (f := -(b.detDualEquiv v : Module.Dual ℤ N)) (v := v)
      (by simp only [LinearMap.neg_apply, Module.Basis.detDualEquiv_self, neg_zero])).toAddEquiv
  else AddEquiv.refl N

private theorem chartLatticeEquiv_apply (side : Bool) (x : N) :
    chartLatticeEquiv b (v := v) side x = if side then x - m x • v else x := by
  cases side <;> simp [chartLatticeEquiv, LinearMap.transvection.apply, sub_eq_add_neg]

private theorem chartLinearEquiv_lattice (side : Bool) (x : N) :
    chartLinearEquiv Φ b (v := v) side (i x) = i (chartLatticeEquiv b (v := v) side x) := by
  cases side <;> simp [chartLinearEquiv, chartLatticeEquiv_apply,
    LinearMap.transvection.apply, Int.cast_smul_eq_zsmul, sub_eq_add_neg]

variable (σ : Φ.cones) (side : Bool)
  (hs : mutationChartCharacter b (v := v) side ∈ dualSemigroup Φ.lattice σ.val)

include hs in
private theorem chartLinearEquiv_eqOn :
    Set.EqOn (chartLinearEquiv Φ b (v := v) side) (Φ.lattice.mutationRayEquiv b v)
      (σ.val : Set V) := by
  have h := (mem_dualSemigroup Φ.lattice _).mp hs
  intro x hx
  cases side
  · simpa [chartLinearEquiv] using
      (Φ.lattice.mutationRayEquiv_apply_of_nonneg b v (h hx)).symm
  · have hn : Φ.lattice.realCharacter m x ≤ 0 := by
      simpa [mutationChartCharacter] using h hx
    rw [Φ.lattice.mutationRayEquiv_apply_of_nonpos b v hn]
    simp [chartLinearEquiv, LinearMap.transvection.apply]

include hs in
private theorem chartLinearEquiv_map :
    σ.val.map (chartLinearEquiv Φ b (v := v) side).toLinearMap = τ(σ) := by
  apply SetLike.coe_injective
  rw [PointedCone.coe_map, coe_mutationFanConeEquiv]
  exact (chartLinearEquiv_eqOn Φ b σ side hs).image_eq

/-- The map on exponents of the affine charts is the identity on the nonnegative side
and precomposition with the lattice transvection on the negative side. -/
def mutationChartExponentEquiv :
    dualSemigroup Φ.lattice τ(σ) ≃+ dualSemigroup Φ.lattice σ.val :=
  dualSemigroupEquiv Φ.lattice Φ.lattice (chartLatticeEquiv b side) (chartLinearEquiv Φ b side)
    (chartLinearEquiv_lattice Φ b side) (chartLinearEquiv_map Φ b hv hpos hneg σ side hs)

/-- The formula for a pulled-back chart exponent evaluated on a lattice vector. -/
theorem mutationChartExponentEquiv_apply (a : dualSemigroup Φ.lattice τ(σ)) (x : N) :
    (Φ.mutationChartExponentEquiv b hv hpos hneg σ side hs a : N →+ ℤ) x =
      if side then a.val x - a.val v * m x else a.val x := by
  rw [mutationChartExponentEquiv, dualSemigroupEquiv_apply, chartLatticeEquiv_apply]
  cases side <;> simp [mul_comm]

include hs in
/-- The same signed pivot character is regular on the corresponding mutated cone. -/
theorem mutationChartCharacter_mem_dualSemigroup_target :
    mutationChartCharacter b (v := v) side ∈ dualSemigroup Φ.lattice τ(σ) := by
  rw [mem_dualSemigroup]
  intro x hx
  rw [← SetLike.mem_coe, coe_mutationFanConeEquiv] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [← chartLinearEquiv_eqOn Φ b σ side hs hy]
  have h := (mem_dualSemigroup Φ.lattice _).mp hs hy
  have hzero : Φ.lattice.realCharacter (mutationChartCharacter b (v := v) side) (i v) = 0 := by
    simp [IsIntegralLattice.realCharacter_apply, mutationChartCharacter_at_pivot]
  cases side
  · simpa [chartLinearEquiv] using h
  · simpa only [chartLinearEquiv, ite_true, LinearEquiv.transvection.apply,
      map_add, map_smul, hzero, smul_zero, add_zero] using h

private theorem mutationChartExponentEquiv_pivot :
    Φ.mutationChartExponentEquiv b hv hpos hneg σ side hs
        ⟨_, Φ.mutationChartCharacter_mem_dualSemigroup_target b hv hpos hneg σ side hs⟩ =
      ⟨mutationChartCharacter b (v := v) side, hs⟩ := by
  apply Subtype.ext
  ext x
  rw [mutationChartExponentEquiv_apply]
  split_ifs <;> simp only [mutationChartCharacter_at_pivot, zero_mul, sub_zero]

variable (c : ℂ)

local notation "R(" κ ")" => AddMonoidAlgebra ℂ (dualSemigroup (lattice Φ) κ)
local notation "constant" => (cond side c 1)
local notation "coefficient" => (cond side 1 c)
local notation "q" => (Subtype.mk (mutationChartCharacter b (v := v) side) hs :
  dualSemigroup (lattice Φ) (Subtype.val σ))
local notation "q'" => (Subtype.mk (mutationChartCharacter b (v := v) side)
  (mutationChartCharacter_mem_dualSemigroup_target Φ b hv hpos hneg σ side hs) :
  dualSemigroup (lattice Φ) τ(σ))

/-- The regular binomial on the side of a cone is either one plus the pivot monomial
times the center, or the center plus the inverse pivot monomial. -/
abbrev mutationChartBinomial {κ : PointedCone ℝ V} (a : dualSemigroup Φ.lattice κ) : R(κ) :=
  single 0 constant + single a coefficient

/-- The two terms of the regular binomial on the chosen half-plane. -/
theorem mutationChartBinomial_eq {κ : PointedCone ℝ V} (a : dualSemigroup Φ.lattice κ) :
    mutationChartBinomial Φ side c a = algebraMap ℂ (R(κ)) constant + single a coefficient :=
  (rfl)

local notation "L" => Localization.Away (mutationChartBinomial Φ side c q)
local notation "L'" => Localization.Away (mutationChartBinomial Φ side c q')

private def chartMonomialAlgEquiv : R(τ(σ)) ≃ₐ[ℂ] R(σ.val) :=
  AddMonoidAlgebra.domCongr ℂ ℂ (Φ.mutationChartExponentEquiv b hv hpos hneg σ side hs)

private theorem chartMonomialAlgEquiv_binomial :
    chartMonomialAlgEquiv Φ b hv hpos hneg σ side hs (mutationChartBinomial Φ side c q') =
      mutationChartBinomial Φ side c q := by
  simp only [chartMonomialAlgEquiv, mutationChartBinomial_eq, map_add, AlgEquiv.commutes,
    domCongr_single, mutationChartExponentEquiv_pivot]

private def chartMonomialLocalizationEquiv : L' ≃ₐ[ℂ] L :=
  IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers (mutationChartBinomial Φ side c q'))
    (T := Submonoid.powers (mutationChartBinomial Φ side c q)) L' L
    (chartMonomialAlgEquiv Φ b hv hpos hneg σ side hs)
    (by rw [Submonoid.map_powers, chartMonomialAlgEquiv_binomial])

private def chartDegree : dualSemigroup Φ.lattice σ.val →+ ℤ :=
  -(AddMonoidHom.eval v).comp (dualSemigroup Φ.lattice σ.val).subtype

private theorem chartDegree_apply (a : dualSemigroup Φ.lattice σ.val) :
    chartDegree Φ (v := v) σ a = -a.val v := (rfl)

private theorem chartDegree_pivot : chartDegree Φ (v := v) σ q = 0 := by
  simp [chartDegree, mutationChartCharacter_at_pivot]

/-- The pullback by toric mutation is an algebra isomorphism between the localizations at
the regular pivot binomial on corresponding affine charts. -/
def mutationChartAlgEquiv : L' ≃ₐ[ℂ] L :=
  (chartMonomialLocalizationEquiv Φ b hv hpos hneg σ side hs c).trans
    (binomialTwist constant coefficient q (chartDegree Φ σ) (chartDegree_pivot Φ b σ side hs))

/-- The pullback multiplies the transported monomial by the regular binomial to the
power given by the negative of the original exponent's value at the pivot. -/
@[simp]
theorem mutationChartAlgEquiv_single (a : dualSemigroup Φ.lattice τ(σ)) (r : ℂ) :
    Φ.mutationChartAlgEquiv b hv hpos hneg σ side hs c (algebraMap _ L' (single a r)) =
      algebraMap _ L (single (Φ.mutationChartExponentEquiv b hv hpos hneg σ side hs a) r) *
        ↑(awayBinomialUnit constant coefficient q ^ (-a.val v)) := by
  have hdeg : chartDegree Φ (v := v) σ (Φ.mutationChartExponentEquiv b hv hpos hneg σ side hs a) =
      -a.val v := by
    rw [chartDegree_apply, mutationChartExponentEquiv_apply]
    cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, LinearMap.toAddMonoidHom_coe,
      Module.Basis.detDualEquiv_self, mul_zero, sub_zero]
  simp only [mutationChartAlgEquiv, AlgEquiv.trans_apply, chartMonomialLocalizationEquiv,
    IsLocalization.algEquivOfAlgEquiv_eq, chartMonomialAlgEquiv, domCongr_single,
    binomialTwist_single, hdeg]

/-- The mutation isomorphism of the indicated affine opens in additive semigroup
coordinates, with source the original cone and target the mutated cone. -/
def mutationChartIso :
    Scheme.Opens.toScheme (X := Spec (.of (R(σ.val))))
      (PrimeSpectrum.basicOpen (mutationChartBinomial Φ side c q)) ≅
    Scheme.Opens.toScheme (X := Spec (.of (R(τ(σ)))))
      (PrimeSpectrum.basicOpen (mutationChartBinomial Φ side c q')) :=
  basicOpenIsoSpecAway (R := .of (R(σ.val))) _ ≪≫
    Scheme.Spec.mapIso
      (Φ.mutationChartAlgEquiv b hv hpos hneg σ side hs c).toRingEquiv.toCommRingCatIso.op ≪≫
    (basicOpenIsoSpecAway (R := .of (R(τ(σ)))) _).symm

/-- The mutation isomorphism of the affine opens commutes with their complex structure
morphisms. -/
theorem mutationChartIso_hom_comp_toBase :
    (Φ.mutationChartIso b hv hpos hneg σ side hs c).hom ≫
      Scheme.Opens.ι (X := Spec (.of (R(τ(σ)))))
        (PrimeSpectrum.basicOpen (mutationChartBinomial Φ side c q')) ≫
      Spec.algebraMap ℂ (R(τ(σ))) =
    Scheme.Opens.ι (X := Spec (.of (R(σ.val))))
        (PrimeSpectrum.basicOpen (mutationChartBinomial Φ side c q)) ≫
      Spec.algebraMap ℂ (R(σ.val)) := by
  let f := Φ.mutationChartAlgEquiv b hv hpos hneg σ side hs c
  let e := basicOpenIsoSpecAway (R := .of (R(σ.val))) (mutationChartBinomial Φ side c q)
  let e' := basicOpenIsoSpecAway (R := .of (R(τ(σ)))) (mutationChartBinomial Φ side c q')
  have h' := basicOpenIsoSpecAway_hom_SpecMap (R := .of (R(τ(σ))))
    (mutationChartBinomial Φ side c q')
  have h := basicOpenIsoSpecAway_hom_SpecMap (R := .of (R(σ.val)))
    (mutationChartBinomial Φ side c q)
  -- Express the two open immersions as the corresponding localization morphisms.
  change (e.hom ≫ Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom) ≫ e'.inv) ≫ _ = _
  rw [← h', ← h]
  simp only [e', Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  simp only [Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  rw [← IsScalarTower.algebraMap_eq ℂ (R(τ(σ))) L',
    ← IsScalarTower.algebraMap_eq ℂ (R(σ.val)) L]
  apply CommRingCat.hom_ext
  exact f.toAlgHom.comp_algebraMap

section Torus

local notation "G" => AddMonoidAlgebra ℂ (N →+ ℤ)
local notation "P" => (AddMonoidAlgebra.single (0 : N →+ ℤ) (1 : ℂ) +
  AddMonoidAlgebra.single m c)
local notation "T" => Localization.Away P

private def torusChartMonomial : Multiplicative (N →+ ℤ) →* Tˣ :=
  ((algebraMap G T).toMonoidHom.comp (AddMonoidAlgebra.of ℂ _)).toHomUnits

private theorem coe_torusChartMonomial (a : N →+ ℤ) :
    (torusChartMonomial b (v := v) c (ofAdd a) : T) =
      algebraMap G T (single a 1) := by
  simp only [torusChartMonomial, MonoidHom.coe_toHomUnits, MonoidHom.comp_apply, of_apply,
    toAdd_ofAdd]
  rfl

private def chartToTorusOnAlgebra (κ : PointedCone ℝ V) : R(κ) →ₐ[ℂ] T :=
  (Algebra.algHom ℂ G T).comp
    (AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (dualSemigroup Φ.lattice κ).subtype)

private theorem chartToTorusOnAlgebra_single {κ : PointedCone ℝ V}
    (a : dualSemigroup Φ.lattice κ) (r : ℂ) :
    chartToTorusOnAlgebra Φ b (v := v) c κ (single a r) =
      algebraMap G T (single a.val r) := by
  -- Evaluate the domain map on the underlying monoid-algebra single.
  change algebraMap G T (mapDomain (dualSemigroup Φ.lattice κ).subtype (single a r)) = _
  rw [mapDomain_single]
  rfl

private theorem chartToTorusOnAlgebra_binomial {κ : PointedCone ℝ V}
    (p : dualSemigroup Φ.lattice κ)
    (hp : p.val = mutationChartCharacter b (v := v) side) :
    chartToTorusOnAlgebra Φ b (v := v) c κ (mutationChartBinomial Φ side c p) =
      ↑(if side then torusChartMonomial b (v := v) c (ofAdd (-m)) * awayBinomialUnit 1 c m
        else awayBinomialUnit 1 c m : Tˣ) := by
  cases side
  · simp only [mutationChartBinomial, Bool.cond_false, map_add,
      chartToTorusOnAlgebra_single, hp, mutationChartCharacter_false, Bool.false_eq_true,
      ↓reduceIte, coe_awayBinomialUnit, AddSubmonoid.coe_zero]
  · have h : (single (-m) 1 : G) * P = algebraMap ℂ G c + single (-m) 1 := by
      rw [mul_add, AddMonoidAlgebra.single_mul_single]
      simp [add_comm, mul_comm (single (-m) (1 : ℂ))]
    simpa only [mutationChartBinomial_eq, Bool.cond_true, map_add, map_mul, AlgHom.commutes,
      chartToTorusOnAlgebra_single, hp, mutationChartCharacter_true, ite_true, Units.val_mul,
      coe_torusChartMonomial, coe_awayBinomialUnit, IsScalarTower.algebraMap_apply ℂ G T]
      using congrArg (algebraMap G T) h.symm

/-- The coordinate-ring map of the common open torus into a chart of either fan.
The two chart denominators differ on the torus by an invertible character. -/
def mutationChartToTorus {κ : PointedCone ℝ V} (p : dualSemigroup Φ.lattice κ)
    (hp : p.val = mutationChartCharacter b (v := v) side) :
    Localization.Away (mutationChartBinomial Φ side c p) →ₐ[ℂ] T :=
  IsLocalization.Away.liftAlgHom _ (f := chartToTorusOnAlgebra Φ b c κ) (by
    rw [chartToTorusOnAlgebra_binomial Φ b side c p hp]
    exact Units.isUnit _)

/-- On the common torus, a chart monomial becomes the corresponding Laurent monomial. -/
@[simp]
theorem mutationChartToTorus_single {κ : PointedCone ℝ V} (p a : dualSemigroup Φ.lattice κ)
    (hp : p.val = mutationChartCharacter b (v := v) side) (r : ℂ) :
    mutationChartToTorus Φ b side c p hp (algebraMap _ _ (single a r)) =
      algebraMap G T (single a.val r) := by
  rw [mutationChartToTorus, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact chartToTorusOnAlgebra_single Φ b c a r

private theorem mutationChartToTorus_unit {κ : PointedCone ℝ V} (p : dualSemigroup Φ.lattice κ)
    (hp : p.val = mutationChartCharacter b (v := v) side) :
    Units.map (mutationChartToTorus Φ b side c p hp).toMonoidHom
      (awayBinomialUnit constant coefficient p) =
        if side then torusChartMonomial b (v := v) c (ofAdd (-m)) * awayBinomialUnit 1 c m
        else awayBinomialUnit 1 c m := by
  apply Units.ext
  simp only [Units.coe_map, coe_awayBinomialUnit]
  -- This is the localization lift evaluated at its denominator.
  change (mutationChartToTorus Φ b side c p hp)
      (algebraMap _ _ (mutationChartBinomial Φ side c p)) = _
  rw [mutationChartToTorus, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact chartToTorusOnAlgebra_binomial Φ b side c p hp

private theorem mutationChartExponentEquiv_val (a : dualSemigroup Φ.lattice τ(σ)) :
    (Φ.mutationChartExponentEquiv b hv hpos hneg σ side hs a).val =
      if side then a.val - a.val v • m else a.val := by
  ext x
  rw [mutationChartExponentEquiv_apply]
  cases side <;> simp

private theorem torusChartMonomial_mul_neg_zpow (a : N →+ ℤ) (n : ℤ) :
    torusChartMonomial b (v := v) c (ofAdd (a - n • m)) *
      (torusChartMonomial b (v := v) c (ofAdd (-m)) * awayBinomialUnit 1 c m) ^ (-n) =
        torusChartMonomial b (v := v) c (ofAdd a) * awayBinomialUnit 1 c m ^ (-n) := by
  simp only [sub_eq_add_neg, ofAdd_add, map_mul, ofAdd_neg, ofAdd_zsmul, map_inv, map_zpow,
    mul_zpow, inv_zpow, ← zpow_neg, neg_neg]
  let x := torusChartMonomial b (v := v) c (ofAdd m)
  let y := torusChartMonomial b (v := v) c (ofAdd a)
  let u := awayBinomialUnit 1 c m
  -- Group the inverse character factors in the commutative group of units.
  change (y * x ^ (-n)) * (x ^ n * u ^ (-n)) = y * u ^ (-n)
  rw [mul_assoc y, ← mul_assoc (x ^ (-n)), ← zpow_add, neg_add_cancel, zpow_zero, one_mul]

private theorem torusDegree_apply (a : N →+ ℤ) : (-(AddMonoidHom.eval v)) a = -a v := (rfl)

/-- The binomial twist on the common open torus, independent of the fan and the side. -/
def mutationTorusChartAlgEquiv : T ≃ₐ[ℂ] T :=
  binomialTwist 1 c m (-(AddMonoidHom.eval v)) (by
    rw [torusDegree_apply, LinearMap.toAddMonoidHom_coe, Module.Basis.detDualEquiv_self, neg_zero])

/-- On the common open torus, mutation multiplies a character by a power of the pivot
binomial. -/
@[simp]
theorem mutationTorusChartAlgEquiv_single (a : N →+ ℤ) (r : ℂ) :
    mutationTorusChartAlgEquiv b (v := v) c (algebraMap G T (single a r)) =
      algebraMap G T (single a r) * ↑(awayBinomialUnit 1 c m ^ (-a v)) := by
  simp only [mutationTorusChartAlgEquiv, binomialTwist_single, torusDegree_apply]

/-- Both half-plane chart pullbacks restrict to the same binomial twist on the
common open torus. In particular this gives the restriction formula for all chart
monomials with exponent given by the negative value at the pivot. -/
theorem mutationChartToTorus_comp_mutationChartAlgEquiv :
    (mutationChartToTorus Φ b side c q rfl).comp
        (Φ.mutationChartAlgEquiv b hv hpos hneg σ side hs c).toAlgHom =
      (mutationTorusChartAlgEquiv b (v := v) c).toAlgHom.comp
        (mutationChartToTorus Φ b side c q' rfl) := by
  apply Localization.algHom_ext
  apply (AddMonoidAlgebra.lift ℂ T (dualSemigroup Φ.lattice τ(σ))).symm.injective
  apply MonoidHom.ext
  intro a
  -- Extensionality has restricted both maps to the chart's unlocalized algebra.
  change mutationChartToTorus Φ b side c q rfl
      (Φ.mutationChartAlgEquiv b hv hpos hneg σ side hs c (algebraMap _ L' (single a.toAdd 1))) =
    mutationTorusChartAlgEquiv b (v := v) c
      (mutationChartToTorus Φ b side c q' rfl (algebraMap _ L' (single a.toAdd 1)))
  rw [mutationChartAlgEquiv_single, map_mul, mutationChartToTorus_single,
    mutationChartToTorus_single, mutationTorusChartAlgEquiv_single]
  have he := congrArg (fun u : Tˣ ↦ (u : T)) (show
      Units.map (mutationChartToTorus Φ b side c q rfl).toMonoidHom
          (awayBinomialUnit constant coefficient q ^ (-a.toAdd.val v)) =
        (if side then torusChartMonomial b (v := v) c (ofAdd (-m)) * awayBinomialUnit 1 c m
         else awayBinomialUnit 1 c m : Tˣ) ^ (-a.toAdd.val v) by
    rw [map_zpow, mutationChartToTorus_unit])
  have he' : mutationChartToTorus Φ b side c q rfl
      (↑(awayBinomialUnit constant coefficient q ^ (-a.toAdd.val v))) = _ :=
    he
  rw [he', mutationChartExponentEquiv_val, ← coe_torusChartMonomial,
    ← coe_torusChartMonomial]
  cases side
  · rfl
  · exact congrArg (fun u : Tˣ ↦ (u : T)) (torusChartMonomial_mul_neg_zpow b c _ _)

end Torus

end TauCeti.Toric.Fan

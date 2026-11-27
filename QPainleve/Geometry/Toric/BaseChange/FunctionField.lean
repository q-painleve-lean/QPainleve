/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.OrderOfVanishing.Base
public import QPainleve.Geometry.Toric.BaseChange.DenseTorus
public import QPainleve.Geometry.Toric.BaseChange.FiniteType
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
public import TauCeti.AlgebraicGeometry.Scheme.Normal

import QPainleve.AlgebraicGeometry.Scheme.Factorial
import QPainleve.AlgebraicGeometry.Scheme.FunctionField
import QPainleve.Geometry.Toric.BaseChange.Fan.Basic
import QPainleve.Geometry.Toric.RegularChart
import QPainleve.LinearAlgebra.Determinant.Dual
import TauCeti.Algebra.Group.UniqueProds.Submonoid
import TauCeti.Algebra.Group.UniqueProds.TorsionFree
import TauCeti.Algebra.MonoidAlgebra.Units
import TauCeti.Algebra.Module.Torsion.Hom
import TauCeti.AlgebraicGeometry.Scheme.Regular

/-!
# Rational characters of toric schemes over a domain

The dense zero-cone chart identifies the function field of a nonempty toric fan scheme
with that of its torus. Monomials on the torus give rational characters on the fan scheme.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open TauCeti.AlgebraicGeometry (CodimensionOnePoint IsNormalScheme)
open TauCeti.AlgebraicGeometry.Scheme
  (exists_unit_germToFunctionField_eq_of_ord_eq_zero_of_isIntegrallyClosed ord_functionFieldMap)

namespace TauCeti.Toric.Fan

universe u

variable (R : Type u) [CommRing R] [IsDomain R]
  {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i)

/-- All affine charts of a toric scheme over a domain are reduced. -/
instance isReduced_finiteFanScheme : IsReduced (Φ.finiteFanScheme R) := by
  refine @IsReduced.of_openCover _ (Φ.affineChartOpenCover R) ?_
  intro σ
  let cone : Φ.cones := σ
  rw [Φ.affineChartOpenCover_X R cone]
  change IsReduced (Spec (.of (affineChartRing R Φ.lattice cone.val)))
  infer_instance

variable [hΦ : Nonempty Φ.cones]

local notation "botCone" =>
  (Subtype.mk (⊥ : PointedCone ℝ V) (Φ.bot_mem hΦ.some.property) : Φ.cones)
local notation "torusChart" => (Φ.affineChartι R botCone)
local notation "B" => (CommRingCat.of (affineChartRing R Φ.lattice (⊥ : PointedCone ℝ V)))

/-- A nonempty toric scheme over a domain is integral. -/
instance isIntegral_finiteFanScheme : IsIntegral (Φ.finiteFanScheme R) := by
  apply (isIntegral_iff_irreducibleSpace_and_isReduced _).2
  refine ⟨(irreducibleSpace_def _).2 ?_, inferInstance⟩
  let j : Spec B ⟶ Φ.finiteFanScheme R := torusChart
  have hd : DenseRange j := (isDominant_affineChartι_bot R Φ _).denseRange
  have hirr := ((IrreducibleSpace.isIrreducible_univ (Spec B)).image j
    j.continuous.continuousOn).closure
  rwa [Set.image_univ, hd.closure_range] at hirr

/-- A nonempty regular toric scheme over a factorial domain is normal. -/
theorem isNormalScheme_finiteFanScheme [UniqueFactorizationMonoid R] (hreg : Φ.IsRegular) :
    IsNormalScheme (Φ.finiteFanScheme R) := by
  let := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := R) hreg
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

private def zeroChartExponent : (N →+ ℤ) →+ dualSemigroup Φ.lattice (⊥ : PointedCone ℝ V) where
  toFun m := ⟨m, by simp⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A lattice character as a rational function on the toric scheme. -/
def functionFieldCharacter : Multiplicative (N →+ ℤ) →* (Φ.finiteFanScheme R).functionField :=
  let j : Spec B ⟶ Φ.finiteFanScheme R := torusChart
  (CategoryTheory.inv j.functionFieldMap).hom.toMonoidHom.comp <|
    (((Scheme.ΓSpecIso B).inv ≫ (Spec B).germToFunctionField ⊤).hom.toMonoidHom.comp
      (AddMonoidAlgebra.of R _)).comp
        (zeroChartExponent Φ).toMultiplicative

/-- On the torus, the rational character is the monomial of the corresponding exponent. -/
@[simp]
theorem functionFieldMap_affineChartι_bot_character (m : N →+ ℤ)
    (hbot : (⊥ : PointedCone ℝ V) ∈ Φ.cones) :
    letI : Algebra B (Spec B).functionField := instAlgebraCarrierFunctionFieldSpec B
    (Φ.affineChartι R ⟨⊥, hbot⟩).functionFieldMap (Φ.functionFieldCharacter R (ofAdd m)) =
      algebraMap B (Spec B).functionField (AddMonoidAlgebra.single
        ⟨m, by simp⟩ 1) := by
  rw [functionFieldCharacter]
  let f := (Φ.affineChartι R ⟨⊥, hbot⟩).functionFieldMap
  change f (CategoryTheory.inv f (((Scheme.ΓSpecIso B).inv ≫ (Spec B).germToFunctionField ⊤)
    (AddMonoidAlgebra.of R _ (ofAdd (zeroChartExponent Φ m))))) = _
  rw [IsIso.inv_hom_id_apply, AddMonoidAlgebra.of_apply, toAdd_ofAdd]
  rfl

/-- A binomial with constant term one and a nontrivial character is nonzero. -/
theorem one_add_mul_functionFieldCharacter_ne_zero (c : R) {m : N →+ ℤ} (hm : m ≠ 0) :
    1 + algebraMap R (Φ.finiteFanScheme R).functionField c *
      Φ.functionFieldCharacter R (ofAdd m) ≠ 0 := by
  let j : Spec B ⟶ Φ.finiteFanScheme R := torusChart
  let : Algebra B (Spec B).functionField := instAlgebraCarrierFunctionFieldSpec B
  let g := ((Scheme.ΓSpecIso B).inv ≫ (Spec B).germToFunctionField ⊤).hom
  let a : dualSemigroup Φ.lattice (⊥ : PointedCone ℝ V) := ⟨m, by simp⟩
  have ha : a ≠ 0 := fun h ↦ hm (congrArg Subtype.val h)
  have hbase : algebraMap R (Spec B).functionField c = g (algebraMap R B c) := by
    rw [Scheme.Spec.algebraMap_functionField_base]
  have hchar : j.functionFieldMap (Φ.functionFieldCharacter R (ofAdd m)) =
      g (AddMonoidAlgebra.single a 1) :=
    Φ.functionFieldMap_affineChartι_bot_character R m (Subtype.property botCone)
  intro h
  have he := congrArg j.functionFieldMap h
  rw [map_add, map_one, map_mul, j.functionFieldMap_algebraMap R, hchar, hbase,
    map_zero, ← map_mul, ← map_one g, ← map_add, ← map_zero g] at he
  have hg : Function.Injective g :=
    ((Spec B).germToFunctionField_injective ⊤).comp
      (Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv.injective
  have hz := hg he
  have hc := congrArg (fun f : affineChartRing R Φ.lattice ⊥ ↦ f.coeff 0) hz
  change (1 + AddMonoidAlgebra.single 0 c * AddMonoidAlgebra.single a 1).coeff 0 = 0 at hc
  simp [AddMonoidAlgebra.one_def, AddMonoidAlgebra.single_mul_single, ha] at hc

/-- Swapping the basis vectors inverts the determinant character. -/
theorem functionFieldCharacter_detDualEquiv_reindex_swap
    (b : Module.Basis (Fin 2) ℤ N) (v : N) :
    Φ.functionFieldCharacter R
        (ofAdd ((b.reindex (Equiv.swap 0 1)).detDualEquiv v).toAddMonoidHom) =
      (Φ.functionFieldCharacter R (ofAdd (b.detDualEquiv v).toAddMonoidHom))⁻¹ := by
  have h : ((b.reindex (Equiv.swap 0 1)).detDualEquiv v).toAddMonoidHom =
      -(b.detDualEquiv v).toAddMonoidHom := by
    ext x
    simp
  rw [h, ofAdd_neg, map_inv]

/-- A character regular on a cone is represented by its monomial on that cone's chart. -/
theorem functionFieldMap_affineChartι_character (σ : Φ.cones)
    (m : dualSemigroup Φ.lattice σ.val) :
    let A := CommRingCat.of (affineChartRing R Φ.lattice σ.val)
    letI : Algebra A (Spec A).functionField := instAlgebraCarrierFunctionFieldSpec A
    (Φ.affineChartι R σ).functionFieldMap (Φ.functionFieldCharacter R (ofAdd m.val)) =
      algebraMap A (Spec A).functionField (AddMonoidAlgebra.single m 1) := by
  dsimp only
  have hface := (Φ.isToricCone σ.property).salient.bot_isFaceOf
  let a := CommRingCat.ofHom (faceAffineChartRingMap R Φ.lattice hface).toRingHom
  have : IsDominant (Spec.map a) := by
    rw [← faceAffineChartMap_def R Φ.lattice hface]
    exact isDominant_faceAffineChartMap R Φ.lattice hface
  have hcomp : Spec.map a ≫ Φ.affineChartι R σ = torusChart := by
    rw [← faceAffineChartMap_def R Φ.lattice hface]
    exact Φ.faceAffineChartMap_comp_affineChartι R (τ := botCone) (σ := σ) hface
  apply (Spec.map a).functionFieldMap.hom.injective
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.functionFieldMap_comp,
    Scheme.Hom.functionFieldMap_congr hcomp, functionFieldMap_affineChartι_bot_character,
    Scheme.Hom.functionFieldMap_SpecMap_algebraMap]
  congr 1
  rw [show a (AddMonoidAlgebra.single m 1) =
    AddMonoidAlgebra.single (AddSubmonoid.inclusion (dualSemigroup_anti Φ.lattice hface.le) m) 1
    from faceAffineChartRingMap_single R Φ.lattice hface m 1]
  exact congrArg (fun z ↦ AddMonoidAlgebra.single z (1 : R)) (Subtype.ext rfl)

/-- An algebra homomorphism out of the toric function field is determined by its values
on the lattice characters. -/
theorem functionFieldCharacter_algHom_ext {K : Type*} [Semiring K] [Algebra R K]
    {f g : (Φ.finiteFanScheme R).functionField →ₐ[R] K}
    (h : ∀ m, f (Φ.functionFieldCharacter R m) = g (Φ.functionFieldCharacter R m)) :
    f = g := by
  let j : Spec B ⟶ Φ.finiteFanScheme R := torusChart
  let e := AlgEquiv.ofBijective (j.functionFieldAlgHom R) (by
    have he : ⇑(j.functionFieldAlgHom R) =
        ⇑(asIso j.functionFieldMap).commRingCatIsoToRingEquiv := by
      funext x
      rw [Scheme.Hom.functionFieldAlgHom_apply]
      rfl
    rw [he]
    exact (asIso j.functionFieldMap).commRingCatIsoToRingEquiv.bijective)
  let : Algebra B (Spec B).functionField := instAlgebraCarrierFunctionFieldSpec B
  have hgerm (r : B) : algebraMap B (Spec B).functionField r =
      ((Scheme.ΓSpecIso B).inv ≫ (Spec B).germToFunctionField ⊤) r := by
    rw [Scheme.ΓSpecIso_inv]
    rfl
  let : IsScalarTower R B (Spec B).functionField := IsScalarTower.of_algebraMap_eq fun c ↦ by
    rw [hgerm, Scheme.Spec.algebraMap_functionField_base]
  let f' := f.comp e.symm.toAlgHom
  let g' := g.comp e.symm.toAlgHom
  have he : f' = g' := by
    let a := Algebra.algHom R B (Spec B).functionField
    have : IsFractionRing B (Spec B).functionField := functionField_isFractionRing_of_affine B
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (nonZeroDivisors B)
    suffices hcomp : f'.comp a = g'.comp a from congrArg AlgHom.toRingHom hcomp
    apply AddMonoidAlgebra.algHom_ext
    · intro m
      have hm : e.symm (algebraMap B (Spec B).functionField (AddMonoidAlgebra.single m 1)) =
          Φ.functionFieldCharacter R (ofAdd m.val) := by
        apply e.injective
        rw [AlgEquiv.apply_symm_apply]
        simpa only [e, AlgEquiv.ofBijective_apply, Scheme.Hom.functionFieldAlgHom_apply, j] using
          (Φ.functionFieldMap_affineChartι_bot_character R m.val (Subtype.property botCone)).symm
      exact (congrArg f hm).trans ((h _).trans (congrArg g hm).symm)
    · exact Subsingleton.elim _ _
  apply AlgHom.ext
  intro x
  simpa only [f', g', AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using
    congrArg (fun a : (Spec B).functionField →ₐ[R] K ↦ a (e x)) he

section Orders

variable [IsNoetherianRing R]

local notation "𝒳" => (Φ.finiteFanScheme R)
local notation "T" => (Spec B)
local notation "j" => torusChart

local instance : IsLocallyNoetherian T :=
  isLocallyNoetherian_of_isOpenImmersion j

/-- A lattice character has order zero at every codimension-one point of the zero-cone chart. -/
theorem ord_functionFieldCharacter_eq_zero_of_mem_range_zeroChart
    (m : N →+ ℤ) {x : CodimensionOnePoint 𝒳} (hx : x.val ∈ Set.range j) :
    (𝒳).ord (Φ.functionFieldCharacter R (ofAdd m)) x.val = 0 := by
  obtain ⟨y, rfl⟩ := (CodimensionOnePoint.mem_range_mapOfIsOpenImmersion j).2 hx
  rw [CodimensionOnePoint.coe_mapOfIsOpenImmersion,
    ← ord_functionFieldMap j, Φ.functionFieldMap_affineChartι_bot_character R]
  let e : dualSemigroup Φ.lattice (⊥ : PointedCone ℝ V) := ⟨m, by simp⟩
  have hm := isUnit_single_bot (R := R) Φ.lattice e
  have hmono :
      @algebraMap B (T).functionField _ _ (instAlgebraCarrierFunctionFieldSpec B)
          (AddMonoidAlgebra.single e (1 : R)) =
        ((Scheme.ΓSpecIso B).inv ≫ (T).germToFunctionField ⊤)
          (AddMonoidAlgebra.single e (1 : R)) := by
    rw [Scheme.ΓSpecIso_inv]
    rfl
  rw [hmono]
  exact (T).ord_of_isUnit (hm.map (Scheme.ΓSpecIso B).inv.hom) trivial

variable [UniqueFactorizationMonoid R]

/-- A nonzero rational function with no zero or pole on the torus is a character
times a unit of the coefficient ring. The base ring is a Noetherian factorial domain. -/
theorem exists_eq_unit_mul_functionFieldCharacter (f : (𝒳).functionFieldˣ)
    (hf : ∀ y : CodimensionOnePoint T,
      (T).ord ((j).functionFieldMap (f : (𝒳).functionField)) y.val = 0) :
    ∃ (c : Rˣ) (m : N →+ ℤ),
      (f : (𝒳).functionField) = algebraMap R (𝒳).functionField (c : R) *
        Φ.functionFieldCharacter R (ofAdd m) := by
  let hreg := isRegularCone_bot Φ.lattice
  have : UniqueFactorizationMonoid B := hreg.uniqueFactorizationMonoid_affineChartRing R Φ.lattice
  obtain ⟨u, hu⟩ := exists_unit_germToFunctionField_eq_of_ord_eq_zero_of_isIntegrallyClosed
    (X := T) (U := ⊤) (f := Units.map (j).functionFieldMap.hom.toMonoidHom f)
    (fun y _ ↦ by
      let p : PrimeSpectrum B := y
      have : UniqueFactorizationMonoid ((T).presheaf.stalk y) :=
        uniqueFactorizationMonoid_stalk_Spec B p
      infer_instance)
    (fun y _ ↦ hf y)
  let τ := Scheme.ΓSpecIso B
  let uB := Units.map τ.hom.hom.toMonoidHom u
  let c := (AddMonoidAlgebra.unitsEquiv uB).1
  let a : dualSemigroup Φ.lattice (⊥ : PointedCone ℝ V) :=
    (AddMonoidAlgebra.unitsEquiv uB).2.toAdd
  let m := (a : N →+ ℤ)
  refine ⟨c, m, (j).functionFieldMap.hom.injective ?_⟩
  have hs : (uB : B) = algebraMap R B (c : R) * AddMonoidAlgebra.single a 1 := by
    change (uB : B) = AddMonoidAlgebra.single 0 (c : R) * AddMonoidAlgebra.single a 1
    rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
    exact AddMonoidAlgebra.val_eq_single_unitsEquiv uB
  have hunit : τ.inv (uB : B) = (u : Γ(T, ⊤)) := by
    simpa only [uB, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      CommRingCat.comp_apply, CommRingCat.id_apply] using
      ConcreteCategory.congr_hom τ.hom_inv_id (u : Γ(T, ⊤))
  rw [map_mul, (j).functionFieldMap_algebraMap R, Φ.functionFieldMap_affineChartι_bot_character R,
    Scheme.Spec.algebraMap_functionField_base]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass] at hu
  rw [← hu, ← hunit]
  change (τ.inv ≫ (T).germToFunctionField ⊤) (uB : B) =
    (τ.inv ≫ (T).germToFunctionField ⊤) (algebraMap R B (c : R)) * _
  rw [hs, map_mul]
  rfl

end Orders

end TauCeti.Toric.Fan

namespace TauCeti.Toric.FanHom

universe u

variable (R : Type u) [CommRing R] [IsDomain R]
  {N N' : Type u} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  [Nonempty Φ.cones] [Nonempty Ψ.cones]

/-- A dominant toric morphism pulls back rational characters by its lattice map. -/
@[simp]
theorem functionFieldMap_finiteFanSchemeHom_character (f : FanHom Φ Ψ)
    [IsDominant (f.finiteFanSchemeHom R)] (m : N' →+ ℤ) :
    (f.finiteFanSchemeHom R).functionFieldMap (Ψ.functionFieldCharacter R (ofAdd m)) =
      Φ.functionFieldCharacter R (ofAdd (m.comp f.latticeMap)) := by
  let hσ := Φ.bot_mem (inferInstance : Nonempty Φ.cones).some.property
  let hτ := Ψ.bot_mem (inferInstance : Nonempty Ψ.cones).some.property
  let σ : Φ.cones := ⟨⊥, hσ⟩
  let τ : Ψ.cones := ⟨⊥, hτ⟩
  let hmaps : Set.MapsTo f.realMap (σ.val : Set V) (τ.val : Set V') := by
    simp [σ, τ, Set.MapsTo]
  let d := dualSemigroupMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice hmaps
  let a := CommRingCat.ofHom (AddMonoidAlgebra.mapDomainAlgHom R R d).toRingHom
  have hcomp : Φ.affineChartι R σ ≫ f.finiteFanSchemeHom R =
      Spec.map a ≫ Ψ.affineChartι R τ := by
    rw [f.affineChartι_comp_finiteFanSchemeHom R σ τ hmaps, affineChartMap_def]
  have : IsDominant (Spec.map a) := by
    have : IsDominant (Spec.map a ≫ Ψ.affineChartι R τ) := hcomp ▸ inferInstanceAs
      (IsDominant (Φ.affineChartι R σ ≫ f.finiteFanSchemeHom R))
    exact IsDominant.of_comp_of_isOpenImmersion (Spec.map a) (Ψ.affineChartι R τ)
  apply (Φ.affineChartι R σ).functionFieldMap.hom.injective
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.functionFieldMap_comp,
    Scheme.Hom.functionFieldMap_congr hcomp, Scheme.Hom.functionFieldMap_comp,
    CommRingCat.comp_apply, Ψ.functionFieldMap_affineChartι_bot_character R m hτ,
    Φ.functionFieldMap_affineChartι_bot_character R (m.comp f.latticeMap) hσ,
    Scheme.Hom.functionFieldMap_SpecMap_algebraMap]
  congr 1
  simp only [a, CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
  exact congrArg (fun t ↦ AddMonoidAlgebra.single t (1 : R))
    (Subtype.ext (coe_dualSemigroupMap Φ.lattice Ψ.lattice _ _ _ hmaps _))

end TauCeti.Toric.FanHom

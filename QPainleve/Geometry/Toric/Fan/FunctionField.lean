/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OrderOfVanishing.Basic
public import QPainleve.AlgebraicGeometry.OrderOfVanishing.Base
public import QPainleve.Geometry.Toric.Fan.Chart
public import QPainleve.Geometry.Toric.Fan.DenseTorus
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
public import TauCeti.Geometry.Toric.Algebraic.Fan.Normal
public import TauCeti.Geometry.Toric.Algebraic.Fan.Over

import QPainleve.AlgebraicGeometry.Scheme.FunctionField
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Equiv
import TauCeti.Algebra.MonoidAlgebra.Units
import TauCeti.AlgebraicGeometry.Scheme.Regular
import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Finiteness

/-!
# Rational characters of a toric fan

A nonempty toric fan realizes an integral scheme, and the inclusion of its dense torus
identifies the two function fields. Each lattice character gives a rational function on the
fan scheme whose representatives on the affine cone charts are the corresponding monomials
whenever the character is nonnegative on the cone. Characters have order zero at the
codimension-one points of the dense torus, and a nonzero rational function with this property
is a scalar times a character.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open TauCeti.AlgebraicGeometry (CodimensionOnePoint)
open TauCeti.AlgebraicGeometry.Scheme
  (exists_unit_germToFunctionField_eq_of_ord_eq_zero_of_isIntegrallyClosed ord_functionFieldMap)

namespace TauCeti.Toric

section

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- Affine toric charts of toric cones have Noetherian coordinate rings. -/
theorem IsToricCone.isNoetherianRing_affineCoordinateRing (hσ : IsToricCone i σ)
    (hi : IsIntegralLattice i) :
    IsNoetherianRing (affineCoordinateRing hi σ) := by
  have : Monoid.FG (Multiplicative (dualSemigroup hi σ)) :=
    Monoid.fg_iff_add_fg.mpr (hσ.fg_dualSemigroup hi)
  exact Algebra.FiniteType.isNoetherianRing ℂ _

namespace Fan

variable (Φ : Fan i)

/-- A nonempty toric fan has integral algebraic realization. -/
instance isIntegral_algebraicRealization [Nonempty Φ.cones] :
    IsIntegral Φ.algebraicRealization := by
  apply (isIntegral_iff_irreducibleSpace_and_isReduced _).2
  refine ⟨(irreducibleSpace_def _).2 ?_, inferInstance⟩
  let j := Φ.denseTorusι inferInstance
  have hd : DenseRange j := (isDominant_denseTorusι Φ inferInstance).denseRange
  have hirr := ((IrreducibleSpace.isIrreducible_univ Φ.denseTorus).image j
    j.continuous.continuousOn).closure
  rwa [Set.image_univ, hd.closure_range] at hirr

/-- A toric fan has locally Noetherian algebraic realization. -/
instance isLocallyNoetherian_algebraicRealization : IsLocallyNoetherian Φ.algebraicRealization :=
  (isLocallyNoetherian_iff_openCover Φ.affineToricOpenCover).2 fun σ ↦ by
    let cone : Φ.cones := σ
    have := (Φ.isToricCone cone.property).isNoetherianRing_affineCoordinateRing Φ.lattice
    exact isLocallyNoetherian_Spec.2 this

/-- The algebraic realization of a finite toric fan is Noetherian. -/
instance isNoetherian_algebraicRealization : IsNoetherian Φ.algebraicRealization := by
  let : Finite Φ.affineToricOpenCover.I₀ := inferInstanceAs (Finite Φ.cones)
  let : ∀ σ, CompactSpace (Φ.affineToricOpenCover.X σ) := fun σ ↦ by
    rw [Φ.affineToricOpenCover_X σ]
    infer_instance
  exact { toIsLocallyNoetherian := inferInstance
          toCompactSpace := Φ.affineToricOpenCover.compactSpace }

variable [Nonempty Φ.cones]

/-- A lattice character, viewed as a rational function on the toric scheme via the dense torus. -/
def character : Multiplicative (N →+ ℤ) →* Φ.algebraicRealization.functionField :=
  (inv ((Φ.denseTorusι inferInstance).functionFieldMap)).hom.toMonoidHom.comp
    (((Iso.inv (Scheme.ΓSpecIso (.of (affineCoordinateRing Φ.lattice ⊥))) ≫
      Φ.denseTorus.germToFunctionField ⊤).hom.toMonoidHom.comp (MonoidAlgebra.of ℂ _)).comp
        (denseTorusDualEquiv Φ.lattice).symm.toMultiplicative.toMonoidHom)

/-- Pulling a rational character back to the dense torus gives the corresponding monomial. -/
@[simp]
theorem functionFieldMap_character (m : Multiplicative (N →+ ℤ)) :
    (Φ.denseTorusι inferInstance).functionFieldMap (Φ.character m) =
      (Iso.inv (Scheme.ΓSpecIso (.of (affineCoordinateRing Φ.lattice ⊥))) ≫
        Φ.denseTorus.germToFunctionField ⊤)
        (MonoidAlgebra.of ℂ _ (ofAdd ((denseTorusDualEquiv Φ.lattice).symm m.toAdd))) := by
  rw [character]
  exact IsIso.inv_hom_id_apply ((Φ.denseTorusι inferInstance).functionFieldMap) _

/-- A regular character on a cone chart is represented there by its coordinate-ring
monomial. -/
theorem functionFieldMap_affineToricChartι_character (σ : Φ.cones)
    (m : dualSemigroup Φ.lattice σ.val) :
    (Φ.affineToricChartι σ).functionFieldMap (Φ.character (ofAdd (m : N →+ ℤ))) =
      ((Scheme.ΓSpecIso (.of (affineCoordinateRing Φ.lattice σ.val))).inv ≫
        (Φ.affineToricChart σ).germToFunctionField ⊤) (MonoidAlgebra.of ℂ _ (ofAdd m)) := by
  let h := (Φ.isToricCone σ.property).salient.bot_isFaceOf
  let f := faceAffineToricSchemeMap Φ.lattice h
  have := isDominant_faceAffineToricSchemeMap Φ.lattice h
  apply f.functionFieldMap.hom.injective
  have hcomp : f ≫ Φ.affineToricChartι σ = Φ.denseTorusι inferInstance :=
    (Φ.denseTorusι_face σ).symm
  have hpull :
      (Φ.affineToricChartι σ).functionFieldMap ≫ f.functionFieldMap =
        (Φ.denseTorusι inferInstance).functionFieldMap := by
    rw [← Scheme.Hom.functionFieldMap_comp]
    apply (Scheme.Hom.eq_functionFieldMap_iff (Φ.denseTorusι inferInstance) _).2
    rw [Scheme.Hom.SpecMap_functionFieldMap_fromSpecStalk, hcomp]
  rw [← ConcreteCategory.comp_apply, hpull, functionFieldMap_character]
  let g := CommRingCat.ofHom (faceAffineCoordinateRingMap Φ.lattice h).toRingHom
  have hg : f = Spec.map g := faceAffineToricSchemeMap_def Φ.lattice h
  have hsections :
      (Φ.affineToricChart σ).germToFunctionField ⊤ ≫ f.functionFieldMap =
        f.appTop ≫ Φ.denseTorus.germToFunctionField ⊤ :=
    f.germToFunctionField_functionFieldMap ⊤
  have htop :
      (Scheme.ΓSpecIso (.of (affineCoordinateRing Φ.lattice σ.val))).inv ≫ f.appTop =
        g ≫ (Scheme.ΓSpecIso (.of (affineCoordinateRing Φ.lattice ⊥))).inv := by
    rw [hg, ← Scheme.ΓSpecIso_inv_naturality]
  rw [← ConcreteCategory.comp_apply, Category.assoc, hsections, ← Category.assoc, htop,
    Category.assoc, ConcreteCategory.comp_apply]
  simp only [ConcreteCategory.comp_apply, toAdd_ofAdd]
  have hm : g (MonoidAlgebra.of ℂ _ (ofAdd m)) =
      MonoidAlgebra.of ℂ _ (ofAdd ((denseTorusDualEquiv Φ.lattice).symm (m : N →+ ℤ))) := by
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.of_apply, denseTorusDualEquiv_symm_apply]
    exact faceAffineCoordinateRingMap_single Φ.lattice h m 1
  rw [hm]

/-- In the additive cone chart, a regular character is the corresponding monomial
in the additive semigroup algebra. -/
theorem functionFieldMap_additiveAffineToricChartι_character (σ : Φ.cones)
    (a : dualSemigroup Φ.lattice σ.val) :
    let R := CommRingCat.of (AddMonoidAlgebra ℂ (dualSemigroup Φ.lattice σ.val))
    letI : Algebra R (Spec R).functionField := instAlgebraCarrierFunctionFieldSpec R
    (Φ.additiveAffineToricChartι σ).functionFieldMap (Φ.character (ofAdd a.val)) =
      algebraMap R (Spec R).functionField (AddMonoidAlgebra.single a 1) := by
  dsimp only
  let R := affineCoordinateRing Φ.lattice σ.val
  let e := (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ
    (dualSemigroup Φ.lattice σ.val)).symm
  let f := e.toRingEquiv.toCommRingCatIso.hom
  have hf : Φ.additiveAffineToricChartι σ = Spec.map f ≫ Φ.affineToricChartι σ :=
    Φ.additiveAffineToricChartι_def σ
  have hc := Scheme.Hom.functionFieldMap_congr hf
  rw [hc, Scheme.Hom.functionFieldMap_comp, CommRingCat.comp_apply,
    functionFieldMap_affineToricChartι_character]
  let : Algebra R (Spec (.of R)).functionField := instAlgebraCarrierFunctionFieldSpec (.of R)
  have hbase (r : R) :
      ((Scheme.ΓSpecIso (.of R)).inv ≫ (Φ.affineToricChart σ).germToFunctionField ⊤) r =
        algebraMap R (Spec (.of R)).functionField r := by
    rw [Scheme.ΓSpecIso_inv]
    rfl
  rw [hbase]
  refine (Scheme.Hom.functionFieldMap_SpecMap_algebraMap f _).trans ?_
  have hmono : f (MonoidAlgebra.of ℂ _ (ofAdd a)) = AddMonoidAlgebra.single a 1 := by
    rw [MonoidAlgebra.of_apply]
    exact AddMonoidAlgebra.toMultiplicativeAlgEquiv_symm_single (R := ℂ) (ofAdd a) 1
  rw [hmono]

local notation "𝒳" => Φ.algebraicRealization
local notation "𝕋" => Φ.denseTorus
local notation "R" => affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V)

local instance : IsLocallyNoetherian 𝕋 :=
  isLocallyNoetherian_of_isOpenImmersion (Φ.denseTorusι inferInstance)

/-- A rational character has order zero at each codimension-one point of the dense torus. -/
theorem ord_character_eq_zero_of_mem_range_denseTorusι (m : N →+ ℤ)
    {x : CodimensionOnePoint 𝒳} (hx : x.val ∈ Set.range (Φ.denseTorusι inferInstance)) :
    (𝒳).ord (Φ.character (ofAdd m)) x.val = 0 := by
  let j := Φ.denseTorusι inferInstance
  obtain ⟨y, rfl⟩ := (CodimensionOnePoint.mem_range_mapOfIsOpenImmersion j).2 hx
  rw [CodimensionOnePoint.coe_mapOfIsOpenImmersion,
    ← ord_functionFieldMap j, functionFieldMap_character,
    CommRingCat.comp_apply]
  have hm : IsUnit (MonoidAlgebra.of ℂ _ (ofAdd ((denseTorusDualEquiv Φ.lattice).symm m))) := by
    have hu := ((Group.isUnit (ofAdd m)).map (MonoidAlgebra.of ℂ _)).map
      (denseTorusCoordinateRingEquiv Φ.lattice).symm.toRingHom
    simpa [MonoidAlgebra.of_apply] using hu
  exact (𝕋).ord_of_isUnit (hm.map (Scheme.ΓSpecIso (.of R)).inv.hom) trivial

end Fan

end

namespace Fan

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) [Nonempty Φ.cones]

local notation "𝒳" => Φ.algebraicRealization
local notation "𝕋" => Φ.denseTorus
local notation "R" => affineCoordinateRing Φ.lattice (⊥ : PointedCone ℝ V)

local instance : IsLocallyNoetherian 𝕋 :=
  isLocallyNoetherian_of_isOpenImmersion (Φ.denseTorusι inferInstance)

/-- The fan's complex structure morphism restricts to the structure morphism of its dense torus. -/
theorem denseTorusι_comp_structureMap :
    Φ.denseTorusι inferInstance ≫ Φ.algebraicRealizationStructureMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ R)) := by
  have hbot := Φ.bot_mem (Classical.choice (inferInstance : Nonempty Φ.cones)).property
  rw [Φ.denseTorusι_eq_affineToricChartι _ hbot,
    Φ.affineToricChartι_comp_algebraicRealizationStructureMap]

/-- The dense torus inclusion is a morphism over the complex base. -/
instance isOver_denseTorusι : (Φ.denseTorusι inferInstance).IsOver (Spec (.of ℂ)) :=
  ⟨Φ.denseTorusι_comp_structureMap⟩

/-- Maps from the function field of a toric fan over the base are determined by their
values on rational characters. -/
theorem functionFieldAlgHom_ext {K : Type*} [Semiring K] [Algebra ℂ K]
    {f g : (𝒳).functionField →ₐ[ℂ] K}
    (h : ∀ m, f (Φ.character m) = g (Φ.character m)) : f = g := by
  let j := Φ.denseTorusι inferInstance
  let e := AlgEquiv.ofBijective (j.functionFieldAlgHom ℂ) (by
    have he : ⇑(j.functionFieldAlgHom ℂ) =
        ⇑(asIso j.functionFieldMap).commRingCatIsoToRingEquiv := by
      funext x
      rw [Scheme.Hom.functionFieldAlgHom_apply]
      rfl
    rw [he]
    exact (asIso j.functionFieldMap).commRingCatIsoToRingEquiv.bijective)
  let : Algebra R (𝕋).functionField := instAlgebraCarrierFunctionFieldSpec (.of R)
  have hgerm (r : R) : algebraMap R (𝕋).functionField r =
      ((Scheme.ΓSpecIso (.of R)).inv ≫ (𝕋).germToFunctionField ⊤) r := by
    rw [Scheme.ΓSpecIso_inv]
    rfl
  let : IsScalarTower ℂ R (𝕋).functionField := IsScalarTower.of_algebraMap_eq fun c ↦ by
    rw [hgerm, Scheme.Spec.algebraMap_functionField_base]
  let f' := f.comp e.symm.toAlgHom
  let g' := g.comp e.symm.toAlgHom
  have he : f' = g' := by
    let a := Algebra.algHom ℂ R (𝕋).functionField
    have : IsFractionRing R (𝕋).functionField := functionField_isFractionRing_of_affine (.of R)
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    suffices hcomp : f'.comp a = g'.comp a from congrArg AlgHom.toRingHom hcomp
    refine MonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
    intro m
    have hx : e.symm (algebraMap R (𝕋).functionField (MonoidAlgebra.single m 1)) =
        Φ.character (ofAdd (denseTorusDualEquiv Φ.lattice m.toAdd)) := by
      apply e.injective
      rw [AlgEquiv.apply_symm_apply, hgerm]
      simp only [e, AlgEquiv.ofBijective_apply, Scheme.Hom.functionFieldAlgHom_apply, j,
        functionFieldMap_character, toAdd_ofAdd, AddEquiv.symm_apply_apply, ofAdd_toAdd,
        MonoidAlgebra.of_apply]
    exact (congrArg f hx).trans ((h _).trans (congrArg g hx).symm)
  apply AlgHom.ext
  intro x
  simpa only [f', g', AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using
    congrArg (fun a : (𝕋).functionField →ₐ[ℂ] K ↦ a (e x)) he

/-- A nonzero rational function of order zero at each codimension-one point of the dense torus
is a character times a nonzero base scalar. -/
theorem exists_eq_const_mul_character (f : (𝒳).functionFieldˣ)
    (hf : ∀ y : CodimensionOnePoint 𝕋,
      (𝕋).ord ((Φ.denseTorusι inferInstance).functionFieldMap (f : (𝒳).functionField)) y.val = 0) :
    ∃ (c : ℂˣ) (m : N →+ ℤ),
      (f : (𝒳).functionField) =
        algebraMap ℂ (𝒳).functionField (c : ℂ) * Φ.character (ofAdd m) := by
  let j := Φ.denseTorusι inferInstance
  obtain ⟨u, hu⟩ :=
    exists_unit_germToFunctionField_eq_of_ord_eq_zero_of_isIntegrallyClosed
      (X := 𝕋) (U := ⊤) (f := Units.map j.functionFieldMap.hom.toMonoidHom f)
      (fun _ _ ↦ inferInstance) (fun y _ ↦ hf y)
  let τ := Scheme.ΓSpecIso (.of R)
  let uR := Units.map τ.hom.hom.toMonoidHom u
  have : TwoUniqueSums (dualSemigroup Φ.lattice (⊥ : PointedCone ℝ V)) :=
    TwoUniqueSums.of_injective_addHom
      ((AddMonoidHom.coeFn N ℤ).comp (dualSemigroup Φ.lattice ⊥).subtype).toAddHom
      (DFunLike.coe_injective.comp Subtype.val_injective) inferInstance
  let c := (MonoidAlgebra.unitsEquiv uR).1
  let a := ((MonoidAlgebra.unitsEquiv uR).2 : Multiplicative (dualSemigroup Φ.lattice ⊥))
  let m := denseTorusDualEquiv Φ.lattice a.toAdd
  refine ⟨c, m, j.functionFieldMap.hom.injective ?_⟩
  have hs : (uR : R) = algebraMap ℂ R (c : ℂ) * MonoidAlgebra.of ℂ _ a := by
    simpa [c, a, MonoidAlgebra.algebraMap_def, MonoidAlgebra.of_apply,
      MonoidAlgebra.single_mul_single] using MonoidAlgebra.val_eq_single_unitsEquiv uR
  have hunit : τ.inv (uR : R) = (u : Γ(𝕋, ⊤)) := by
    simpa only [uR, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      CommRingCat.comp_apply, CommRingCat.id_apply] using
      ConcreteCategory.congr_hom τ.hom_inv_id (u : Γ(𝕋, ⊤))
  have hmono : ofAdd ((denseTorusDualEquiv Φ.lattice).symm m) = a := by simp [m]
  rw [map_mul, j.functionFieldMap_algebraMap ℂ, functionFieldMap_character,
    toAdd_ofAdd, hmono, Scheme.Spec.algebraMap_functionField_base, CommRingCat.comp_apply]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass] at hu ⊢
  rw [← hu, ← hunit, hs, map_mul, map_mul]
  rfl

end Fan

end TauCeti.Toric

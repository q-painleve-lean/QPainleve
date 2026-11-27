/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.CharacterTorus.Specialization
public import QPainleve.Geometry.Toric.Fan.Evaluation.Contraction

import QPainleve.Algebra.MonoidAlgebra.MonomialEquiv
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.AlgebraicGeometry.RationalMap.PartialIso
import QPainleve.Geometry.Toric.DeterminantCharacters

/-!
# Dense-torus charts for fixed-center X evaluation

In determinant coordinates the dense torus of an ordered blowup presentation
gives a dominant rational chart on the contracted surface. On this chart each
independent X coordinate is the corresponding charge character multiplied by
its center parameter. The formula uses the specified contraction.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry TauCeti.LaurentRing QPainleve.Toric
open QPainleve.CharacterTorus

namespace TauCeti.Toric.Fan

variable (K : Type) [Field K] [PerfectField K]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  (b : Module.Basis (Fin 2) ℤ N) {n : ℕ} (s : Fin n → Φ.Ray)
  (c : Multiplicative (Fin n → ℤ) →* Kˣ)

local notation "L" => LaurentRing K (Fin n)
local notation "R" => affineChartRing K Φ.lattice (⊥ : PointedCone ℝ V)
local notation "T" => Spec (CommRingCat.of R)
local notation "hbot" => Fan.bot_mem Φ (Subtype.property (Nonempty.some ‹Nonempty Φ.cones›))
local notation "d" => Fan.affineChartι K Φ ⟨⊥, hbot⟩
local notation "e" => denseTorusCoordinateRingEquivDet K Φ.lattice b
local notation "reprEquiv" => Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)

omit [PerfectField K] [Nonempty Φ.cones] in
private def scaledCharge : L →ₐ[K] AddMonoidAlgebra K N :=
  let r := (reprEquiv).toAddEquiv
  (AddMonoidAlgebra.mapDomainAlgHom K K (rayChargeMap s).toAddMonoidHom).comp
    (AddMonoidAlgebra.monomialAlgEquiv (c.comp r.toMultiplicative) r).toAlgHom

omit [Nonempty Φ.cones] in
omit [PerfectField K] in
private theorem scaledCharge_X (j : Fin n) :
    scaledCharge K s c (X j) =
      AddMonoidAlgebra.single (s j).primitiveGenerator (c (ofAdd (Pi.single j 1)) : K) := by
  simp [scaledCharge, X_def, Finsupp.linearEquivFunOnFinite_single,
    AddMonoidAlgebra.mapDomainAlgHom, rayChargeMap_single]

omit [PerfectField K] in
private theorem denseTorusChart_comp_xEvaluation :
    (d).toRationalMap.comp (Φ.xEvaluation K b s c) =
      (Spec.map (CommRingCat.ofHom
        ((e).toAlgHom.comp (scaledCharge K s c)).toRingHom)).toRationalMap := by
  let : Algebra R (T).functionField := instAlgebraCarrierFunctionFieldSpec (.of R)
  have hgerm (r : R) : algebraMap R (T).functionField r =
      ((Scheme.ΓSpecIso (.of R)).inv ≫ (T).germToFunctionField ⊤) r := by
    rw [Scheme.ΓSpecIso_inv]
    rfl
  let : IsScalarTower K R (T).functionField := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [hgerm, Scheme.Spec.algebraMap_functionField_base]
  have h : ((d).functionFieldAlgHom K).comp (Φ.xEval K b s c) =
      (Algebra.algHom K R (T).functionField).comp ((e).toAlgHom.comp (scaledCharge K s c)) := by
    apply algHom_ext
    intro j
    simp only [AlgHom.comp_apply, xEval_X, map_mul, AlgHom.commutes,
      Scheme.Hom.functionFieldAlgHom_apply,
      scaledCharge_X, AlgEquiv.toAlgHom_apply, denseTorusCoordinateRingEquivDet_single,
      denseTorusDualEquiv_symm_apply]
    rw [Φ.functionFieldMap_affineChartι_bot_character K _ hbot]
    change algebraMap K (T).functionField _ * algebraMap R (T).functionField _ =
      algebraMap R (T).functionField _
    rw [IsScalarTower.algebraMap_apply K R, ← map_mul]
    apply congrArg (algebraMap R (T).functionField)
    change AddMonoidAlgebra.single 0 _ * AddMonoidAlgebra.single _ 1 =
      AddMonoidAlgebra.single _ _
    rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one, Algebra.algebraMap_self_apply]
  let φ := (e).toAlgHom.comp (scaledCharge K s c)
  let τ : CommRingCat.of R ⟶ (T).functionField :=
    StructureSheaf.toStalk R (genericPoint (Spec (.of R)))
  have hcomp : CommRingCat.ofHom (Φ.xEval K b s c).toRingHom ≫ (d).functionFieldMap =
      CommRingCat.ofHom φ.toRingHom ≫ τ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    calc
      _ = ((d).functionFieldAlgHom K).comp (Φ.xEval K b s c) x := by
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
          AlgHom.comp_apply, Scheme.Hom.functionFieldAlgHom_apply]
        rfl
      _ = _ := (AlgHom.congr_fun h x).trans (by
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
          AlgHom.comp_apply]
        rfl)
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [Scheme.RationalMap.fromFunctionField_comp, Scheme.Hom.functionFieldMap_toRationalMap,
    fromFunctionField_xEvaluation, ← Spec.map_comp, hcomp]
  exact (Spec.map_comp (CommRingCat.ofHom φ.toRingHom) τ).trans (by
      have ha := Spec.fromSpecStalk_eq' (.of R) (genericPoint (Spec (.of R)))
      exact (congrArg (· ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)) ha.symm).trans
        (Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap _ _).symm)

private theorem exists_dominant_chart (hΦ : Φ.IsRegular)
    {Z : Scheme} [IsIntegral Z]
    (p : (internalBlowupTower K b s (fun j ↦ c (ofAdd (Pi.single j 1)))).1 ⟶ Z)
    [IsModification p] :
    letI : Module.Free ℤ N := .of_basis b
    ∃ (j : scheme K N ⤏ Z) (_ : j.IsDominant),
      j.comp (contractedXEvaluation K b s c hΦ p) =
        (Spec.map (CommRingCat.ofHom (scaledCharge K s c).toRingHom)).toRationalMap := by
  let : Module.Free ℤ N := .of_basis b
  let Y := (internalBlowupTower K b s (fun j ↦ c (ofAdd (Pi.single j 1)))).1
  let π : Y ⟶ Φ.finiteFanScheme K :=
    (internalBlowupTower K b s (fun j ↦ c (ofAdd (Pi.single j 1)))).2.toTower.toBase
  let : IsIntegral Y := isIntegral_internalBlowupTower K b s _ hΦ
  let : IsModification π := isModification_internalBlowupTower_toBase K b s _ hΦ
  let η := (IsModification.birationalOver π).partialIso.symm
  let ψ := η.toRationalMap
  let : ψ.IsDominant := η.toPartialMap.isDominant_toRationalMap_iff.mpr inferInstance
  have hψ : ψ.comp π.toRationalMap = Scheme.RationalMap.id _ := by
    have hη : ψ.IsOver (𝟙 _) π :=
      ⟨η.toPartialMap, ⟨(IsModification.birationalOver π).partialIso_isOver.symm⟩, rfl⟩
    rw [Scheme.RationalMap.comp_toRationalMap, Scheme.RationalMap.isOver_iff.mp hη]
  let α : scheme K N ≅ T := Scheme.Spec.mapIso (e).symm.toRingEquiv.toCommRingCatIso.op
  let a := α.hom.toRationalMap
  let j := a.comp ((d).toRationalMap.comp (ψ.comp p.toRationalMap))
  refine ⟨j, inferInstance, ?_⟩
  have hcontract : p.toRationalMap.comp (contractedXEvaluation K b s c hΦ p) =
      π.toRationalMap.comp (Φ.xEvaluation K b s c) :=
    comp_contractedXEvaluation K b s c hΦ p
  simp only [j, Scheme.RationalMap.comp_assoc, hcontract]
  rw [← Scheme.RationalMap.comp_assoc ψ π.toRationalMap]
  simp only [hψ, Scheme.RationalMap.id_comp, denseTorusChart_comp_xEvaluation]
  rw [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom]
  congr 1
  have hα : α.hom = Spec.map (CommRingCat.ofHom (e).symm.toRingHom) := rfl
  rw [hα, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  simp

omit [Nonempty Φ.cones] in
omit [PerfectField K] in
private theorem spec_scaledCharge :
    let v := (rayChargeMap s).toAddMonoidHom.comp (reprEquiv).toAddEquiv.toAddMonoidHom
    let a := c.comp (reprEquiv).toAddEquiv.toMultiplicative
    Spec.map (CommRingCat.ofHom (scaledCharge K s c).toRingHom) =
      affineCenterSlice a ≫ affineEvaluation K v := by
  dsimp only
  apply Spec.preimage_injective
  rw [Spec.preimage_map, Spec.preimage_comp]
  apply CommRingCat.hom_ext
  apply RingHom.toAddMonoidHom_injective
  apply AddMonoidAlgebra.addMonoidHom_ext
  intro a r
  let v := (rayChargeMap s).toAddMonoidHom.comp (reprEquiv).toAddEquiv.toAddMonoidHom
  let χ := c.comp (reprEquiv).toAddEquiv.toMultiplicative.toMonoidHom
  -- The additive-hom extensionality lemma presents monomials in the Finsupp model.
  change scaledCharge K s c (AddMonoidAlgebra.single a r) =
    (Spec.preimage (affineCenterSlice χ)).hom
      ((Spec.preimage (affineEvaluation K v)).hom (AddMonoidAlgebra.single a r))
  rw [preimage_affineEvaluation_single, preimage_affineCenterSlice_single]
  simp [scaledCharge, v, χ, AddMonoidAlgebra.mapDomainAlgHom]

/-- The fixed-center evaluation on a contracted toric presentation is the restriction of the
joint center and charge evaluation to that center, viewed along a dominant rational chart.
The charge map uses the finite-coordinate identification on the independent X exponents. -/
theorem exists_dominant_chart_comp_contractedXEvaluation (hΦ : Φ.IsRegular)
    {Z : Scheme} [IsIntegral Z]
    (p : (internalBlowupTower K b s (fun j ↦ c (ofAdd (Pi.single j 1)))).1 ⟶ Z)
    [IsModification p] :
    letI : Module.Free ℤ N := .of_basis b
    let v := (rayChargeMap s).toAddMonoidHom.comp (reprEquiv).toAddEquiv.toAddMonoidHom
    let a := c.comp (reprEquiv).toAddEquiv.toMultiplicative
    ∃ (j : scheme K N ⤏ Z) (_ : j.IsDominant),
      j.comp (contractedXEvaluation K b s c hΦ p) =
        (affineCenterSlice a ≫ affineEvaluation K v).toRationalMap := by
  simpa only [spec_scaledCharge] using exists_dominant_chart K b s c hΦ p

end TauCeti.Toric.Fan

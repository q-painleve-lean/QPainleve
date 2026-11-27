/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus
public import QPainleve.Geometry.Toric.Fan.Evaluation
public import QPainleve.Geometry.Toric.Fan.InternalBlowup
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.AlgebraicGeometry.RationalMap.Modification

/-!
# Fixed-center X evaluation on contracted toric models

The rational X evaluation descends along a modification of an ordered toric blowup
model. Its compatibility with a change of presentation can be checked after passing
to a common dominant model.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry TauCeti.LaurentRing

namespace TauCeti.Toric.Fan

variable (K : Type) [Field K] [PerfectField K] {N : Type} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  {n : ℕ} (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "S" => Spec (CommRingCat.of K)
local notation "L" => LaurentRing K (Fin n)
local notation "F" => (Φ.finiteFanScheme K)
local notation "center" a:arg => (fun j ↦ a (ofAdd (Pi.single j 1)))
local notation "Y" a:arg => (Sigma.fst (internalBlowupTower K b s (center a)))
local notation "π" a:arg => toBase (WithBoundary.toTower
  (Sigma.snd (internalBlowupTower K b s (center a))))

variable {X : Scheme} [IsIntegral X]

/-- Evaluation at the specified centers on a contraction of an ordered toric blowup
model. Its pullback to the model evaluates each Laurent coordinate as its scaled charge
character. -/
def contractedXEvaluation (c : Multiplicative (Fin n → ℤ) →* Kˣ) (hΦ : Φ.IsRegular)
    (p : Y c ⟶ X) [IsModification p] : X ⤏ Spec (.of L) := by
  have := isIntegral_internalBlowupTower K b s (center c) hΦ
  have := isModification_internalBlowupTower_toBase K b s (center c) hΦ
  exact (p.existsUnique_rationalMap_comp_eq_of_isModification
    ((π c).toRationalMap.comp (Φ.xEvaluation K b s c))).exists.choose

variable (c : Multiplicative (Fin n → ℤ) →* Kˣ) (hΦ : Φ.IsRegular)
  (p : (internalBlowupTower K b s (fun j : Fin n ↦ c (ofAdd (Pi.single j 1)))).1 ⟶ X)
  [IsModification p]

/-- Pullback to the ordered blowup model recovers the original fixed-center evaluation. -/
theorem comp_contractedXEvaluation :
    letI := isIntegral_internalBlowupTower K b s (center c) hΦ
    letI := isModification_internalBlowupTower_toBase K b s (center c) hΦ
    p.toRationalMap.comp (contractedXEvaluation K b s c hΦ p) =
      (π c).toRationalMap.comp (Φ.xEvaluation K b s c) := by
  have := isIntegral_internalBlowupTower K b s (center c) hΦ
  have := isModification_internalBlowupTower_toBase K b s (center c) hΦ
  exact (p.existsUnique_rationalMap_comp_eq_of_isModification
    ((π c).toRationalMap.comp (Φ.xEvaluation K b s c))).exists.choose_spec

/-- The descended evaluation is over the coefficient field when the two projections
from the ordered model give the same structure morphism. -/
theorem contractedXEvaluation_isOver (f : X ⟶ S)
    (hf : p ≫ f = π c ≫ Φ.finiteFanSchemeToSpec K) :
    (contractedXEvaluation K b s c hΦ p).IsOver f (Spec.algebraMap K L) := by
  have := isIntegral_internalBlowupTower K b s (center c) hΦ
  have := isModification_internalBlowupTower_toBase K b s (center c) hΦ
  have hbase := Scheme.RationalMap.isOver_iff.mp
    (inferInstance : (Φ.xEvaluation K b s c).IsOver
      (F ↘ S) (Spec.algebraMap K L))
  apply Scheme.RationalMap.isOver_iff.mpr
  apply Scheme.RationalMap.comp_left_injective p.toRationalMap
  simpa only [Scheme.RationalMap.comp_compHom, comp_contractedXEvaluation,
    Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom,
    finiteFanScheme_over K, hf] using
    congrArg ((π c).toRationalMap.comp ·) hbase

/-- At the generic point the contracted evaluation is the scaled Laurent evaluation
transported through the function field isomorphism of the contraction. -/
@[simp]
theorem fromFunctionField_contractedXEvaluation :
    letI := isIntegral_internalBlowupTower K b s (center c) hΦ
    letI := isModification_internalBlowupTower_toBase K b s (center c) hΦ
    letI := p.isIso_functionFieldMap_of_isModification
    (contractedXEvaluation K b s c hΦ p).fromFunctionField =
      Spec.map ((CommRingCat.ofHom (Φ.xEval K b s c).toRingHom) ≫
        (π c).functionFieldMap ≫ inv p.functionFieldMap) := by
  have := isIntegral_internalBlowupTower K b s (center c) hΦ
  have := isModification_internalBlowupTower_toBase K b s (center c) hΦ
  have := p.isIso_functionFieldMap_of_isModification
  have h := congrArg Scheme.RationalMap.fromFunctionField
    (comp_contractedXEvaluation K b s c hΦ p)
  simp only [Scheme.RationalMap.fromFunctionField_comp,
    Scheme.Hom.functionFieldMap_toRationalMap, fromFunctionField_xEvaluation] at h
  rw [Spec.map_comp, Spec.map_comp, Category.assoc, ← h, ← Category.assoc, ← Spec.map_comp,
    IsIso.hom_inv_id, Spec.map_id, Category.id_comp]

variable {N' : Type} {V' : Type*} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
  {i' : N' →+ V'} {Ψ : Fan i'} [Nonempty Ψ.cones] {m : ℕ}
  (b' : Module.Basis (Fin 2) ℤ N') (t : Fin m → Ψ.Ray)
  (d' : Multiplicative (Fin m → ℤ) →* Kˣ) (hΨ : Ψ.IsRegular)
  {Z W : Scheme} [IsIntegral Z] [IsIntegral W]
  (q' : (internalBlowupTower K b' t (center d')).1 ⟶ Z) [IsModification q']

local notation "π'" => toBase (WithBoundary.toTower
  (Sigma.snd (internalBlowupTower K b' t (center d'))))

open Scheme.RationalMap in
/-- A compatibility of toric evaluations on a common dominant model gives the same
compatibility on the contracted pairs. The maps to the Laurent spectra may have nondense image. -/
theorem comp_contractedXEvaluation_of_common_model
    (u : W ⟶ Y c) (v : W ⟶ (internalBlowupTower K b' t (center d')).1)
    [IsDominant u] [IsDominant v] (f : X ⟶ Z)
    (hf : (u ≫ p) ≫ f = v ≫ q') (r : Spec (.of L) ⟶ Spec (.of (LaurentRing K (Fin m))))
    (h :
      letI := isModification_internalBlowupTower_toBase K b s (center c) hΦ
      letI := isModification_internalBlowupTower_toBase K b' t (center d') hΨ
      (v ≫ π').toRationalMap.comp (Ψ.xEvaluation K b' t d') =
        ((u ≫ π c).toRationalMap.comp (Φ.xEvaluation K b s c)).compHom r) :
    letI : IsDominant f := IsDominant.of_comp (u ≫ p) f (H := hf.symm ▸ inferInstance)
    f.toRationalMap.comp (contractedXEvaluation K b' t d' hΨ q') =
      (contractedXEvaluation K b s c hΦ p).compHom r := by
  have : IsDominant f := IsDominant.of_comp (u ≫ p) f (H := hf.symm ▸ inferInstance)
  have := isIntegral_internalBlowupTower K b s (center c) hΦ
  have := isIntegral_internalBlowupTower K b' t (center d') hΨ
  have := isModification_internalBlowupTower_toBase K b s (center c) hΦ
  have := isModification_internalBlowupTower_toBase K b' t (center d') hΨ
  apply comp_left_injective (u ≫ p).toRationalMap
  dsimp only
  calc
    _ = (v ≫ q').toRationalMap.comp (contractedXEvaluation K b' t d' hΨ q') := by
      simp only [← comp_assoc, comp_toRationalMap, Scheme.Hom.toRationalMap_compHom, hf]
    _ = (v ≫ π').toRationalMap.comp (Ψ.xEvaluation K b' t d') := by
      simp only [← Scheme.Hom.toRationalMap_compHom, ← comp_toRationalMap,
        comp_assoc, comp_contractedXEvaluation]
    _ = _ := by
      rw [h, comp_compHom]
      simp only [← Scheme.Hom.toRationalMap_compHom, ← comp_toRationalMap,
        comp_assoc, comp_contractedXEvaluation]

end TauCeti.Toric.Fan

namespace TauCeti.Toric.FanEquiv

variable (K : Type) [Field K] [PerfectField K]
  {N N' : Type} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  [Nonempty Φ.cones] [Nonempty Ψ.cones] {n : ℕ}

open Fan Scheme.RationalMap

local notation "centers(" c ")" => (fun j : Fin n ↦ c (ofAdd (Pi.single j 1)))

/-- Transporting an ordered model along a determinant-preserving fan equivalence and
reindexing its centers changes the evaluation on the same contraction by the corresponding
renaming of the X coordinates. The permutation sends new labels to old labels. -/
theorem contractedXEvaluation_eq_of_reindex_transport (e : FanEquiv Φ Ψ)
    (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (ρ : Fin n → Φ.Ray) (c d : Multiplicative (Fin n → ℤ) →* Kˣ) (σ : Equiv.Perm (Fin n))
    (hc : centers(c) ∘ σ = centers(d))
    (hdet : ∀ x y, b'.detDualEquiv (e.latticeEquiv x) (e.latticeEquiv y) = b.detDualEquiv x y)
    {X : Scheme} [IsIntegral X] (p : (internalBlowupTower K b ρ centers(c)).1 ⟶ X)
    [IsModification p] :
    let τ := e.rayEquiv ∘ ρ ∘ σ
    ∀ (g : (internalBlowupTower K b ρ centers(c)).1 ≅ (internalBlowupTower K b' τ centers(d)).1),
      g.hom ≫ (internalBlowupTower K b' τ centers(d)).2.toTower.toBase =
          (internalBlowupTower K b ρ centers(c)).2.toTower.toBase ≫
            e.toFanHom.finiteFanSchemeHom K →
      contractedXEvaluation K b ρ c hΦ p =
        (contractedXEvaluation K b' τ d hΨ (g.inv ≫ p)).compHom
          (Spec.map (CommRingCat.ofHom (rename (R := K) σ.symm).toRingHom)) := by
  intro τ g hproj
  let A := internalBlowupTower K b ρ centers(c)
  let B := internalBlowupTower K b' τ centers(d)
  have := isIntegral_internalBlowupTower K b' τ centers(d) hΨ
  have := isModification_internalBlowupTower_toBase K b' τ centers(d) hΨ
  have hprojInv :
      g.inv ≫ A.2.toTower.toBase = B.2.toTower.toBase ≫ e.symm.toFanHom.finiteFanSchemeHom K := by
    have h := congrArg (fun z ↦ g.inv ≫ z ≫ e.symm.toFanHom.finiteFanSchemeHom K) hproj
    simpa only [Category.assoc, e.finiteFanSchemeHom_comp_symm K,
      Category.comp_id, Iso.inv_hom_id_assoc]
      using h.symm
  have htoric := e.symm.toFanHom.comp_xEvaluation K b' b τ ρ σ.symm d c (fun j ↦ by
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using congrFun hc (σ.symm j))
    (by
      intro j
      ext x
      simp only [τ, Function.comp_apply, Equiv.apply_symm_apply, primitiveGenerator_rayEquiv,
        toFanHom_latticeMap, AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe,
        AddMonoidHom.coe_ofClass, symm_latticeEquiv]
      simpa only [AddEquiv.apply_symm_apply] using (hdet (ρ j).primitiveGenerator
        (e.latticeEquiv.symm x)).symm)
  have hid : (𝟙 X : X ⟶ X).toRationalMap = Scheme.RationalMap.id X :=
    (id_compHom (𝟙 X)).symm.trans (compHom_id _)
  simpa only [hid, Scheme.RationalMap.id_comp] using
    comp_contractedXEvaluation_of_common_model K b' τ d hΨ (g.inv ≫ p) b ρ c hΦ p
      (𝟙 _) g.inv (𝟙 X) (by simp) _ (by
        dsimp only [A, B] at hprojInv
        simp only [Category.id_comp, hprojInv]
        simp only [← Scheme.Hom.toRationalMap_compHom, ← comp_toRationalMap, comp_assoc,
          htoric, comp_compHom])

end TauCeti.Toric.FanEquiv

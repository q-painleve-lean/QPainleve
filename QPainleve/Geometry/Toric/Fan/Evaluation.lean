/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition
public import QPainleve.Geometry.Toric.CharacterTorus.Scheme
public import QPainleve.Geometry.Toric.Fan.Charge
public import QPainleve.Geometry.Toric.BaseChange.Translation
public import QPainleve.Geometry.Toric.Fan.Subdivision.FunctionField
public import QPainleve.LinearAlgebra.Determinant.Dual
public import TauCeti.Algebra.MvPolynomial.Laurent.Basic

import QPainleve.Algebra.MvPolynomial.Laurent.FiniteType
import QPainleve.AlgebraicGeometry.RationalMap.Affine

/-!
# Evaluation of cluster X coordinates on toric presentations

At fixed centers the independent Laurent coordinates evaluate to scaled rational characters.
Toric morphisms pull back these evaluations by precomposition on character exponents.
Subdivisions preserve evaluation, and a lattice frame change with a label permutation
intertwines evaluation with the corresponding relabeling of the independent X torus.
A torus translation preserves evaluation when the center parameters are transformed inversely.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open TauCeti.LaurentRing

namespace TauCeti.Toric.Fan

universe u

variable (R : Type u) [CommRing R] [IsDomain R] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {l : N →+ V} (Φ : Fan l) (b : Module.Basis (Fin 2) ℤ N)
  {ι : Type u} [DecidableEq ι] (s : ι → Φ.Ray)
  (c : Multiplicative (ι → ℤ) →* Rˣ)

local notation "u" j:arg => Ray.primitiveGenerator (Phi := Φ) (s j)
local notation "χ(" x ")" => LinearMap.toAddMonoidHom (b.detDualEquiv x)
local notation "c[" j "]" => c (ofAdd (Pi.single j 1))
local notation "K(" F ")" => Scheme.functionField (Fan.finiteFanScheme R F)

section

variable [Nonempty Φ.cones]

private def xCoordinateUnit (j : ι) : K(Φ)ˣ :=
  Units.map (algebraMap R K(Φ)).toMonoidHom c[j] *
    (Φ.functionFieldCharacter R).toHomUnits (ofAdd χ(u j))

/-- Laurent evaluation at the scaled characters of a fixed-center toric presentation. -/
def xEval : LaurentRing R ι →ₐ[R] K(Φ) :=
  LaurentRing.aeval (xCoordinateUnit R Φ b s c)

/-- Each independent X coordinate evaluates to its center parameter times its charge character. -/
@[simp]
theorem xEval_X (j : ι) :
    Φ.xEval R b s c (X j) =
      algebraMap R K(Φ) (c[j] : R) * Φ.functionFieldCharacter R (ofAdd χ(u j)) := by
  simp [xEval, xCoordinateUnit]

variable {Φ}

local notation "bᵣ" => b.reindex (Equiv.swap 0 1)
local notation "L" => LaurentRing R ι
local notation "invX" => AddMonoidAlgebra.domCongr R R (AddEquiv.neg (ι →₀ ℤ))

/-- Reversing the basis and inverting the center character has the effect of
inverting all independent X coordinates before evaluating. This inversion is the signed
generator of Bershtein, Gavrylenko and Marshakov
([*Cluster integrable systems, q-Painlevé equations and their quantization*, §3.1]
(https://arxiv.org/abs/1711.02063)). -/
theorem xEval_reindex_swap :
    Φ.xEval R bᵣ s c⁻¹ = (Φ.xEval R b s c).comp (invX).toAlgHom := by
  apply LaurentRing.algHom_ext
  intro j
  have hinv :
      Φ.xEval R b s c (↑((unitX j : Lˣ)⁻¹) : L) =
        (Φ.xEval R b s c (X j))⁻¹ := by
    let f : L →* (Φ.finiteFanScheme R).functionField := Φ.xEval R b s c
    simpa only [Units.val_inv_eq_inv_val, Units.coe_map, val_unitX, f,
      AlgHom.coe_toMonoidHom] using (Units.coe_map_inv f (unitX j)).symm
  have hX : (invX) (X j) = (↑((unitX j : Lˣ)⁻¹) : L) := by
    rw [X_def, AddMonoidAlgebra.domCongr_single, AddEquiv.neg_apply, ← Finsupp.single_neg,
      val_inv_unitX]
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hX, hinv, xEval_X, xEval_X]
  have hchar : ((bᵣ).detDualEquiv (u j)).toAddMonoidHom =
      -((b.detDualEquiv (u j)).toAddMonoidHom) := by
    ext x
    simp
  rw [hchar, ofAdd_neg, map_inv]
  simp only [MonoidHom.inv_apply, map_units_inv, mul_inv_rev, mul_comm]

variable (Φ)

variable [Finite ι]

/-- The rational evaluation map to the independent X torus at a fixed center. -/
def xEvaluation : Φ.finiteFanScheme R ⤏ Spec (.of (LaurentRing R ι)) :=
  Scheme.RationalMap.ofAffineAlgHom (Φ.xEval R b s c)

instance : (Φ.xEvaluation R b s c).IsOver
    (Φ.finiteFanScheme R ↘ Spec (.of R)) (Spec.algebraMap R (LaurentRing R ι)) := by
  unfold xEvaluation
  infer_instance

/-- The generic-point map of fixed-center torus evaluation is induced by Laurent evaluation. -/
@[simp]
theorem fromFunctionField_xEvaluation :
    (Φ.xEvaluation R b s c).fromFunctionField =
      Spec.map (CommRingCat.ofHom (Φ.xEval R b s c).toRingHom) := by
  unfold xEvaluation
  exact Scheme.RationalMap.fromFunctionField_ofAffineAlgHom _

variable {Φ}

/-- Fixed-center X evaluation in the reversed toric presentation equals evaluation
in the original presentation followed by regular inversion on the X torus. -/
theorem xEvaluation_reindex_swap :
    Φ.xEvaluation R bᵣ s c⁻¹ =
      (Φ.xEvaluation R b s c).compHom
        (QPainleve.CharacterTorus.map R (AddEquiv.neg (ι →₀ ℤ)).toAddMonoidHom) := by
  have hmap : QPainleve.CharacterTorus.map R (AddEquiv.neg (ι →₀ ℤ)).toAddMonoidHom =
      Spec.map (CommRingCat.ofHom (invX).toAlgHom.toRingHom) := by
    apply Spec.preimage_injective
    apply CommRingCat.hom_ext
    simp only [QPainleve.CharacterTorus.preimage_map, Spec.preimage_map, CommRingCat.hom_ofHom,
      AddMonoidAlgebra.domCongr_toAlgHom, AddEquiv.toAddMonoidHom_eq_coe]
  simp only [hmap, xEvaluation, Scheme.RationalMap.ofAffineAlgHom_compHom, xEval_reindex_swap]

end

end TauCeti.Toric.Fan

namespace TauCeti.Toric

variable (R : Type u) [CommRing R] [IsDomain R] {N N' : Type u} {V V' : Type*}
  [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {l : N →+ V} {l' : N' →+ V'} {Φ : Fan l} {Ψ : Fan l'}
  [Nonempty Φ.cones] [Nonempty Ψ.cones]
  {ι κ : Type u} [DecidableEq ι] [DecidableEq κ]

/-- Pulling fixed-center Laurent evaluation back through a dominant toric morphism
is the same as renaming the independent coordinates when the center weights and
pulled-back determinant characters match on each label. -/
theorem FanHom.functionFieldAlgHom_comp_xEval (f : FanHom Φ Ψ) [IsDominant (f.finiteFanSchemeHom R)]
    (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
    (s : ι → Φ.Ray) (s' : κ → Ψ.Ray) (e : κ → ι)
    (c : Multiplicative (ι → ℤ) →* Rˣ) (c' : Multiplicative (κ → ℤ) →* Rˣ)
    (hc : ∀ j, c' (ofAdd (Pi.single j 1)) = c (ofAdd (Pi.single (e j) 1)))
    (hchar : ∀ j, (b'.detDualEquiv (s' j).primitiveGenerator).toAddMonoidHom.comp f.latticeMap =
      (b.detDualEquiv (s (e j)).primitiveGenerator).toAddMonoidHom) :
    ((f.finiteFanSchemeHom R).functionFieldAlgHom R).comp (Ψ.xEval R b' s' c') =
      (Φ.xEval R b s c).comp (rename e) := by
  apply LaurentRing.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, rename_X, Fan.xEval_X, map_mul, AlgHom.commutes,
    Scheme.Hom.functionFieldAlgHom_apply, f.functionFieldMap_finiteFanSchemeHom_character R,
    hc, hchar]

/-- The fixed-center rational evaluation square for a dominant toric morphism with
matching labeled center weights and characters. -/
theorem FanHom.comp_xEvaluation (f : FanHom Φ Ψ) [IsDominant (f.finiteFanSchemeHom R)]
    [Finite ι] [Finite κ] (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
    (s : ι → Φ.Ray) (s' : κ → Ψ.Ray) (e : κ → ι)
    (c : Multiplicative (ι → ℤ) →* Rˣ) (c' : Multiplicative (κ → ℤ) →* Rˣ)
    (hc : ∀ j, c' (ofAdd (Pi.single j 1)) = c (ofAdd (Pi.single (e j) 1)))
    (hchar : ∀ j, (b'.detDualEquiv (s' j).primitiveGenerator).toAddMonoidHom.comp f.latticeMap =
      (b.detDualEquiv (s (e j)).primitiveGenerator).toAddMonoidHom) :
    (f.finiteFanSchemeHom R).toRationalMap.comp (Ψ.xEvaluation R b' s' c') =
      (Φ.xEvaluation R b s c).compHom
        (Spec.map (CommRingCat.ofHom (rename (R := R) e).toRingHom)) := by
  simp only [Fan.xEvaluation, Scheme.RationalMap.comp_ofAffineAlgHom,
    Scheme.RationalMap.ofAffineAlgHom_compHom,
    f.functionFieldAlgHom_comp_xEval R b b' s s' e c c' hc hchar]

namespace Fan

variable {Ψ : Fan l} [Nonempty Ψ.cones] [Finite ι]

/-- Pulling fixed-center evaluation back through a subdivision is evaluation on the
refined fan at the same centers on the lifted rays. -/
theorem IsSubdivision.comp_xEvaluation (h : Φ.IsSubdivision Ψ)
    (b : Module.Basis (Fin 2) ℤ N) (s : ι → Ψ.Ray) (c : Multiplicative (ι → ℤ) →* Rˣ) :
    (h.toFanHom.finiteFanSchemeHom R).toRationalMap.comp (Ψ.xEvaluation R b s c) =
      Φ.xEvaluation R b (h.liftRay ∘ s) c := by
  have he := h.toFanHom.functionFieldAlgHom_comp_xEval R b b (h.liftRay ∘ s) s id c c
    (fun _ ↦ rfl) (by
    intro j
    simp only [h.toFanHom_latticeMap, AddMonoidHom.comp_id, Function.comp_apply, id_eq,
      h.primitiveGenerator_liftRay])
  simp only [xEvaluation, Scheme.RationalMap.comp_ofAffineAlgHom, he, rename_id, AlgHom.comp_id]

/-- Translating the surface and dividing each center parameter by the value of its
charge character at the translating point preserves fixed-center rational evaluation. -/
theorem torusTranslation_comp_xEvaluation (b : Module.Basis (Fin 2) ℤ N)
    (s : ι → Φ.Ray) (c : Multiplicative (ι → ℤ) →* Rˣ) (t : Multiplicative (N →+ ℤ) →* Rˣ) :
    let charge := ((addMonoidHomLequivInt ℤ).symm.toLinearMap.comp
      (b.detDualEquiv.toLinearMap.comp (rayChargeMap s))).toAddMonoidHom
    (Φ.torusTranslationIso R t).hom.toRationalMap.comp
      (Φ.xEvaluation R b s (c / t.comp charge.toMultiplicative)) = Φ.xEvaluation R b s c := by
  intro charge
  rw [xEvaluation, xEvaluation, Scheme.RationalMap.comp_ofAffineAlgHom]
  congr 1
  apply LaurentRing.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, xEval_X, MonoidHom.div_apply, MonoidHom.comp_apply,
    AddMonoidHom.coe_toMultiplicative, Function.comp_apply, toAdd_ofAdd,
    LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply,
    rayChargeMap_single, LinearEquiv.coe_coe, Scheme.Hom.functionFieldAlgHom_apply,
    addMonoidHomLequivInt_symm_apply, charge]
  rw [map_mul, Scheme.Hom.functionFieldMap_algebraMap R,
    Φ.functionFieldMap_torusTranslationIso_character R t, ← _root_.mul_assoc, ← map_mul,
    ← Units.val_mul, div_mul_cancel]

end Fan

/-- A fan equivalence, with the lattice basis carried along it and the center labels
reindexed, induces the corresponding renaming on the independent X coordinates. -/
theorem FanEquiv.comp_xEvaluation (f : FanEquiv Φ Ψ) [Finite ι] [Finite κ]
    (b : Module.Basis (Fin 2) ℤ N) (s : ι → Φ.Ray) (e : κ ≃ ι)
    (c : Multiplicative (ι → ℤ) →* Rˣ) :
    let relabel := (LinearEquiv.funCongrLeft ℤ ℤ e.symm).toLinearMap.toAddMonoidHom
    let c' := c.comp relabel.toMultiplicative
    (f.toFanHom.finiteFanSchemeHom R).toRationalMap.comp
      (Ψ.xEvaluation R (b.map f.latticeEquiv.toIntLinearEquiv) (f.rayEquiv ∘ s ∘ e) c') =
      (Φ.xEvaluation R b s c).compHom
        (Spec.map (CommRingCat.ofHom (rename (R := R) e).toRingHom)) := by
  intro relabel c'
  apply f.toFanHom.comp_xEvaluation R
  · intro j
    have hsingle : LinearEquiv.funCongrLeft ℤ ℤ e.symm (Pi.single j 1) = Pi.single (e j) 1 := by
      ext i
      simp [LinearEquiv.funCongrLeft_apply, Pi.single_apply, Equiv.symm_apply_eq]
    simp [c', relabel, hsingle]
  · intro j
    ext x
    simp only [Function.comp_apply, primitiveGenerator_rayEquiv, toFanHom_latticeMap,
      AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe, AddMonoidHom.coe_ofClass]
    exact b.detDualEquiv_map f.latticeEquiv.toIntLinearEquiv _ _

end TauCeti.Toric

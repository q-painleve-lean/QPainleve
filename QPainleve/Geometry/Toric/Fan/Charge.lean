/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Basic
public import QPainleve.Geometry.Toric.Fan.Ray

import Mathlib.GroupTheory.IndexNSmul
import Mathlib.LinearAlgebra.StdBasis

/-!
# Toric boundary charges

The charge map of a labeled family of boundary rays assigns the primitive generator of
each ray to the corresponding basis vector.
-/

public noncomputable section

namespace TauCeti.Toric.Fan

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

/-- The charges of a finite family of centers on toric boundary rays. The charge of a
basis vector is the primitive generator of its assigned ray. -/
def rayChargeMap [Finite ι] (s : ι → Φ.Ray) : (ι → ℤ) →ₗ[ℤ] N :=
  Module.piEquiv ι ℤ N fun j ↦ (s j).primitiveGenerator

/-- A standard basis vector maps to the generator of the ray for its label. -/
@[simp]
theorem rayChargeMap_single [Finite ι] [DecidableEq ι] (s : ι → Φ.Ray) (j : ι) :
    rayChargeMap s (Pi.single j 1) = (s j).primitiveGenerator := by
  rw [rayChargeMap, Module.piEquiv, ← Pi.basisFun_apply, Module.Basis.constr_basis]

/-- Lifting the labeled rays through a subdivision leaves their charges unchanged. -/
@[simp]
theorem IsSubdivision.rayChargeMap_liftRay [Finite ι] {Ω : Fan i} (h : Ω.IsSubdivision Φ)
    (s : ι → Φ.Ray) : rayChargeMap (h.liftRay ∘ s) = rayChargeMap s := by
  simp only [rayChargeMap, Function.comp_apply, primitiveGenerator_liftRay]

/-- The charge of each standard basis vector is primitive. -/
theorem rayChargeMap_primitive [Finite ι] [DecidableEq ι] (s : ι → Φ.Ray) (j : ι) :
    IsPrimitive (rayChargeMap s (Pi.single j 1)) := by
  rw [rayChargeMap_single]
  exact (s j).isPrimitiveGenerator.isPrimitive

section Reindex

variable {N' V' ι' : Type*} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
  {i' : N' →+ V'} {Ψ : Fan i'} [Finite ι] [Finite ι']
  {s : ι → Φ.Ray} {t : ι' → Ψ.Ray}

/-- An injective lattice map matching primitive charges induces the contravariant
reindexing of their integer relations along the labeling equivalence. -/
def rayChargeKernelReindex (σ : ι ≃ ι') (e : N →ₗ[ℤ] N') (he : Function.Injective e)
    (h : ∀ j, e (s j).primitiveGenerator = (t (σ j)).primitiveGenerator) :
    (rayChargeMap t).ker ≃ₗ[ℤ] (rayChargeMap s).ker := by
  classical
  let p := LinearEquiv.funCongrLeft ℤ ℤ σ
  refine p.ofSubmodules _ _ ?_
  have hcomp : (rayChargeMap t).comp p.symm.toLinearMap =
      e.comp (rayChargeMap s) := by
    let := Fintype.ofFinite ι
    apply (Pi.basisFun ℤ ι).ext
    intro j
    have hj : p.symm (Pi.single j 1) = Pi.single (σ j) 1 := by
      ext a
      simpa only [p, LinearEquiv.funCongrLeft_symm, LinearEquiv.funCongrLeft_apply,
        LinearMap.funLeft_apply, Function.comp_apply, Equiv.symm_symm] using
        congrFun (Pi.single_comp_equiv σ.symm j (1 : ℤ)) a
    simpa only [Pi.basisFun_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hj,
      rayChargeMap_single] using (h j).symm
  rw [Submodule.map_equiv_eq_comap_symm, ← LinearMap.ker_comp, hcomp,
    LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot_of_injective he)]

/-- The coefficient of a transported relation is the target coefficient at the
corresponding label. -/
@[simp]
theorem rayChargeKernelReindex_apply (σ : ι ≃ ι') (e : N →ₗ[ℤ] N') (he : Function.Injective e)
    (h : ∀ j, e (s j).primitiveGenerator = (t (σ j)).primitiveGenerator)
    (x : (rayChargeMap t).ker) (j : ι) :
    (rayChargeKernelReindex σ e he h x : ι → ℤ) j = (x : ι' → ℤ) (σ j) := by
  rw [rayChargeKernelReindex, LinearEquiv.ofSubmodules_apply]
  exact (rfl)

end Reindex

/-- If the charges span a finite-index sublattice, a lattice equivalence into a
torsion-free group is determined by its values on the labeled ray generators. -/
theorem rayChargeEquiv_ext {N' : Type*} [AddCommGroup N'] [Module.IsTorsionFree ℤ N']
    [Finite ι] (s : ι → Φ.Ray) (hindex : (rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    {E F : N ≃ₗ[ℤ] N'} (h : ∀ j, E (s j).primitiveGenerator = F (s j).primitiveGenerator) :
    E = F := by
  classical
  have hcomp : E.toLinearMap.comp (rayChargeMap s) = F.toLinearMap.comp (rayChargeMap s) := by
    apply (Pi.basisFun ℤ ι).ext
    simpa using h
  ext x
  apply AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hindex
  obtain ⟨a, ha⟩ := (rayChargeMap s).range.toAddSubgroup.nsmul_index_mem x
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, ha, map_nsmul,
    nsmulAddMonoidHom_apply] using LinearMap.congr_fun hcomp a

open QPainleve.Cluster in
/-- Orientation reversal negates the exchange matrix without changing the ray charges. -/
@[simp]
theorem chargeExchangeMatrix_reindex_swap {N V : Type} [AddCommGroup N] [AddCommGroup V]
    [Module ℝ V] {l : N →+ V} {Φ : Fan l} (b : Module.Basis (Fin 2) ℤ N)
    {ι : Type} [DecidableEq ι] (s : ι → Φ.Ray) [Fintype ι] :
    chargeExchangeMatrix (b.reindex (Equiv.swap 0 1)).detDualEquiv.toLinearMap (rayChargeMap s) =
      -chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s) := by
  ext j k
  simp [chargeExchangeMatrix_apply]

end TauCeti.Toric.Fan

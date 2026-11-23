/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

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

/-- The charge of each standard basis vector is primitive. -/
theorem rayChargeMap_primitive [Finite ι] [DecidableEq ι] (s : ι → Φ.Ray) (j : ι) :
    IsPrimitive (rayChargeMap s (Pi.single j 1)) := by
  rw [rayChargeMap_single]
  exact (s j).isPrimitiveGenerator.isPrimitive

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

end TauCeti.Toric.Fan

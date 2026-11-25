/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.DedekindDomain.Basic

import TauCeti.LinearAlgebra.Submodule.Primitive

/-!
# Coordinates on matrix kernels

Over a Dedekind domain, the basis of a matrix kernel admits a matrix of coordinate
readers on the ambient free module. The quotient by the kernel is torsion-free,
so the kernel inclusion splits by `Submodule.exists_isCompl_iff_isTorsionFree_quotient`.
-/

public section

open Module

namespace Matrix

variable {R m n κ : Type*} [CommRing R] [IsDedekindDomain R]
  [Fintype n] [Finite κ] [DecidableEq κ]

/-- The matrix whose columns are a basis of a matrix kernel has a left inverse.
The rows of a left inverse agree on the kernel with the basis coordinate forms. -/
theorem exists_leftInverse_ker_basis (A : Matrix m n R)
    (b : Basis κ R A.mulVecLin.ker) :
    ∃ read : Matrix κ n R, read * Matrix.of (fun i j ↦ (b j : n → R) i) = 1 := by
  let := Fintype.ofFinite κ
  let : DecidableEq n := Classical.decEq n
  let e := A.mulVecLin.quotKerEquivRange
  have hfree : Module.IsTorsionFree R ((n → R) ⧸ A.mulVecLin.ker) :=
    e.injective.moduleIsTorsionFree _ (map_smul e)
  obtain ⟨P, hP⟩ := A.mulVecLin.ker.exists_isCompl_iff_isTorsionFree_quotient.mpr hfree
  let p := A.mulVecLin.ker.projectionOnto P hP
  refine ⟨LinearMap.toMatrix (Pi.basisFun R n) b p, ?_⟩
  have hcolumns :
      LinearMap.toMatrix b (Pi.basisFun R n) A.mulVecLin.ker.subtype =
        Matrix.of (fun i j ↦ (b j : n → R) i) := by
    ext i j
    simp [LinearMap.toMatrix_apply]
  rw [← hcolumns, ← LinearMap.toMatrix_comp, Submodule.projectionOnto_comp_subtype,
    LinearMap.toMatrix_id]

end Matrix

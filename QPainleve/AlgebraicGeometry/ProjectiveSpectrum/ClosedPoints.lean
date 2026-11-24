/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.LinearAction

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedPoints

/-!
# Projective linear changes of closed points

The description of closed points by nonzero linear functionals in
`ProjectiveSpectrum.exists_ne_zero_forall_mem_symmetricAlgebra_iff_of_isClosed`
identifies the orbits of `Proj.symmetricAlgebraMapIso`. In particular a specified
closed center can be moved to a coordinate vertex before taking a point blowup.
-/

public section

open CategoryTheory Module TauCeti.SymmetricAlgebra

namespace AlgebraicGeometry.Proj

universe u

variable {k M : Type u} [Field k] [IsAlgClosed k] [AddCommGroup M] [Module k M]
  [Module.Finite k M]

local notation "P" => Proj (homogeneousSubmodule k M)

/-- Projective linear automorphisms act transitively on the closed points of the
projective spectrum of the symmetric algebra of a finite-dimensional vector space. -/
theorem exists_symmetricAlgebraMapIso_hom_apply_eq_of_isClosed (x y : P)
    (hx : IsClosed {x}) (hy : IsClosed {y}) :
    ∃ e : M ≃ₗ[k] M, (symmetricAlgebraMapIso k e).hom x = y := by
  classical
  obtain ⟨f, hf, hfx⟩ :=
    ProjectiveSpectrum.exists_ne_zero_forall_mem_symmetricAlgebra_iff_of_isClosed x hx
  obtain ⟨g, hg, hgy⟩ :=
    ProjectiveSpectrum.exists_ne_zero_forall_mem_symmetricAlgebra_iff_of_isClosed y hy
  let toF := LinearEquiv.toSpanNonzeroSingleton k _ f hf
  let toG := LinearEquiv.toSpanNonzeroSingleton k _ g hg
  obtain ⟨a, ha⟩ := Submodule.exists_linearEquiv_restrict_eq (toF.symm.trans toG)
  have haf : a f = g := by
    have hOne : toF.symm ⟨f, Submodule.mem_span_singleton_self f⟩ = 1 :=
      LinearEquiv.coord_self k _ f hf
    simpa [toG, hOne] using (ha ⟨f, Submodule.mem_span_singleton_self f⟩).symm
  let eval := Module.evalEquiv k M
  let e := eval.trans (a.dualMap.trans eval.symm)
  have hfg : f.comp e.toLinearMap = g := by
    ext v
    calc
      f (e v) = eval (e v) f := (Module.Dual.eval_apply k M (e v) f).symm
      _ = (eval v) (a f) := by
        simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
          LinearEquiv.dualMap_apply]
      _ = g v := by rw [haf]; rfl
  have hLift : (SymmetricAlgebra.lift f).comp (SymmetricAlgebra.map k e.toLinearMap) =
      SymmetricAlgebra.lift g := by
    apply SymmetricAlgebra.algHom_ext
    ext v
    simpa using DFunLike.congr_fun hfg v
  refine ⟨e, ProjectiveSpectrum.ext_of_mem_pos fun n hn s hs ↦ ?_⟩
  let F := SymmetricAlgebra.gradedMap k e.toLinearMap
  have hmap : s ∈ ((symmetricAlgebraMapIso k e).hom x).asHomogeneousIdeal ↔
      F s ∈ x.asHomogeneousIdeal := by
    rw [← not_iff_not, ← mem_basicOpen, ← Scheme.Hom.mem_preimage,
      symmetricAlgebraMapIso_hom, map_preimage_basicOpen, mem_basicOpen]
  have hEval : SymmetricAlgebra.lift f (F s) = SymmetricAlgebra.lift g s := by
    simpa only [F, SymmetricAlgebra.gradedMap_apply, AlgHom.comp_apply] using
      DFunLike.congr_fun hLift s
  exact hmap.trans ((hfx n hn _ (F.map_mem hs)).trans (hEval ▸ (hgy n hn _ hs).symm))

end AlgebraicGeometry.Proj

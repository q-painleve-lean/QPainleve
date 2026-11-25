/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Cohomology.TracePairing
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveLine.Differentials
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveLine.Basic
import TauCeti.AlgebraicGeometry.Curves.Differentials
import TauCeti.AlgebraicGeometry.Geometrically.Irreducible

/-!
# The residue pairing on the projective line

Evaluation into the relative differential sheaf followed by the coordinate-normalized
trace pairs the first cohomology of a line bundle with sections of its differential-valued
dual. The pairing is perfect over any field, including the residue field of a center of
a surface blowup.

The trace is Tau Ceti's `projectiveLine.cohomologyOneDifferentialsLinearEquiv`, which sends
the Mayer–Vietoris class of `dt/t` to one. The dimensions agree by Tau Ceti's
`finrank_cohomology_one_eq_finrank_cohomology_zero_differentials_tensor_dual_of_smooth`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonoidalClosed
open TauCeti TauCeti.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry.projectiveLine

universe u

variable (R : Type u) [CommRing R]

local notation "P" => projectiveLine R
local notation "Ω" => Scheme.relativeDifferentials R (projectiveLine R)

/-- Pair a class in `H¹(ℙ¹, L)` with a section of `Hom(L, Ω)` by evaluation and the
trace normalized by the class of `dt/t`. -/
def cohomologyResiduePairing (L : InvertibleSheaf P) :
    Cohomology L.obj 1 →ₗ[R] Γ((ihom L.obj).obj Ω, ⊤) →ₗ[R] R :=
  cohomologyTracePairing R 1 (cohomologyOneDifferentialsLinearEquiv R).toLinearMap

/-- The residue pairing evaluates the morphism represented by the section and then
takes the normalized trace. -/
@[simp]
theorem cohomologyResiduePairing_apply (L : InvertibleSheaf P) (x : Cohomology L.obj 1)
    (s : Γ((ihom L.obj).obj Ω, ⊤)) :
    cohomologyResiduePairing R L x s =
      cohomologyOneDifferentialsLinearEquiv R
        (cohomologyMapBaseLinear R P (internalHomSectionsEquiv s) 1 x) :=
  cohomologyTracePairing_apply R 1 (cohomologyOneDifferentialsLinearEquiv R).toLinearMap x s

/-- The coordinate-normalized residue pairing is perfect for every line bundle on the
projective line over a field. -/
theorem isPerfPair_cohomologyResiduePairing (k : Type u) [Field k]
    (L : InvertibleSheaf (projectiveLine k)) : (cohomologyResiduePairing k L).IsPerfPair := by
  let K : InvertibleSheaf (projectiveLine k) :=
    ⟨Scheme.relativeDifferentials k (projectiveLine k), isInvertible_relativeDifferentials k⟩
  have hK : K = InvertibleSheaf.relativeDifferentials k (projectiveLine k) :=
    ObjectProperty.FullSubcategory.ext (InvertibleSheaf.relativeDifferentials_obj k _).symm
  let M := K.tensorProduct L.dual
  let e₀ := L.sectionsInternalHomLinearEquiv k K
  have := finite_cohomology_one k L.obj
  have := finite_cohomology_zero k M.obj
  have := Module.Finite.equiv e₀.symm
  have hdim : Module.finrank k Γ((ihom L.obj).obj K.obj, ⊤) =
      Module.finrank k (Module.Dual k (Cohomology L.obj 1)) := by
    rw [e₀.finrank_eq, Subspace.dual_finrank_eq]
    let eM := eqToIso (congrArg (fun K' ↦ (K'.tensorProduct L.dual).obj) hK)
    exact (cohomologyBaseLinearEquivOfIso k eM 0).finrank_eq.trans
      (finrank_cohomology_one_eq_finrank_cohomology_zero_differentials_tensor_dual_of_smooth
        (k := k) L).symm
  have htr : (cohomologyOneDifferentialsLinearEquiv k).toLinearMap ≠ 0 := by
    intro h
    exact one_ne_zero ((LinearEquiv.apply_symm_apply _ _).symm.trans
      (DFunLike.congr_fun h ((cohomologyOneDifferentialsLinearEquiv k).symm 1)))
  have : IsNoetherian (projectiveLine k) :=
    isNoetherian_of_finiteType (projectiveLine k ↘ Spec (.of k))
  have hcurve := topologicalKrullDim_eq_of_smoothOfRelativeDimension
    (projectiveLine k ↘ Spec (.of k)) (n := 1)
  have hinj : Function.Injective (cohomologyResiduePairing k L).flip :=
    cohomologyTracePairing_injective_flip_of_surjective k _ htr fun f hf ↦
      L.surjective_cohomologyMap_one_of_ne_zero k K f hf hcurve.le
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (cohomologyResiduePairing k L).flip)).mp hinj
  exact (LinearMap.IsPerfPair.of_bijective _ ⟨hinj, hsurj⟩).flip

end TauCeti.AlgebraicGeometry.projectiveLine

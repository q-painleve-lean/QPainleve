/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Cohomology.Isomorphism
public import QPainleve.AlgebraicGeometry.Cohomology.TracePairing
public import QPainleve.AlgebraicGeometry.Modules.InternalHom.Pullback

/-!
# Trace pairings under scheme isomorphisms

For an isomorphism over the base ring, the cohomology and internal Hom
comparisons carry the trace pairing to the trace pairing of the transported
functional. This transports perfection, including between the two models of
a common resolution.
-/

public noncomputable section

open CategoryTheory MonoidalClosed TauCeti
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
  (R : Type u) [CommRing R] [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  [f.IsOver (Spec (.of R))] {M N : Y.Modules} {M' N' : X.Modules}

variable (a : (pullback f).obj M ≅ M') (b : (pullback f).obj N ≅ N')
  (q : ℕ) (tr : Cohomology N q →ₗ[R] R)

/-- Evaluating the trace pairing on a pulled-back section is equivalent to
evaluating on the original section after identifying the cohomology class. -/
theorem cohomologyTracePairing_pullbackInternalHomSectionsLinearEquiv
    (x : Cohomology M' q) (s : Γ((ihom M).obj N, ⊤)) :
    cohomologyTracePairing R q
        (tr.comp (f.cohomologyBaseLinearEquivOfPullbackIso R b q).toLinearMap)
        x (f.pullbackInternalHomSectionsLinearEquiv R a b s) =
      cohomologyTracePairing R q tr (f.cohomologyBaseLinearEquivOfPullbackIso R a q x) s := by
  simp only [cohomologyTracePairing_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    internalHomSectionsEquiv_pullbackInternalHomSectionsLinearEquiv,
    cohomologyBaseLinearEquivOfPullbackIso_naturality]

include a in
/-- Perfection of the trace pairing is invariant under an isomorphism of schemes
with the trace and both coefficient sheaves transported along that isomorphism. -/
theorem isPerfPair_cohomologyTracePairing_iff_of_isIso :
    (cohomologyTracePairing (M := M') R q
      (tr.comp (f.cohomologyBaseLinearEquivOfPullbackIso R b q).toLinearMap)).IsPerfPair ↔
      (cohomologyTracePairing (M := M) R q tr).IsPerfPair := by
  let e := f.cohomologyBaseLinearEquivOfPullbackIso R a q
  let d := f.pullbackInternalHomSectionsLinearEquiv R a b
  let p := cohomologyTracePairing (M := M) R q tr
  let p' := cohomologyTracePairing (M := M') R q
    (tr.comp (f.cohomologyBaseLinearEquivOfPullbackIso R b q).toLinearMap)
  have h : p'.compl₁₂ e.symm d = p := by
    ext x s
    simpa only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, e, d, p, p',
      LinearEquiv.apply_symm_apply] using
      f.cohomologyTracePairing_pullbackInternalHomSectionsLinearEquiv R a b q tr (e.symm x) s
  have h' : p.compl₁₂ e d.symm = p' := by
    rw [← h]
    ext x s
    simp [LinearMap.compl₁₂_apply]
  constructor
  · intro hp
    have : p'.IsPerfPair := hp
    exact LinearMap.IsPerfPair.congr p' e.symm d p h'
  · intro hp
    have : p.IsPerfPair := hp
    exact LinearMap.IsPerfPair.congr p e d.symm p' h

end AlgebraicGeometry.Scheme.Hom

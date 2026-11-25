/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Cohomology.TracePairing

/-!
# Transport of perfect cohomology trace pairings

Changing the source sheaf by an isomorphism preserves perfection. The
comparison uses the action of each section as a sheaf morphism under the
cohomology functor.
-/

public noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))]

/-- Replacing the source sheaf by an isomorphic one preserves perfection of the
trace pairing. -/
theorem isPerfPair_cohomologyTracePairing_of_iso {M M' N : X.Modules}
    (e : M ≅ M') (q : ℕ) (tr : Cohomology N q →ₗ[k] k)
    [FiniteDimensional k (Cohomology M q)]
    (h : (cohomologyTracePairing (M := M) k q tr).IsPerfPair) :
    (cohomologyTracePairing (M := M') k q tr).IsPerfPair := by
  let E := cohomologyBaseLinearEquivOfIso k e q
  let H := internalHomSectionsEquiv.trans ((e.homCongr (Iso.refl N)).trans
    internalHomSectionsEquiv.symm)
  have hE (x : Cohomology M q) (s : Γ((ihom M).obj N, ⊤)) :
      cohomologyTracePairing k q tr (E x) (H s) = cohomologyTracePairing k q tr x s := by
    have hH : internalHomSectionsEquiv (H s) = e.inv ≫ internalHomSectionsEquiv s := by
      simp [H, Iso.homCongr]
    rw [cohomologyTracePairing_apply, cohomologyTracePairing_apply, hH]
    dsimp only [E]
    rw [cohomologyBaseLinearEquivOfIso_apply]
    have he := LinearMap.congr_fun
      (cohomologyMapBaseLinear_comp k X e.hom (e.inv ≫ internalHomSectionsEquiv s) q) x
    simpa only [Iso.hom_inv_id_assoc, LinearMap.comp_apply] using (congrArg tr he).symm
  have := Module.Finite.equiv E
  apply LinearMap.IsPerfPair.of_injective
  · refine (injective_iff_map_eq_zero _).mpr fun y hy ↦ ?_
    obtain ⟨x, rfl⟩ := E.surjective y
    have hx : x = 0 := h.separatingLeft x fun s ↦
      (hE x s).symm.trans (DFunLike.congr_fun hy (H s))
    simp [hx]
  · refine (injective_iff_map_eq_zero _).mpr fun t ht ↦ ?_
    obtain ⟨s, rfl⟩ := H.surjective t
    have hs : s = 0 := h.separatingRight s fun x ↦
      (hE x s).symm.trans (DFunLike.congr_fun ht (E x))
    apply internalHomSectionsEquiv.injective
    simp [H, hs, Iso.homCongr]

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.GlobalCoordinates
import TauCeti.RingTheory.MvPolynomial.Homogeneous

/-!
# Rescaling polynomial projective coordinates

An indexed family of projective coordinates defines the same morphism after
multiplication by a common unit, by Tau Ceti's homogeneous rescaling theorem.
-/

public section

open MvPolynomial hiding X

namespace AlgebraicGeometry.Proj

universe u

variable {R ι : Type u} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A common unit rescaling of the variables preserves the induced projective morphism
when the evaluation maps agree on coefficients. -/
theorem fromOfGlobalSections_eq_of_X_unit_rescaling {S : Scheme.{u}}
    (p q : MvPolynomial ι R →+* Γ(S, ⊤)) (c : Γ(S, ⊤)ˣ)
    (hC : p.comp C = q.comp C) (hX : ∀ i, q (.X i) = c * p (.X i))
    (hp : (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι R)).toIdeal.map p = ⊤)
    (hq : (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι R)).toIdeal.map q = ⊤) :
    Proj.fromOfGlobalSections _ p hp = Proj.fromOfGlobalSections _ q hq := by
  have eval_eq (g : MvPolynomial ι R →+* Γ(S, ⊤)) :
      eval₂Hom (g.comp C) (fun k ↦ g (.X k)) = g := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro k
      simp
  have he (n : ℕ) (a : MvPolynomial ι R) (ha : a ∈ homogeneousSubmodule ι R n) :
      q a = c ^ n * p a := by
    calc
      q a = eval₂ (p.comp C) (fun k ↦ c * p (.X k)) a := by
        simpa only [← hC, hX, coe_eval₂Hom] using DFunLike.congr_fun (eval_eq q).symm a
      _ = c ^ n * p a := by
        simpa only [← coe_eval₂Hom, eval_eq] using
          (mem_homogeneousSubmodule _ _ |>.mp ha).eval₂_const_mul (p.comp C)
            (fun k ↦ p (.X k)) (c : Γ(S, ⊤))
  exact (TauCeti.ProjectiveSpectrum.fromOfGlobalSections_eq_of_unit_rescaling
    _ p q c he hp).symm

end AlgebraicGeometry.Proj

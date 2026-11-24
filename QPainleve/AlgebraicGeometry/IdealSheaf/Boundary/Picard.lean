/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Excision

/-!
# Picard classes and fixation of boundary primes

If the Picard classes of the primes supported on a closed subscheme distinguish those
primes, a boundary-preserving automorphism fixing the Picard classes fixes the primes.
-/

public section

open CategoryTheory TauCeti.AlgebraicGeometry
open LineBundleClass

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [∀ x : X, IsDomain (X.presheaf.stalk x)]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

/-- An automorphism preserving the boundary support and fixing its prime classes fixes
the boundary primes if their classes distinguish them. -/
theorem fixes_boundary_primes_of_pullback_eq (D : X.IdealSheafData) (e : X ≅ X)
    (hD : Set.MapsTo e.hom (D.support : Set X) D.support)
    (hinj : Set.InjOn primeDivisorClass {p : CodimensionOnePoint X | (p : X) ∈ D.support})
    (hPic : ∀ p : CodimensionOnePoint X, (p : X) ∈ D.support →
      pullback e.hom (primeDivisorClass p) = primeDivisorClass p)
    (p : CodimensionOnePoint X) (hp : (p : X) ∈ D.support) : e.hom p = p := by
  let q := CodimensionOnePoint.mapOfIsOpenImmersion e.hom p
  have hq : (q : X) ∈ D.support := by
    simpa only [q, CodimensionOnePoint.coe_mapOfIsOpenImmersion, SetLike.mem_coe] using hD hp
  have hclass : primeDivisorClass p = primeDivisorClass q :=
    (pullback_primeDivisorClass_mapOfIsOpenImmersion e.hom p).symm.trans (hPic q hq)
  simpa only [q, CodimensionOnePoint.coe_mapOfIsOpenImmersion] using
    congrArg Subtype.val (hinj hq hp hclass.symm)

end AlgebraicGeometry.Scheme.IdealSheafData

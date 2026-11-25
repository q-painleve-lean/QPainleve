/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Unramified.Basic
public import TauCeti.RingTheory.FittingIdeal.BaseChange
import QPainleve.RingTheory.Kaehler.LocalCoordinates
import TauCeti.RingTheory.Ideal.Operations
import TauCeti.RingTheory.Node.Hessian

/-!
# The singular ideal of a quadratic hypersurface

For a quadratic equation in two local coordinates with formally unramified residue algebra,
a unit discriminant makes the first Fitting ideal of the hypersurface differentials
the maximal ideal.
This uses the Hessian and Fitting ideal criterion for nodes from Tau Ceti.
-/

public section

open IsLocalRing KaehlerDifferential TauCeti

namespace QPainleve

/-- For a quadratic hypersurface in a local algebra with two independent differentials,
the discriminant is a unit exactly when the singular ideal cuts out the reduced closed point. -/
theorem fittingIdeal_eq_maximalIdeal_iff_isUnit_discrim
    {k P A : Type*} [CommRing k] [CommRing P] [IsLocalRing P] [Algebra k P]
    [Algebra.FormallyUnramified k (ResidueField P)] [CommRing A] [IsLocalRing A] [Algebra k A]
    [Algebra.EssFiniteType k A]
    (basis : Module.Basis (Fin 2) P Ω[P⁄k]) (π : P →ₐ[k] A) (hπ : Function.Surjective π)
    {x y a b c f : P} (hxy : Ideal.span {x, y} = maximalIdeal P)
    (hker : RingHom.ker π = Ideal.span {f}) (hf : f = a * x ^ 2 + b * x * y + c * y ^ 2) :
    fittingIdeal A Ω[A⁄k] 1 = maximalIdeal A ↔ IsUnit (discrim a b c) := by
  let e := (Ideal.quotientEquivAlgOfEq k hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hπ)
  have : Algebra.EssFiniteType k (P ⧸ Ideal.span {f}) :=
    .of_surjective e.symm.toAlgHom e.symm.surjective
  let z : Fin 2 → P := ![x, y]
  have hz : maximalIdeal P = Ideal.span (Set.range z) := by
    simpa only [z, Matrix.range_cons_cons_empty] using hxy.symm
  have hmem (i : Fin 2) : z i ∈ maximalIdeal P := hz ▸ Ideal.subset_span ⟨i, rfl⟩
  have : Algebra.FormallyUnramified k (P ⧸ Ideal.span (Set.range z)) := hz ▸ inferInstanceAs
    (Algebra.FormallyUnramified k (ResidueField P))
  obtain ⟨basis', hb⟩ :=
    basis.exists_basis_kaehlerDifferential_of_formallyUnramified_quotient z hmem
  have hder (i j : Fin 2) : (basis'.coord i).compDer (D k P) (z j) =
      if i = j then 1 else 0 := by
    simp [← hb, Finsupp.single_apply, eq_comm]
  have heq := comap_fittingIdeal_kaehlerDifferential_eq_maximalIdeal_iff (f := f) basis' hz hb
  have : IsLocalRing (P ⧸ Ideal.span {f}) := e.symm.toRingEquiv.isLocalRing
  have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {f})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hcomap : (maximalIdeal (P ⧸ Ideal.span {f})).comap (Ideal.Quotient.mk _) =
      maximalIdeal P := maximalIdeal_comap _
  have hfit := fittingIdeal_kaehlerDifferential_eq_map_algEquiv e 1
  rw [hfit, ← map_maximalIdeal_of_surjective e.toRingHom e.surjective]
  -- Both ideals are mapped by the same algebra equivalence, viewed as a ring homomorphism.
  change (Ideal.map e.toRingHom _ = Ideal.map e.toRingHom _) ↔ _
  have hk : RingHom.ker e.toRingHom = ⊥ := RingHom.ker_equiv e.toRingEquiv
  rw [Ideal.map_eq_iff_sup_ker_eq_of_surjective e.toRingHom e.surjective,
    hk, sup_bot_eq, sup_bot_eq,
    ← (Ideal.comap_injective_of_surjective (Ideal.Quotient.mk (Ideal.span {f}))
      Ideal.Quotient.mk_surjective).eq_iff, hcomap]
  norm_num at heq
  rw [heq, hf]
  have hquad : a * x ^ 2 + b * x * y + c * y ^ 2 ∈ maximalIdeal P ^ 2 :=
    hxy ▸ Ideal.mem_span_pair_sq.mpr ⟨a, b, c, rfl⟩
  exact (and_iff_right hquad).trans (isUnit_det_hessian_iff_isUnit_discrim hmem hder a b c)

end QPainleve

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Scheme.Stalk
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
public import TauCeti.RingTheory.FittingIdeal.Basic

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Unramified.Field
import QPainleve.AlgebraicGeometry.Modules.Differentials.Stalk
import QPainleve.RingTheory.Kaehler.Hypersurface
import QPainleve.RingTheory.Kaehler.LocalCoordinates
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Stalk

/-!
# Transverse intersections of effective Cartier divisors

At a closed point of a smooth surface over a perfect field, transverse effective
Cartier divisors give a product equation whose first Fitting ideal of
differentials is the maximal ideal of the product divisor's stalk.
-/

public section

open CategoryTheory TopologicalSpace IsLocalRing TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [hsmooth : SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

/-- At a closed point where two effective Cartier divisors in a smooth surface
meet transversely, the first Fitting ideal of the product divisor's differentials
is the maximal ideal of its stalk. -/
theorem fittingIdeal_stalk_mul_eq_maximalIdeal_of_stalkIdeal_sup_eq
    [PerfectField k] {I J : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier)
    (p : (I * J).subscheme)
    (hp : IsClosed ({(I * J).subschemeι p} : Set X))
    (htrans : I.stalkIdeal ((I * J).subschemeι p) ⊔ J.stalkIdeal ((I * J).subschemeι p) =
      maximalIdeal (X.presheaf.stalk ((I * J).subschemeι p))) :
    let := SmoothOfRelativeDimension.smooth 2 (X ↘ Spec (.of k))
    let _ : LocallyOfFiniteType ((I * J).subscheme ↘ Spec (.of k)) := by
      rw [(I * J).over_eq_subschemeι_comp]
      infer_instance
    let := (I * J).subscheme.essFiniteType_stalk k p
    fittingIdeal ((I * J).subscheme.presheaf.stalk p) Ω[(I * J).subscheme.presheaf.stalk p⁄k] 1 =
      maximalIdeal ((I * J).subscheme.presheaf.stalk p) := by
  dsimp only
  let i := (I * J).subschemeι
  let x := i p
  let P := X.presheaf.stalk x
  let L := (I * J).subscheme.presheaf.stalk p
  have := SmoothOfRelativeDimension.smooth 2 (X ↘ Spec (.of k))
  have : LocallyOfFiniteType ((I * J).subscheme ↘ Spec (.of k)) := by
    rw [(I * J).over_eq_subschemeι_comp]
    infer_instance
  have : Algebra.EssFiniteType k L := (I * J).subscheme.essFiniteType_stalk k p
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  obtain ⟨a, _, ha⟩ := hI.exists_map_germ_eq_span_singleton ⟨U, hU⟩ hxU
  obtain ⟨b, _, hb⟩ := hJ.exists_map_germ_eq_span_singleton ⟨U, hU⟩ hxU
  have ha' : I.stalkIdeal x = Ideal.span {a} := (I.stalkIdeal_eq_map _ _ hxU).trans ha
  have hb' : J.stalkIdeal x = Ideal.span {b} := (J.stalkIdeal_eq_map _ _ hxU).trans hb
  have hab : Ideal.span {a, b} = maximalIdeal P := by
    rw [Ideal.span_insert, ← ha', ← hb']
    exact htrans
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hp
  have hf : IsFinite (X.fromSpecResidueField x ≫ X ↘ Spec (.of k)) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have : Module.Finite k (X.residueField x) := by
    rwa [Scheme.fromSpecResidueField_comp_over, IsFinite.SpecMap_iff, CommRingCat.hom_ofHom,
      RingHom.finite_algebraMap] at hf
  obtain ⟨basis⟩ := X.nonempty_basis_kaehlerDifferential_stalk (k := k) 2 x
  let v : Fin 2 → P := ![a, b]
  have hv : Ideal.span (Set.range v) = maximalIdeal P := by
    rw [← hab]
    congr 1
    ext z
    simp [v, or_comm, eq_comm]
  have hsep : Algebra.FormallyUnramified k (X.residueField x) := .of_isSeparable _ _
  have : Algebra.FormallyUnramified k (P ⧸ Ideal.span (Set.range v)) := hv ▸ hsep
  obtain ⟨c, hc⟩ := basis.exists_basis_kaehlerDifferential_of_formallyUnramified_quotient v
    (fun j ↦ hv ▸ Ideal.subset_span ⟨j, rfl⟩)
  let f := i.stalkMapAlgHom (k := k) p
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨a, ha⟩ := i.stalkMap_surjective p y
    exact ⟨a, (i.stalkMapAlgHom_apply (k := k) p a).trans ha⟩
  have hker : RingHom.ker f = Ideal.span {a * b} := by
    rw [AlgHom.ker_coe, i.stalkMapAlgHom_toRingHom, i.ker_stalkMap_of_isClosedImmersion,
      ker_subschemeι, stalkIdeal_mul, ha', hb', Ideal.span_singleton_mul_span_singleton]
  rw [c.fittingIdeal_kaehlerDifferential_eq_map_span_of_ker_eq_span_mul
    (x := a) (y := b) (hc 0) (hc 1) f hsurj hker, hab]
  exact IsLocalRing.map_maximalIdeal_of_surjective _ hsurj

end AlgebraicGeometry.Scheme.IdealSheafData

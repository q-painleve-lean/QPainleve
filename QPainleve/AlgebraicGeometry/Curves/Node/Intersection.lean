/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Order
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over
public import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
public import TauCeti.RingTheory.FittingIdeal.Basic
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import QPainleve.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import QPainleve.AlgebraicGeometry.Modules.Differentials.Stalk
import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial
import QPainleve.RingTheory.Kaehler.LocalCoordinates
import QPainleve.RingTheory.Node.Intersection
import Mathlib.RingTheory.Unramified.Field
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Factorial
import TauCeti.AlgebraicGeometry.Scheme.StalkSpecializes

/-!
# Intersections of components of a nodal Cartier divisor

At a point common to two distinct prime components of a nodal Cartier divisor in
a smooth surface, the two reduced component ideals generate the ambient maximal
ideal. The first Fitting ideal of the divisor differentials detects the intrinsic
singular subscheme and gives transversality in the surface.
See [Stacks Project, Lemma 53.19.17](https://stacks.math.columbia.edu/tag/0E38)
for the intersection of complementary unions of components of a nodal curve.
-/

public section

open CategoryTheory TopologicalSpace IsLocalRing TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [hsmooth : SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "I(" p ")" => vanishingIdeal (Closeds.mk (closure {(p : X)}) isClosed_closure)

include hsmooth in
private theorem exists_prime_stalkIdeal_generator (p : CodimensionOnePoint X) {x : X}
    (hp : (p : X) ⤳ x) :
    ∃ a : X.presheaf.stalk x, a ∈ maximalIdeal (X.presheaf.stalk x) ∧
      (I(p)).stalkIdeal x = Ideal.span {a} := by
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : ∀ y : X, IsDomain (X.presheaf.stalk y) := fun y ↦
    letI := isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k)) y
    inferInstance
  let : ∀ y : X, UniqueFactorizationMonoid (X.presheaf.stalk y) :=
    (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hI := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  obtain ⟨z, hz⟩ := (I(p)).range_subschemeι.ge (by
    rw [coe_support_vanishingIdeal, Closeds.coe_mk]
    exact specializes_iff_mem_closure.mp hp)
  obtain ⟨a, _, ha, hspan, _⟩ := hI.exists_stalkIdeal_eq_span_and_quotient z
  exact hz ▸ ⟨a, ha, hspan⟩

/-- The reduced ideals of distinct prime components of a nodal Cartier divisor
sum to the ambient maximal ideal wherever the components meet. -/
theorem IsEffectiveCartier.stalkIdeal_sup_eq_maximalIdeal_of_nodal {D : X.IdealSheafData}
    (hD : D.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subscheme ↘ Spec (.of k)))
    {p q : CodimensionOnePoint X} (hpq : p ≠ q) (hpD : (p : X) ∈ D.support)
    (hqD : (q : X) ∈ D.support) {x : X} (hp : (p : X) ⤳ x) (hq : (q : X) ⤳ x) :
    (I(p)).stalkIdeal x ⊔ (I(q)).stalkIdeal x = maximalIdeal (X.presheaf.stalk x) := by
  let := hnodal.syntomic
  have hle {y : X} (hy : y ∈ D.support) : D ≤ I(y) :=
    le_support_iff_le_vanishingIdeal.mp (closure_minimal (Set.singleton_subset_iff.mpr hy)
      D.support.isClosed)
  obtain ⟨z, rfl⟩ := D.range_subschemeι.ge (hp.mem_closed D.support.isClosed hpD)
  let x := D.subschemeι z
  obtain ⟨a, ha, hpa⟩ := exists_prime_stalkIdeal_generator (k := k) p hp
  obtain ⟨c, hc, hqc⟩ := exists_prime_stalkIdeal_generator (k := k) q hq
  obtain ⟨f, _, _, hf, _⟩ := hD.exists_stalkIdeal_eq_span_and_quotient z
  have hfa : a ∣ f := Ideal.mem_span_singleton.mp
    (hpa ▸ stalkIdeal_mono (hle hpD) x (hf ▸ Ideal.mem_span_singleton_self f))
  have hfc : f ∈ (I(q)).stalkIdeal x :=
    stalkIdeal_mono (hle hqD) x (hf ▸ Ideal.mem_span_singleton_self f)
  have hprime : ((I(q)).stalkIdeal x).IsPrime := by
    rw [stalkIdeal_vanishingIdeal_closure_singleton_of_specializes hq]
    infer_instance
  have hnot : a ∉ (I(q)).stalkIdeal x := by
    intro hm
    have hsub : (I(p)).stalkIdeal x ≤ (I(q)).stalkIdeal x := by
      rwa [hpa, Ideal.span_singleton_le_iff_mem]
    rw [stalkIdeal_vanishingIdeal_closure_singleton_of_specializes hp,
      stalkIdeal_vanishingIdeal_closure_singleton_of_specializes hq] at hsub
    exact hpq (CodimensionOnePoint.eq_of_specializes
      (Scheme.specializes_of_comap_stalkSpecializes_maximalIdeal_le hp hq hsub))
  -- The prime of the second component divides the quotient by the first component's equation.
  have hdiv : a * c ∣ f := by
    obtain ⟨r, hr⟩ := hfa
    have hm := hprime.mem_or_mem (hr ▸ hfc)
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp (hqc ▸ hm.resolve_left hnot)
    exact ⟨s, by rw [hr, hs, mul_assoc]⟩
  obtain ⟨b⟩ := X.nonempty_basis_kaehlerDifferential_stalk (k := k) 2 x
  let π := D.subschemeι.stalkMapAlgHom (k := k) z
  have hπring : (π : _ →+* _) = (D.subschemeι.stalkMap z).hom :=
    D.subschemeι.stalkMapAlgHom_toRingHom (k := k) z
  have hker : RingHom.ker π = Ideal.span {f} := by
    rw [AlgHom.ker_coe, hπring, D.subschemeι.ker_stalkMap_of_isClosedImmersion, ker_subschemeι, hf]
  have hπ : Function.Surjective π := by
    intro y
    simpa only [π, Hom.stalkMapAlgHom_apply] using D.subschemeι.stalkMap_surjective z y
  let := D.subscheme.essFiniteType_stalk k z
  let := (D.subscheme.fittingIdeal_stalk_of_atWorstNodal hnodal z).2
  rw [hpa, hqc, ← Ideal.span_insert]
  exact b.span_pair_eq_maximalIdeal_of_formallyUnramified π hπ hker ha hc hdiv

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

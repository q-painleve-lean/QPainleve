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
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import QPainleve.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import QPainleve.AlgebraicGeometry.Modules.Differentials.Stalk
import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial
import QPainleve.RingTheory.Node.Intersection
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

end AlgebraicGeometry.Scheme.IdealSheafData

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Isometry.Basic
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Primes
public import QPainleve.AlgebraicGeometry.Curves.Node.Locus

import QPainleve.AlgebraicGeometry.Blowup.Point.BoundaryPrimes
import QPainleve.AlgebraicGeometry.Blowup.Point.Picard
import QPainleve.AlgebraicGeometry.Curves.Node.ComponentOrder
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Picard isometries at corresponding boundary nodes

The extension of a Picard isometry through blowups at corresponding nodes matches
the strict-transform classes of the original boundary primes and the new exceptional
primes. At a self-node the unique component through the center loses twice the
exceptional class.

This is the boundary-class comparison for the corner blowup in the proof of
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*, Theorem 4.7][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S4.Thmtheorem7
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

universe u

namespace QPainleve.BlowupTower

local notation "pointIdeal(" p ")" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ p)
local notation "pointTower(" p ")" => (BlowupTower.nil.snoc (pointIdeal(p)))
local notation "P(" q ")" => vanishingIdeal (Closeds.mk (closure {(q : _)}) isClosed_closure)
local notation "prime(" a ")" => Scheme.IdealSheafData.boundaryPrimeEmbedding _ a
local notation "S(" k ")" => Spec (CommRingCat.of k)
local notation "g(" k ", " X ")" => (X ↘ S(k))
local notation "B(" k ", " S ")" => Chow.intersectionBilinForm k S

variable {k : Type u} [Field k] {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
  [X.Over S(k)] [Z.Over S(k)]
  [SmoothOfRelativeDimension 2 (g(k, X))] [SmoothOfRelativeDimension 2 (g(k, Z))]
  {D : X.IdealSheafData} {F : Z.IdealSheafData} {p : X} {q : Z}
  (σ : D.boundaryPrimes ≃ F.boundaryPrimes)
  (hcenter : ∀ a : D.boundaryPrimes, p ∈ closure {a.val} ↔ q ∈ closure {(σ a).val})

include hcenter in
private theorem stalkOrder_prime_eq_of_matching_nodes [QuasiCompact (g(k, X))]
    [QuasiCompact (g(k, Z))]
    (hD : D.IsEffectiveCartier) (hF : F.IsEffectiveCartier)
    (hnd : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ g(k, X)))
    (hnf : AtWorstNodalOfRelativeDimensionOne (F.subschemeι ≫ g(k, Z)))
    (hp : D.IsNodeOfReducedBoundary (g(k, X)) p) (hq : F.IsNodeOfReducedBoundary (g(k, Z)) q)
    (a : D.boundaryPrimes) :
    (P(a.val)).stalkOrder p = (P((σ a).val)).stalkOrder q := by
  classical
  have hother :
      (∃ b : D.boundaryPrimes, b ≠ a ∧ p ∈ closure {b.val}) ↔
        ∃ b : F.boundaryPrimes, b ≠ σ a ∧ q ∈ closure {b.val} := by
    constructor
    · rintro ⟨b, hba, hb⟩
      exact ⟨σ b, fun h ↦ hba (σ.injective h), (hcenter b).mp hb⟩
    · rintro ⟨b, hba, hb⟩
      obtain ⟨b, rfl⟩ := σ.surjective b
      exact ⟨b, fun h ↦ hba (congrArg σ h), (hcenter b).mpr hb⟩
  have hD' := hD.stalkOrder_prime_eq_of_node hnd hp prime(a)
    (by simpa only [coe_boundaryPrimeEmbedding] using (mem_boundaryPrimes.mp a.property).1)
  have hF' := hF.stalkOrder_prime_eq_of_node hnf hq prime(σ a)
    (by simpa only [coe_boundaryPrimeEmbedding] using (mem_boundaryPrimes.mp (σ a).property).1)
  simp only [coe_boundaryPrimeEmbedding] at hD' hF'
  rw [hD', hF']
  have hex {Y : Scheme.{u}} (J : Y.IdealSheafData) (x : Y) (a : J.boundaryPrimes) :
      (∃ r : CodimensionOnePoint Y, r ≠ prime(a) ∧ (r : Y) ∈ J.support ∧
        x ∈ closure {(r : Y)}) ↔ ∃ b : J.boundaryPrimes, b ≠ a ∧ x ∈ closure {b.val} := by
    constructor
    · rintro ⟨r, hr, hs, hx⟩
      exact ⟨⟨r, mem_boundaryPrimes.mpr ⟨hs, r.property⟩⟩,
        fun h ↦ hr (Subtype.ext (by
          simpa only [coe_boundaryPrimeEmbedding] using
            congrArg (fun t : J.boundaryPrimes ↦ t.val) h)), hx⟩
    · rintro ⟨b, hba, hb⟩
      exact ⟨prime(b),
        fun h ↦ hba (Subtype.ext (by
          simpa only [coe_boundaryPrimeEmbedding] using
            congrArg (fun t : CodimensionOnePoint Y ↦ t.val) h)),
        by simpa only [coe_boundaryPrimeEmbedding] using (mem_boundaryPrimes.mp b.property).1,
        by simpa only [coe_boundaryPrimeEmbedding] using hb⟩
  rw [if_congr (hcenter a) (if_congr ((hex D p a).trans (hother.trans (hex F q (σ a)).symm))
    rfl rfl) rfl]

include hcenter in
/-- If the Picard isometry matches the original boundary classes, blowing up two
closed nodes incident to the corresponding components extends the correspondence
to every prime of the reduced total boundaries, including the exceptional primes.
Boundary primes depend only on support. The result also records the images of the
paired primes on the original surfaces. -/
theorem picardIsometryCongr_nodal_boundaryPrimes
    [IsAlgClosed k] [X.IsProjectiveOver k] [Z.IsProjectiveOver k]
    (e : B(k, X).IsometryEquiv B(k, Z))
    (he : letI := (g(k, X)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
          letI := (g(k, Z)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
          letI := LocallyOfFiniteType.isLocallyNoetherian (g(k, X))
          letI := LocallyOfFiniteType.isLocallyNoetherian (g(k, Z))
          ∀ a : D.boundaryPrimes, e (Additive.ofMul (primeDivisorClass prime(a))) =
            Additive.ofMul (primeDivisorClass prime(σ a)))
    (hp : IsClosed ({p} : Set X)) (hq : IsClosed ({q} : Set Z))
    (hD : D.IsEffectiveCartier) (hF : F.IsEffectiveCartier)
    (hnd : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ g(k, X)))
    (hnf : AtWorstNodalOfRelativeDimensionOne (F.subschemeι ≫ g(k, Z)))
    (hpn : D.IsNodeOfReducedBoundary (g(k, X)) p)
    (hqn : F.IsNodeOfReducedBoundary (g(k, Z)) q) :
    let T := pointTower(p)
    let U := pointTower(q)
    let hT : IsClosedPointTower X T := .snoc .nil p hp rfl
    let hU : IsClosedPointTower Z U := .snoc .nil q hq rfl
    letI : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
    letI : IsNoetherian Z := isNoetherian_of_finiteType (g(k, Z))
    letI := T.isNoetherian
    letI := U.isNoetherian
    letI := hT.isIntegral (g(k, X))
    letI := hU.isIntegral (g(k, Z))
    letI : SmoothOfRelativeDimension 2 (T.toBase ≫ g(k, X)) :=
      hT.smoothOfRelativeDimension (g(k, X))
    letI : SmoothOfRelativeDimension 2 (U.toBase ≫ g(k, Z)) :=
      hU.smoothOfRelativeDimension (g(k, Z))
    letI := (T.toBase ≫ g(k, X)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    letI := (U.toBase ≫ g(k, Z)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let π := blowupToBase (pointIdeal(p))
    let τ := blowupToBase (pointIdeal(q))
    ∃ σ' : (D.comap π).boundaryPrimes ≃ (F.comap τ).boundaryPrimes,
      ∀ a, picardIsometryCongr k hT hU e (Additive.ofMul (primeDivisorClass prime(a))) =
          Additive.ofMul (primeDivisorClass prime(σ' a)) ∧
        ((π a.val = p ∧ τ (σ' a).val = q) ∨
          ∃ b : D.boundaryPrimes, π a.val = b.val ∧ τ (σ' a).val = (σ b).val) := by
  let T := pointTower(p)
  let U := pointTower(q)
  have hT : IsClosedPointTower X T := .snoc .nil p hp rfl
  have hU : IsClosedPointTower Z U := .snoc .nil q hq rfl
  have : Smooth (g(k, X)) := SmoothOfRelativeDimension.smooth 2 _
  have : Smooth (g(k, Z)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
  have : IsNoetherian Z := isNoetherian_of_finiteType (g(k, Z))
  have := T.isNoetherian
  have := U.isNoetherian
  have : IsIntegral (pointIdeal(p)).blowup := hT.isIntegral (g(k, X))
  have : IsIntegral (pointIdeal(q)).blowup := hU.isIntegral (g(k, Z))
  have := hT.smoothOfRelativeDimension (g(k, X))
  have := hU.smoothOfRelativeDimension (g(k, Z))
  let := (g(k, X)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := (g(k, Z)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := (T.toBase ≫ g(k, X)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := (U.toBase ≫ g(k, Z)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  obtain ⟨l, hl, hlp⟩ := D.exists_equiv_boundaryPrimes_comap_pointBlowup (g(k, X)) hp
    (mem_support_of_isNodeOfReducedBoundary hpn)
  obtain ⟨r, hr, hrq⟩ := F.exists_equiv_boundaryPrimes_comap_pointBlowup (g(k, Z)) hq
    (mem_support_of_isNodeOfReducedBoundary hqn)
  dsimp only at l r hl hr hlp hrq ⊢
  refine ⟨l.symm.trans ((Equiv.sumCongr σ (Equiv.refl PUnit)).trans r), ?_⟩
  intro a
  obtain ⟨b | ⟨⟩, rfl⟩ := l.surjective a
  · simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply, Sum.map_inl]
    refine ⟨?_, Or.inr ⟨b, hl b, hr (σ b)⟩⟩
    rw [← picardHom_primeDivisorClass_pointBlowup (g(k, X)) hp prime(b) prime(l (.inl b))
        (by simpa only [coe_boundaryPrimeEmbedding] using hl b),
      ← picardHom_primeDivisorClass_pointBlowup (g(k, Z)) hq prime(σ b)
        prime(r (.inl (σ b))) (by simpa only [coe_boundaryPrimeEmbedding] using hr (σ b)),
      picardIsometryCongr_picardHom, he b, coe_boundaryPrimeEmbedding, coe_boundaryPrimeEmbedding,
      stalkOrder_prime_eq_of_matching_nodes σ hcenter hD hF hnd hnf hpn hqn b]
  · simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply,
      Equiv.refl_apply, Sum.map_inr]
    refine ⟨?_, Or.inl ⟨hlp, hrq⟩⟩
    have := isRegularLocalRing_stalk_of_smooth (g(k, X)) p
    have := isRegularLocalRing_stalk_of_smooth (g(k, Z)) q
    have hdp := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
      (g(k, X)) 2).mp inferInstance).2 p hp
    have hdq := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
      (g(k, Z)) 2).mp inferInstance).2 q hq
    rw [primeDivisorClass_eq_blowupExceptionalClass_of_over_center
        prime(l (.inr PUnit.unit)) (by simpa only [coe_boundaryPrimeEmbedding] using hlp) hp hdp,
      primeDivisorClass_eq_blowupExceptionalClass_of_over_center
        prime(r (.inr PUnit.unit)) (by simpa only [coe_boundaryPrimeEmbedding] using hrq) hq hdq]
    simpa only [T, U, exceptionalClass_snoc_last, ← blowupExceptionalClass_def] using
      picardIsometryCongr_exceptionalClass k hT hU e (Fin.last 0)

end QPainleve.BlowupTower

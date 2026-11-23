/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.SurfaceIntersection
public import TauCeti.AlgebraicGeometry.CartierDivisor.Excision
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import QPainleve.AlgebraicGeometry.IdealSheaf.EulerCharacteristic
import QPainleve.AlgebraicGeometry.RationalPoint
import Mathlib.Data.Set.Card.Arithmetic
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.IdealSheaf.Rank

/-!
# Local lengths of proper Cartier intersections

If two effective Cartier divisors on a projective surface meet properly, the Euler
intersection number of their Picard classes is the rank of their scheme-theoretic
intersection. In local rings this is a sum of quotient lengths weighted by residue
degrees. Over an algebraically closed field each nonzero term has weight one.
The comparison uses `IsEffectiveCartier.eulerCharBelow_eq_add_restriction`
and Tau Ceti's `Scheme.Hom.finrank_comp_eq_finsum_of_isClosedImmersion`.

The local multiplicity formula for a Cartier divisor and an integral curve is
[The Stacks Project, Lemma 43.16.4](https://stacks.math.columbia.edu/tag/0B05).
Here the successive Cartier exact sequences also apply to nonreduced divisors
when the inverse image of one on the other is effective Cartier.
-/

open CategoryTheory AlgebraicGeometry
open TauCeti TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable (k : Type u) [Field k] [Infinite k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] {I J : X.IdealSheafData}

omit [Infinite k] in
private theorem isFinite_cartierIntersection (hX : topologicalKrullDim X ≤ 2)
    (hJ : J.IsEffectiveCartier) (hIJ : (I.comap J.subschemeι).IsEffectiveCartier) :
    IsFinite ((I.comap J.subschemeι).subscheme ↘ Spec (.of k)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsProper (J.subscheme ↘ Spec (.of k)) := by
    rw [over_eq_subschemeι_comp]
    infer_instance
  have hdim : topologicalKrullDim J.subscheme ≤ 1 := hJ.topologicalKrullDim_subscheme_le
    (d := 1) hX
  have : RelativeDimensionLE 1 (J.subscheme ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr hdim
  rw [over_eq_subschemeι_comp]
  exact hIJ.isFinite_subschemeι_comp

omit [Infinite k] in
private theorem ker_cartierIntersection (I J : X.IdealSheafData) :
    ((I.comap J.subschemeι).subschemeι ≫ J.subschemeι).ker = I ⊔ J := by
  simp [Scheme.Hom.ker_comp]

/-- The surface intersection number of properly meeting effective Cartier divisors
is the rank over the ground field of their scheme-theoretic intersection. The
Picard classes of the divisors are the inverses of the classes of their ideals. -/
public theorem classIntersectionNumber_eq_finrank_intersection (hX : topologicalKrullDim X ≤ 2)
    (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier)
    (hIJ : (I.comap J.subschemeι).IsEffectiveCartier) (s : Spec (.of k)) :
    classIntersectionNumber k X (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹
        (LineBundleClass.mk hJ.toInvertibleSheaf)⁻¹ =
      ((I.comap J.subschemeι).subscheme ↘ Spec (.of k)).finrank s := by
  let K := I.comap J.subschemeι
  let a := LineBundleClass.mk hI.toInvertibleSheaf
  have : J.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k J.subschemeι
  have : IsFinite (K.subscheme ↘ Spec (.of k)) := isFinite_cartierIntersection k hX hJ hIJ
  have hdim : topologicalKrullDim X < 3 := hX.trans_lt (by decide)
  have hdimJ : topologicalKrullDim J.subscheme < 3 :=
    ((topologicalKrullDim_range_of_isPreimmersion J.subschemeι).symm.le.trans
      (topologicalKrullDim_subspace_le X _)).trans_lt hdim
  -- Restrict the trivial bundle and the ideal of the first divisor to the second divisor.
  have h₁ := hJ.eulerCharBelow_eq_add_restriction (k := k) 1 hdim
  have h₂ := hJ.eulerCharBelow_eq_add_restriction (k := k) a hdim
  have h₃ := hIJ.eulerCharBelow_eq_add_restriction (k := k) 1 hdimJ
  simp only [one_mul, LineBundleClass.pullback_one] at h₁ h₃
  rw [hI.pullback_mk_toInvertibleSheaf hIJ] at h₂
  have hχ : LineBundleClass.eulerCharBelow k (1 : LineBundleClass K.subscheme) 3 =
      (K.subscheme ↘ Spec (.of k)).finrank s := by
    let e := eqToIso (InvertibleSheaf.trivial_obj K.subscheme) ≪≫
      TauCeti.SheafOfModules.freePUnitIsoUnit K.subscheme.ringCatSheaf
    rw [LineBundleClass.eulerCharBelow_one, Scheme.Modules.eulerCharBelow_congr k e 3]
    exact (K.subschemeι.eulerCharBelow_pushforward k _ 3).symm.trans
      (K.subschemeι.eulerCharBelow_pushforward_structureSheaf k s 2)
  rw [classIntersectionNumber_eq, inv_inv, inv_inv]
  linear_combination h₁ - h₂ + h₃ + hχ

/-- Properly meeting effective Cartier divisors have positive intersection number exactly
when their supports meet. -/
public theorem classIntersectionNumber_pos_iff_support_inter_nonempty
    (hX : topologicalKrullDim X ≤ 2) (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier)
    (hIJ : (I.comap J.subschemeι).IsEffectiveCartier) :
    0 < classIntersectionNumber k X (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹
      (LineBundleClass.mk hJ.toInvertibleSheaf)⁻¹ ↔
        ((I.support : Set X) ∩ (J.support : Set X)).Nonempty := by
  let K := I.comap J.subschemeι
  let i := K.subschemeι ≫ J.subschemeι
  have : IsFinite (K.subscheme ↘ Spec (.of k)) := isFinite_cartierIntersection k hX hJ hIJ
  have hrange : Set.range i = (I.support : Set X) ∩ (J.support : Set X) := by
    rw [← TopologicalSpace.Closeds.coe_inf, ← support_sup, ← ker_cartierIntersection I J]
    exact (i.support_ker.trans i.isClosedEmbedding.isClosed_range.closure_eq).symm
  rw [classIntersectionNumber_eq_finrank_intersection k hX hI hJ hIJ default, Int.natCast_pos,
    Nat.pos_iff_ne_zero, Ne, Scheme.Hom.finrank_eq_zero_iff_notMem_range, not_not,
    ← hrange, Set.range_nonempty_iff_nonempty]
  exact ⟨fun ⟨z, _⟩ ↦ ⟨z⟩, fun ⟨z⟩ ↦ ⟨z, Subsingleton.elim _ _⟩⟩

/-- For two effective Cartier divisors meeting properly on a projective surface, the
intersection number is the sum over the surface of the local quotient lengths,
weighted by the residue degrees. The intersection scheme is finite over the field. -/
public theorem classIntersectionNumber_eq_finsum_residueDegree_mul_length
    (hX : topologicalKrullDim X ≤ 2) (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier)
    (hIJ : (I.comap J.subschemeι).IsEffectiveCartier) :
    classIntersectionNumber k X (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹
        (LineBundleClass.mk hJ.toInvertibleSheaf)⁻¹ =
      ∑ᶠ x : X, ((X ↘ Spec (.of k)).residueDegree x : ℤ) *
        (Module.length (X.presheaf.stalk x)
          (X.presheaf.stalk x ⧸ (I.stalkIdeal x ⊔ J.stalkIdeal x))).toNat := by
  let i := (I.comap J.subschemeι).subschemeι ≫ J.subschemeι
  have hbase : (I.comap J.subschemeι).subscheme ↘ Spec (.of k) = i ≫ X ↘ Spec (.of k) := by
    simp only [i, comp_over]
  have : IsFinite (i ≫ X ↘ Spec (.of k)) :=
    hbase ▸ isFinite_cartierIntersection k hX hJ hIJ
  rw [classIntersectionNumber_eq_finrank_intersection k hX hI hJ hIJ default, hbase,
    i.finrank_comp_eq_finsum_of_isClosedImmersion _ _,
    (ker_cartierIntersection I J : i.ker = I ⊔ J)]
  refine ((Nat.castAddMonoidHom ℤ).map_finsum_of_injective Nat.cast_injective _).trans ?_
  exact finsum_congr fun x ↦ by rw [stalkIdeal_sup]; exact Nat.cast_mul _ _

omit [Infinite k] in
/-- Over an algebraically closed field, the intersection number of two properly meeting
effective Cartier divisors is the sum of the ambient local intersection lengths. -/
public theorem classIntersectionNumber_eq_finsum_length [IsAlgClosed k]
    (hX : topologicalKrullDim X ≤ 2) (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier)
    (hIJ : (I.comap J.subschemeι).IsEffectiveCartier) :
    classIntersectionNumber k X (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹
        (LineBundleClass.mk hJ.toInvertibleSheaf)⁻¹ =
      ∑ᶠ x : X, ((Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ (I.stalkIdeal x ⊔ J.stalkIdeal x))).toNat : ℤ) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsLocallyNoetherian J.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (J.subschemeι ≫ X ↘ Spec (.of k))
  have := hIJ.isLocallyArtinian_subscheme (hJ.topologicalKrullDim_subscheme_le (d := 1) hX)
  let i := (I.comap J.subschemeι).subschemeι ≫ J.subschemeι
  have hi : i.ker = I ⊔ J := ker_cartierIntersection I J
  rw [classIntersectionNumber_eq_finsum_residueDegree_mul_length k hX hI hJ hIJ]
  refine finsum_congr fun x ↦ ?_
  by_cases hx : I.stalkIdeal x ⊔ J.stalkIdeal x = ⊤
  · simp [hx]
  · have hmem : x ∈ Set.range i := by
      contrapose hx
      rw [← stalkIdeal_sup, ← hi]
      exact i.stalkIdeal_ker_eq_top_of_notMem_range hx
    obtain ⟨z, rfl⟩ := hmem
    have hz : IsClosed {i z} := by
      rw [← Set.image_singleton]
      exact i.isClosedMap _ (isClosed_discrete _)
    rw [Scheme.Hom.residueDegree_eq_one_of_isClosed _ hz, Nat.cast_one, one_mul]

omit [Infinite k] in
/-- If two properly meeting effective Cartier divisors cut out the maximal ideal at each
intersection point, their intersection number over an algebraically closed field is the
number of common points. -/
public theorem classIntersectionNumber_eq_ncard_of_stalkIdeal_sup_eq_maximalIdeal [IsAlgClosed k]
    (hX : topologicalKrullDim X ≤ 2) (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier)
    (hIJ : (I.comap J.subschemeι).IsEffectiveCartier)
    (h : ∀ x ∈ (I ⊔ J).support,
      I.stalkIdeal x ⊔ J.stalkIdeal x = IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    classIntersectionNumber k X (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹
        (LineBundleClass.mk hJ.toInvertibleSheaf)⁻¹ =
      ((I ⊔ J).support : Set X).ncard := by
  rw [classIntersectionNumber_eq_finsum_length k hX hI hJ hIJ,
    ← finsum_one (s := ((I ⊔ J).support : Set X)), finsum_mem_def]
  refine Eq.trans ?_ (((Nat.castAddMonoidHom ℤ).map_finsum_of_injective
    Nat.cast_injective _).symm)
  refine finsum_congr fun x ↦ ?_
  by_cases hx : x ∈ (I ⊔ J).support
  · rw [Set.indicator_of_mem hx, h x hx, Ideal.length_quotient_eq_one, ENat.toNat_one]
    rfl
  · have htop : I.stalkIdeal x ⊔ J.stalkIdeal x = ⊤ := by
      rw [← stalkIdeal_sup]
      by_contra hproper
      exact hx (((I ⊔ J).mem_support_iff_stalkIdeal_ne_top x).mpr hproper)
    rw [Set.indicator_of_notMem hx, htop]
    simp

/-- Two distinct prime divisors on a locally factorial projective surface intersect
positively exactly when their closures meet. -/
public theorem classIntersectionNumber_primeDivisorClass_pos_iff
    [IsLocallyNoetherian X] [∀ x : X, IsDomain (X.presheaf.stalk x)]
    [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    (hX : topologicalKrullDim X ≤ 2) {p q : CodimensionOnePoint X} (hpq : p ≠ q) :
    0 < classIntersectionNumber k X (LineBundleClass.primeDivisorClass p)
        (LineBundleClass.primeDivisorClass q) ↔
      (closure {(p : X)} ∩ closure {(q : X)}).Nonempty := by
  rw [LineBundleClass.primeDivisorClass_def, LineBundleClass.primeDivisorClass_def]
  simpa only [coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_mk] using
    classIntersectionNumber_pos_iff_support_inter_nonempty k hX
      (isEffectiveCartier_vanishingIdeal_closure_singleton p.property)
      (isEffectiveCartier_vanishingIdeal_closure_singleton q.property)
      (IsEffectiveCartier.comap_subschemeι_vanishingIdeal_closure_singleton_of_ne
        (isEffectiveCartier_vanishingIdeal_closure_singleton p.property) hpq.symm)

omit [Infinite k] in
/-- Distinct prime divisors on a locally factorial projective surface over an
algebraically closed field meet with intersection number equal to the sum of their
local intersection lengths. -/
public theorem classIntersectionNumber_primeDivisorClass_eq_finsum_length [IsAlgClosed k]
    [IsLocallyNoetherian X] [∀ x : X, IsDomain (X.presheaf.stalk x)]
    [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    (hX : topologicalKrullDim X ≤ 2) {p q : CodimensionOnePoint X} (hpq : p ≠ q) :
    classIntersectionNumber k X (LineBundleClass.primeDivisorClass p)
        (LineBundleClass.primeDivisorClass q) =
      ∑ᶠ x : X, ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
        ((vanishingIdeal ⟨closure {(p : X)}, isClosed_closure⟩).stalkIdeal x ⊔
          (vanishingIdeal ⟨closure {(q : X)}, isClosed_closure⟩).stalkIdeal x))).toNat : ℤ) := by
  rw [LineBundleClass.primeDivisorClass_def, LineBundleClass.primeDivisorClass_def]
  exact classIntersectionNumber_eq_finsum_length k hX _ _
    (IsEffectiveCartier.comap_subschemeι_vanishingIdeal_closure_singleton_of_ne
      (isEffectiveCartier_vanishingIdeal_closure_singleton p.property) hpq.symm)

end TauCeti.AlgebraicGeometry.Chow

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.CartierDivisor.ZeroDivisor
public import QPainleve.AlgebraicGeometry.WeilDivisor.IdealSheaf
public import QPainleve.AlgebraicGeometry.WeilDivisor.LinearSystem.FixedPart

import QPainleve.AlgebraicGeometry.IdealSheaf.Stalk
import TauCeti.AlgebraicGeometry.IdealSheaf.Colon
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint
import TauCeti.Topology.KrullDimension.Basic

/-!
# Base ideals and multiplicities of linear systems

For a family of effective Weil divisors on a locally factorial scheme, the base ideal is the
sum of their Cartier ideals. The fixed divisor contributes a common invertible factor.
The residual ideal cuts out the base scheme of the moving system. Its order at a point is
the least order attained by a member of that system.

## References

* P. Hacking, *583C Lecture notes*, §7.2 and Proposition 7.3.
-/

public section

open AlgebraicGeometry TopologicalSpace Order

namespace TauCeti.AlgebraicGeometry.SchemeWeilDivisor

noncomputable section

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

variable {S : Set (SchemeWeilDivisor X)} (hS : ∀ D ∈ S, 0 ≤ D)

/-- The base ideal is the sum of the Cartier ideals of the divisors in the system. -/
def baseIdeal (S : Set (SchemeWeilDivisor X)) (hS : ∀ D ∈ S, 0 ≤ D) : X.IdealSheafData :=
  ⨆ D : S, D.val.idealSheaf (hS D D.property)

/-- The base ideal lies in an ideal exactly when each member's ideal lies in it. -/
theorem baseIdeal_le_iff {I : X.IdealSheafData} :
    baseIdeal S hS ≤ I ↔ ∀ D (hD : D ∈ S), D.idealSheaf (hS D hD) ≤ I := by
  rw [baseIdeal, iSup_le_iff, Subtype.forall]

/-- The base locus consists of the points on every divisor in the system. -/
@[simp]
theorem mem_support_baseIdeal_iff {x : X} :
    x ∈ (baseIdeal S hS).support ↔ ∀ D (hD : D ∈ S), x ∈ (D.idealSheaf (hS D hD)).support := by
  rw [baseIdeal, Scheme.IdealSheafData.support_iSup, Closeds.mem_iInf, Subtype.forall]

/-- At a prime divisor, the base locus detects common support of the family. -/
theorem notMem_support_baseIdeal_iff {x : CodimensionOnePoint X} :
    (x : X) ∉ (baseIdeal S hS).support ↔ ∃ D ∈ S, D x = 0 := by
  classical
  rw [mem_support_baseIdeal_iff hS]
  push Not
  constructor
  · rintro ⟨D, hD, hx⟩
    exact ⟨D, hD, (D.coeff_eq_zero_iff_notMem_support (hS D hD) x).mpr hx⟩
  · rintro ⟨D, hD, hx⟩
    exact ⟨D, hD, (D.coeff_eq_zero_iff_notMem_support (hS D hD) x).mp hx⟩

/-- The order of the base ideal is the infimum of the orders of the members' ideals. -/
theorem stalkOrder_baseIdeal (x : X) :
    (baseIdeal S hS).stalkOrder x = ⨅ D : S, (D.val.idealSheaf (hS D D.property)).stalkOrder x :=
  Scheme.IdealSheafData.stalkOrder_iSup _ x

/-- Some member of a nonempty system attains the order of the base ideal at the given point. -/
theorem exists_stalkOrder_eq_baseIdeal (hne : S.Nonempty) (x : X) :
    ∃ D : S, (D.val.idealSheaf (hS D D.property)).stalkOrder x = (baseIdeal S hS).stalkOrder x := by
  rw [stalkOrder_baseIdeal]
  have : Nonempty S := hne.to_subtype
  exact ENat.exists_eq_iInf _

/-- Every base-point multiplicity of a nonempty system is finite. -/
theorem stalkOrder_baseIdeal_lt_top (hne : S.Nonempty) (x : X) :
    (baseIdeal S hS).stalkOrder x < ⊤ := by
  obtain ⟨D, hD⟩ := exists_stalkOrder_eq_baseIdeal hS hne x
  rw [← hD, Scheme.IdealSheafData.stalkOrder_def, lt_top_iff_ne_top]
  exact mt (Ideal.localOrder_eq_top_iff_eq_bot _).mp
    ((D.val.isEffectiveCartier_idealSheaf (hS D D.property)).stalkIdeal_ne_bot x)

/-- The base ideal of a system is the product of the fixed divisor ideal and the base ideal
of its moving part. -/
theorem baseIdeal_eq_mul_movingPart (hne : S.Nonempty) :
    baseIdeal S hS =
      idealSheaf (WeilDivisor.fixedPart S hne hS) (WeilDivisor.fixedPart_nonneg hne hS) *
        baseIdeal (WeilDivisor.movingPart S hne hS) (fun _ ↦
          WeilDivisor.nonneg_of_mem_movingPart hne hS) := by
  let F : SchemeWeilDivisor X := WeilDivisor.fixedPart S hne hS
  let M : Set (SchemeWeilDivisor X) := WeilDivisor.movingPart S hne hS
  let hF : 0 ≤ F := WeilDivisor.fixedPart_nonneg hne hS
  let hM : ∀ E ∈ M, 0 ≤ E := fun _ ↦ WeilDivisor.nonneg_of_mem_movingPart hne hS
  have hmem {E : SchemeWeilDivisor X} : E ∈ M ↔ E + F ∈ S :=
    WeilDivisor.mem_movingPart_iff hne hS
  have hprod {E : SchemeWeilDivisor X} (hE : E ∈ M) :
      E.idealSheaf (hM E hE) * F.idealSheaf hF = (E + F).idealSheaf (hS _ (hmem.mp hE)) :=
    (idealSheaf_add E F (hM E hE) hF).symm
  apply eq_of_forall_ge_iff
  intro I
  rw [mul_comm, ← Scheme.IdealSheafData.le_colon_iff, baseIdeal_le_iff, baseIdeal_le_iff]
  simp only [Scheme.IdealSheafData.le_colon_iff]
  constructor
  · intro h E hE
    exact (hprod hE).trans_le (h _ (hmem.mp hE))
  · intro h D hD
    let E : SchemeWeilDivisor X := D - F
    have hEF : E + F = D := sub_add_cancel D F
    have hE : E ∈ M := hmem.mpr (hEF.symm ▸ hD)
    have hle := (hprod hE).symm.trans_le (h E hE)
    -- The proof of effectivity is dependent on the divisor being translated.
    have translate (A : SchemeWeilDivisor X) (hA : 0 ≤ A) (hEq : A = E + F) :
        A.idealSheaf hA ≤ I := by
      subst A
      exact hle
    exact translate D (hS D hD) hEF.symm

/-- The base locus of the moving system avoids all codimension-one points. -/
theorem notMem_support_baseIdeal_movingPart (hne : S.Nonempty) (x : CodimensionOnePoint X) :
    (x : X) ∉ (baseIdeal (WeilDivisor.movingPart S hne hS)
      (fun _ ↦ WeilDivisor.nonneg_of_mem_movingPart hne hS)).support :=
  (notMem_support_baseIdeal_iff _).mpr (WeilDivisor.exists_mem_movingPart_apply_eq_zero hne hS x)

/-- In dimension at most two, the moving base locus consists of closed points. -/
theorem support_baseIdeal_movingPart_subset_closedPoints (hne : S.Nonempty)
    (hX : topologicalKrullDim X ≤ 2) :
    ↑(baseIdeal (WeilDivisor.movingPart S hne hS)
      (fun _ ↦ WeilDivisor.nonneg_of_mem_movingPart hne hS)).support ⊆ closedPoints X := by
  intro x hx
  have hdim (y : X) : coheight y ≤ 2 :=
    WithBot.coe_le_coe.mp ((TauCeti.coheight_le_topologicalKrullDim y).trans hX)
  obtain ⟨D, hD⟩ := WeilDivisor.movingPart_nonempty hne hS
  have hxD := (mem_support_baseIdeal_iff _).mp hx D hD
  have hCard := isEffectiveCartier_idealSheaf D (WeilDivisor.nonneg_of_mem_movingPart hne hS hD)
  have hxgen : x ≠ genericPoint X := fun h ↦ hCard.genericPoint_notMem_support (h ▸ hxD)
  have hne₁ : coheight x ≠ 1 := fun h ↦ notMem_support_baseIdeal_movingPart hS hne ⟨x, h⟩ hx
  have hge₁ : 1 ≤ coheight x :=
    Order.one_le_iff_pos.mpr (coheight_pos.mpr (hxgen ∘ Scheme.eq_genericPoint_of_isMax))
  have hge₂ : 2 ≤ coheight x :=
    (ENat.add_one_le_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mpr (lt_of_le_of_ne hge₁ (Ne.symm hne₁))
  rw [mem_closedPoints_iff, ← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm (fun y hy ↦ ?_) subset_closure
  have hsp := specializes_iff_mem_closure.mpr hy
  rcases eq_or_ne y x with rfl | hne
  · exact Set.mem_singleton _
  have hyx : y < x :=
    lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp) fun h ↦
      hne ((Scheme.le_iff_specializes.mp h).antisymm hsp).eq
  have hxfin : coheight x < ⊤ := (hdim x).trans_lt (ENat.natCast_lt_top 2)
  exact ((hge₂.trans_lt (coheight_strictAnti hyx hxfin)).not_ge (hdim y)).elim

/-- On a locally factorial Noetherian integral surface the moving base locus is finite. -/
theorem finite_support_baseIdeal_movingPart (hne : S.Nonempty) (hX : topologicalKrullDim X ≤ 2) :
    (↑(baseIdeal (WeilDivisor.movingPart S hne hS)
      (fun _ ↦ WeilDivisor.nonneg_of_mem_movingPart hne hS)).support : Set X).Finite := by
  let B : Closeds X := (baseIdeal (WeilDivisor.movingPart S hne hS)
    (fun _ ↦ WeilDivisor.nonneg_of_mem_movingPart hne hS)).support
  have hB := support_baseIdeal_movingPart_subset_closedPoints hS hne hX
  obtain ⟨C, hCf, hCclosed, hCirred, hcover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible B.isClosed
  rw [hcover]
  refine hCf.sUnion fun V hV ↦ ?_
  obtain ⟨x, hx⟩ := QuasiSober.sober (hCirred V hV) (hCclosed V hV)
  have hxB : x ∈ (B : Set X) := hcover ▸ Set.mem_sUnion_of_mem hx.mem hV
  rw [← hx, (hB hxB).closure_eq]
  exact Set.finite_singleton _

attribute [local instance] IsNormalScheme.of_uniqueFactorizationMonoid_stalk

/-- For a family cut out by nonzero sections, the base ideal is the sum of their actual
zero ideals. In particular the family may consist of all nonzero sections of a subsystem. -/
theorem baseIdeal_range_toWeilDivisor_zeroDivisor (L : InvertibleSheaf X) {ι : Type*}
    (s : ι → Γ(L.obj, ⊤)) (hs : ∀ i, s i ≠ 0) :
    baseIdeal (Set.range fun i ↦ (L.zeroDivisor (hs i)).toWeilDivisor)
      (fun _ ⟨i, hi⟩ ↦ hi ▸
        (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
          (L.isEffective_zeroDivisor (hs i))) = ⨆ i, L.zeroIdeal (s i) := by
  have hzero (i : ι) :
      idealSheaf (L.zeroDivisor (hs i)).toWeilDivisor
        ((Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
          (L.isEffective_zeroDivisor (hs i))) = L.zeroIdeal (s i) :=
    (idealSheaf_toWeilDivisor (L.isEffective_zeroDivisor (hs i))).trans
      (L.idealSheaf_zeroDivisor (hs i))
  apply eq_of_forall_ge_iff
  intro I
  rw [baseIdeal_le_iff, iSup_le_iff]
  constructor
  · intro h i
    exact (hzero i).symm.trans_le (h _ (Set.mem_range_self i))
  · rintro h D ⟨i, rfl⟩
    exact (hzero i).trans_le (h i)

end

end TauCeti.AlgebraicGeometry.SchemeWeilDivisor

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.CartierDivisor.Support
public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf
import QPainleve.AlgebraicGeometry.Blowup.Point.Multiplicity
import QPainleve.AlgebraicGeometry.CartierDivisor.Multiplicity
import QPainleve.AlgebraicGeometry.Curves.Node.ComponentOrder
import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Total boundary weights at a nodal blowup

The exceptional weight in the total transform is the sum of the two incident
branch weights. At a self-node, both branches contribute the weight of the
same prime. The weights on the strict transforms are inherited from the base.
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

universe u v

namespace AlgebraicGeometry.Scheme.NodalCycleNumbering

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {B : X.IdealSheafData} [PrestableFamily (B.subscheme ↘ Spec (.of k))]
  {ι : Type v} {p : ι → (B.subscheme ↘ Spec (.of k)).smoothLocus} {n : ℕ} [NeZero n]

local notation "s" => (X ↘ Spec (CommRingCat.of k))
local notation "prime(" A "," h "," l ")" =>
  (B.boundaryPrimeEmbedding (NodalCycleNumbering.boundaryPrimeEquiv A h l))

/-- Blowing up a node of a numbered cycle adds an exceptional component whose Weil
multiplicity is the sum of the two branch multiplicities of the original divisor.
The support of that divisor is the numbered cycle, with arbitrary multiplicities. -/
theorem coeff_toWeilDivisor_comap_pointBlowup_of_over_node [IsNoetherian X]
    (A : NodalCycleNumbering p n) (hB : B.IsEffectiveCartier)
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier) (hsupport : D.support = B.support)
    (j : ZMod n) {I : X.IdealSheafData}
    (hI : I = (X.fromSpecResidueField (A.ambientNode j)).ker)
    [IsIntegral I.blowup] [IsNoetherian I.blowup] [IsDominant I.blowupToBase]
    (q : CodimensionOnePoint I.blowup)
    [IsDiscreteValuationRing (I.blowup.presheaf.stalk (q : I.blowup))]
    (hq : I.blowupToBase q = A.ambientNode j) :
    let hT := hD.comap_of_isDominant I.blowupToBase
    WeilDivisor.coeff hT.toCartierDivisor.toWeilDivisor q =
      WeilDivisor.coeff hD.toCartierDivisor.toWeilDivisor prime(A,hB,j) +
        WeilDivisor.coeff hD.toCartierDivisor.toWeilDivisor prime(A,hB,j + 1) := by
  classical
  dsimp only
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 _
  let := Scheme.Hom.uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two s
  let e : ZMod n ↪ CodimensionOnePoint X :=
    (A.boundaryPrimeEquiv hB).toEmbedding.trans B.boundaryPrimeEmbedding
  have hsupport' : hD.toCartierDivisor.toWeilDivisor.support ⊆ Finset.univ.map e := by
    intro x hx
    have hxB := (not_congr (hD.coeff_toWeilDivisor_eq_zero_iff x)).mp
      (Finsupp.mem_support_iff.mp hx)
    obtain ⟨a, rfl⟩ := B.range_boundaryPrimeEmbedding.ge
      (hsupport ▸ (not_not.mp hxB : (x : X) ∈ D.support))
    exact Finset.mem_map.mpr ⟨(A.boundaryPrimeEquiv hB).symm a, Finset.mem_univ _, by simp [e]⟩
  let x := A.ambientNode j
  let : IsRegularLocalRing (X.presheaf.stalk x) := isRegularLocalRing_stalk_of_smooth s x
  have hx := A.isClosed_ambientNode j
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq s 2).mp inferInstance).2 x hx
  have hcoeff (l : ZMod n) :
      let hP := (isEffectiveCartier_vanishingIdeal_closure_singleton
        (e l).property).comap_of_isDominant I.blowupToBase
      WeilDivisor.coeff hP.toCartierDivisor.toWeilDivisor q =
        (if l = j then 1 else 0) + (if l = j + 1 then 1 else 0) := by
    intro hP
    rw [IsEffectiveCartier.coeff_toWeilDivisor_comap_pointBlowup_of_over_center
      (isEffectiveCartier_vanishingIdeal_closure_singleton (e l).property)
      hx hdim hI hP q hq]
    simp only [e, Function.Embedding.trans_apply, Equiv.toEmbedding_apply]
    rw [A.stalkOrder_prime_eq_branch_count hB j l, ENat.toNat_natCast]
    split_ifs <;> norm_num
  rw [hD.coeff_toWeilDivisor_comap_eq_sum _ hsupport', Finset.sum_map]
  simp only [hcoeff, mul_add, Finset.sum_add_distrib,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

end AlgebraicGeometry.Scheme.NodalCycleNumbering

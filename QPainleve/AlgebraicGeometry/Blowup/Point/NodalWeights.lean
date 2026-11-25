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
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
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
local notation "ideal(" q ")" => vanishingIdeal (Closeds.mk (closure {(q : X)}) isClosed_closure)

private theorem stalkOrder_prime_eq_branch_count [IsLocallyNoetherian X]
    (A : NodalCycleNumbering p n) (hB : B.IsEffectiveCartier) (j l : ZMod n) :
    (ideal(prime(A,hB,l))).stalkOrder (A.ambientNode j) =
      (((if l = j then 1 else 0) + (if l = j + 1 then 1 else 0) : ℕ) : ℕ∞) := by
  classical
  let e := B.boundaryPrimeEmbedding ∘ A.boundaryPrimeEquiv hB
  have hinj : Function.Injective e :=
    B.boundaryPrimeEmbedding.injective.comp (A.boundaryPrimeEquiv hB).injective
  have hmem (a : ZMod n) : A.ambientNode j ∈ closure {(e a : X)} ↔ a = j ∨ a = j + 1 := by
    simpa [e, Fin.exists_fin_two, eq_comm] using A.ambientNode_mem_closure_boundaryPrime_iff hB j a
  have hsupp (q : CodimensionOnePoint X) : (q : X) ∈ B.support ↔ q ∈ Set.range e := by
    rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ, range_boundaryPrimeEmbedding]
    exact Iff.rfl
  have hother :
      (∃ q : CodimensionOnePoint X, q ≠ e l ∧ (q : X) ∈ B.support ∧
        A.ambientNode j ∈ closure {(q : X)}) ↔ l ≠ j ∨ l ≠ j + 1 := by
    constructor
    · rintro ⟨q, hq, hBq, hjq⟩
      obtain ⟨a, rfl⟩ := (hsupp q).mp hBq
      rcases (hmem a).mp hjq with rfl | rfl
      · exact Or.inl (ne_of_apply_ne e hq).symm
      · exact Or.inr (ne_of_apply_ne e hq).symm
    · intro h
      rcases h with h | h
      · exact ⟨e j, hinj.ne h.symm, (hsupp _).mpr (Set.mem_range_self j), (hmem j).mpr (Or.inl rfl)⟩
      · exact ⟨e (j + 1), hinj.ne h.symm, (hsupp _).mpr (Set.mem_range_self (j + 1)),
          (hmem _).mpr (Or.inr rfl)⟩
  have hN : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ s) := by
    rw [← B.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  calc
    _ = if A.ambientNode j ∈ closure {(e l : X)} then
        if ∃ q : CodimensionOnePoint X, q ≠ e l ∧ (q : X) ∈ B.support ∧
            A.ambientNode j ∈ closure {(q : X)} then 1 else 2 else 0 :=
      hB.stalkOrder_prime_eq_of_node hN
        (A.isNodeOfReducedBoundary_ambientNode j B.over_eq_subschemeι_comp)
        (e l) ((hsupp _).mpr (Set.mem_range_self l))
    _ = _ := by
      rw [hmem l, hother]
      split_ifs <;> norm_num <;> grind

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

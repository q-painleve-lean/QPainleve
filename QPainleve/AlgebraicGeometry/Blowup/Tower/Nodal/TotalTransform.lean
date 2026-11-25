/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.AlgebraicGeometry.CartierDivisor.Support
public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
import QPainleve.AlgebraicGeometry.Blowup.Point.BoundaryPrimes
import QPainleve.AlgebraicGeometry.Blowup.Point.Multiplicity
import QPainleve.AlgebraicGeometry.Blowup.Point.NodalWeights
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Subdivision
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

/-!
# Integer weights of total boundary transforms

In a tower of blowups at nodes of a reduced Cartier cycle, give every original
component weight one. At each blowup retain the weights on the strict transforms
and append the sum of the two branch weights. The resulting integer table gives
the Weil coefficients of the total transform, including all exceptional primes.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u v

namespace QPainleve.BlowupTower

/-- Data for computing the full boundary weights along a sequence of nodal blowups.
The two entries at a step index the branches' components among the current labels.
They can coincide at a self-node. -/
inductive BoundaryWeightRecurrence (n : ℕ) : ℕ → Type
  /-- Start with the original components. -/
  | nil : BoundaryWeightRecurrence n 0
  /-- Append the new component after the existing component labels. -/
  | snoc {m : ℕ} (r : BoundaryWeightRecurrence n m) (a b : Fin (n + m)) :
      BoundaryWeightRecurrence n (m + 1)

namespace BoundaryWeightRecurrence

/-- Compute the weights from the two component labels at each step. -/
def weights {n : ℕ} : {m : ℕ} → BoundaryWeightRecurrence n m → Fin (n + m) → ℕ
  | _, .nil => fun _ ↦ 1
  | _, .snoc r a b => Fin.snoc r.weights (r.weights a + r.weights b)

/-- Every original component starts with coefficient one. -/
@[simp]
theorem weights_nil {n : ℕ} (i : Fin n) :
    (nil : BoundaryWeightRecurrence n 0).weights i = 1 := (rfl)

/-- A blowup leaves the weights at all previous labels unchanged. -/
@[simp]
theorem weights_snoc_castSucc {n m : ℕ} (r : BoundaryWeightRecurrence n m)
    (a b i : Fin (n + m)) : (r.snoc a b).weights i.castSucc = r.weights i := by
  rw [weights, Fin.snoc_castSucc]

/-- The new exceptional label has the sum of the two incident weights. -/
@[simp]
theorem weights_snoc_last {n m : ℕ} (r : BoundaryWeightRecurrence n m)
    (a b : Fin (n + m)) :
    (r.snoc a b).weights (Fin.last (n + m)) = r.weights a + r.weights b := by
  rw [weights]
  exact Fin.snoc_last _ _

/-- A recurrence matches a tower from the given original labels if each step retains the
labels on the strict transforms and appends the exceptional prime over the center. The two
summand labels are exactly the components through the center, and coincide at a self-node. -/
def MatchesTower {X : Scheme.{u}} (D : X.IdealSheafData) {n : ℕ} (original : Fin n → X) :
    {m : ℕ} → {Y : Scheme.{u}} → BoundaryWeightRecurrence n m → (T : BlowupTower X m Y) →
      (Fin (n + m) ≃ (D.comap T.toBase).boundaryPrimes) → Prop
  | _, _, .nil, .nil, e => ∀ i, (e i).val = original i
  | _, _, .snoc (m := m) r a b, .snoc (Y := Z) T I, e' =>
    ∃ (e : Fin (n + m) ≃ (D.comap T.toBase).boundaryPrimes) (x : Z),
      MatchesTower D original r T e ∧ IsClosed ({x} : Set Z) ∧ I = (Z.fromSpecResidueField x).ker ∧
      (∀ i, I.blowupToBase (e' i.castSucc).val = (e i).val) ∧
      I.blowupToBase (e' (Fin.last (n + m))).val = x ∧
      ∀ i, x ∈ closure {(e i).val} ↔ i = a ∨ i = b

namespace MatchesTower

variable {X Z : Scheme.{u}} {D : X.IdealSheafData} {n m : ℕ} {original : Fin n → X}

/-- The empty tower uses the given original labels. -/
theorem nil_iff {e : Fin n ≃ (D.comap (BlowupTower.nil (X := X)).toBase).boundaryPrimes} :
    (nil : BoundaryWeightRecurrence n 0).MatchesTower D original .nil e ↔
      ∀ i, (e i).val = original i := (Iff.rfl)

/-- At a blowup, the prefix labels lift by strict transform, the last label lies
over the center, and the two summand labels account for its incident components. -/
theorem snoc_iff {T : BlowupTower X m Z} {I : Z.IdealSheafData} {r : BoundaryWeightRecurrence n m}
    {a b : Fin (n + m)} {e' : Fin (n + (m + 1)) ≃ (D.comap (T.snoc I).toBase).boundaryPrimes} :
    (r.snoc a b).MatchesTower D original (T.snoc I) e' ↔
      ∃ (e : Fin (n + m) ≃ (D.comap T.toBase).boundaryPrimes) (x : Z),
        r.MatchesTower D original T e ∧ IsClosed ({x} : Set Z) ∧
        I = (Z.fromSpecResidueField x).ker ∧
        (∀ i, I.blowupToBase (e' i.castSucc).val = (e i).val) ∧
        I.blowupToBase (e' (Fin.last (n + m))).val = x ∧
        ∀ i, x ∈ closure {(e i).val} ↔ i = a ∨ i = b := (Iff.rfl)

end MatchesTower

end BoundaryWeightRecurrence

namespace IsNodalBoundaryTower

variable {k : Type u} [Field k] [IsSepClosed k] [PerfectField k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [IsIntegral X] [IsNoetherian X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ Spec (.of k))]
  {n m : ℕ} [NeZero n] {T : BlowupTower X m Y}
  {ι : Type v} {p : ι → (D.subscheme ↘ Spec (.of k)).smoothLocus}

local notation "s" => (X ↘ Spec (CommRingCat.of k))
local notation "P[" T "]" => comap D (BlowupTower.toBase T)
local notation "B[" T "]" => radical (P[T])
local notation "weight(" h "," q ")" =>
  WeilDivisor.coeff (Scheme.CartierDivisor.toWeilDivisor (IsEffectiveCartier.toCartierDivisor h)) q
local notation "original(" A "," hD ")" =>
  (fun i ↦ Subtype.val (Scheme.NodalCycleNumbering.boundaryPrimeEquiv A hD (ZMod.finEquiv _ i)))

omit [IsSepClosed k] [PerfectField k] [NeZero n] in
private theorem exists_equiv_boundaryPrimes_snoc
    {Z : Scheme.{u}} [IsNoetherian Z] {f : Z ⟶ Spec (.of k)} [SmoothOfRelativeDimension 2 f]
    (P : Z.IdealSheafData) (x : Z) (hx : IsClosed ({x} : Set Z)) (hxP : x ∈ P.support)
    {I : Z.IdealSheafData} (hI : (Z.fromSpecResidueField x).ker = I)
    (e : Fin (n + m) ≃ P.boundaryPrimes) :
    ∃ e' : Fin (n + (m + 1)) ≃ (P.comap I.blowupToBase).boundaryPrimes,
      (∀ i, I.blowupToBase (e' i.castSucc).val = (e i).val) ∧
        I.blowupToBase (e' (Fin.last (n + m))).val = x := by
  subst I
  obtain ⟨b, hb, hb₀⟩ := P.exists_equiv_boundaryPrimes_comap_pointBlowup f hx hxP
  let e' := (finSumFinEquiv (m := n + m) (n := 1)).symm.trans
    ((Equiv.sumCongr e (Equiv.equivPUnit (Fin 1))).trans b)
  refine ⟨e', fun i ↦ ?_, ?_⟩
  · simpa only [e', Equiv.trans_apply, finSumFinEquiv_symm_apply_castSucc,
      Equiv.sumCongr_apply, Sum.map_inl] using hb (e i)
  · have hp : Equiv.equivPUnit (Fin 1) 0 = (PUnit.unit : PUnit.{u + 1}) :=
      Subsingleton.elim _ _
    simpa only [e', Equiv.trans_apply, finSumFinEquiv_symm_last, Equiv.sumCongr_apply,
      Sum.map_inr, hp] using hb₀

private abbrev HasBoundaryWeights (hD : D.IsEffectiveCartier)
    (A : Scheme.NodalCycleNumbering p n) (T : BlowupTower X m Y)
    [IsIntegral Y] [IsNoetherian Y] (hP : (P[T]).IsEffectiveCartier) : Prop :=
  ∃ (e : Fin (n + m) ≃ (P[T]).boundaryPrimes) (a : BoundaryWeightRecurrence n m),
    a.MatchesTower D original(A,hD) T e ∧
    (∀ i : Fin n, T.toBase (e (Fin.castAdd m i)).val = original(A,hD) i) ∧
    ∀ i, weight(hP,(P[T]).boundaryPrimeEmbedding (e i)) = a.weights i

omit [PerfectField k] in
private theorem hasBoundaryWeights_id (hD : D.IsEffectiveCartier)
    (A : Scheme.NodalCycleNumbering p n) :
    ∀ hP, HasBoundaryWeights hD A .nil hP := by
  suffices ∀ hP : (P[BlowupTower.nil]).IsEffectiveCartier,
      ∃ e : Fin n ≃ (P[BlowupTower.nil]).boundaryPrimes,
        (∀ i, (e i).val = original(A,hD) i) ∧
        ∀ i, weight(hP,(P[BlowupTower.nil]).boundaryPrimeEmbedding (e i)) =
          (BoundaryWeightRecurrence.nil : BoundaryWeightRecurrence n 0).weights i by
    intro hP
    obtain ⟨e, he, hw⟩ := this hP
    exact ⟨e, .nil, BoundaryWeightRecurrence.MatchesTower.nil_iff.mpr he,
      fun i ↦ by simpa using he i, hw⟩
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 _
  have : IsRegular X := IsRegular.of_smooth s
  have hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s) := by
    rw [← D.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have : IsReduced D.subscheme := hN.isReduced
  rw [toBase_nil, comap_id]
  intro hP
  refine ⟨(ZMod.finEquiv n).toEquiv.trans (A.boundaryPrimeEquiv hD), fun _ ↦ rfl, fun i ↦ ?_⟩
  let q := D.boundaryPrimeEmbedding (A.boundaryPrimeEquiv hD (ZMod.finEquiv n i))
  have : IsDiscreteValuationRing (X.presheaf.stalk (q : X)) :=
    IsNormalScheme.isDiscreteValuationRing_stalk q.val q.property
  rw [BoundaryWeightRecurrence.weights_nil, Nat.cast_one]
  exact hP.coeff_toWeilDivisor_eq_one_of_isReduced q (by
    simpa only [q, coe_boundaryPrimeEmbedding] using
      (mem_boundaryPrimes.mp (A.boundaryPrimeEquiv hD (ZMod.finEquiv n i)).property).1)

section Step

variable {Z : Scheme.{u}} [Z.Over (Spec (.of k))] [IsIntegral Z] [IsNoetherian Z]
  [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k))]
  {U : BlowupTower X m Z} {I : Z.IdealSheafData}
  [IsIntegral I.blowup] [IsNoetherian I.blowup] [IsNormalScheme I.blowup]
  [IsDominant I.blowupToBase]
  [PrestableFamily ((D.comap U.toBase).radical.subscheme ↘ Spec (.of k))]
  {ι' : Type v} {p' : ι' → ((D.comap U.toBase).radical.subscheme ↘ Spec (.of k)).smoothLocus}
  [NeZero (n + m)]

omit [PerfectField k] [X.Over (Spec (.of k))] [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] [PrestableFamily (D.subscheme ↘ Spec (.of k))]
  [NeZero n] in
private theorem exists_boundaryWeights_snoc_of_numbering
    (C : Scheme.NodalCycleNumbering p' (n + m)) (hB : (B[U]).IsEffectiveCartier) (j : ZMod (n + m))
    (hI : I = (Z.fromSpecResidueField (C.ambientNode j)).ker)
    (hP : (P[U]).IsEffectiveCartier) (e : Fin (n + m) ≃ (P[U]).boundaryPrimes)
    (r : BoundaryWeightRecurrence n m)
    (hr : ∀ i, weight(hP,(P[U]).boundaryPrimeEmbedding (e i)) = r.weights i) :
    ∃ (e' : Fin (n + (m + 1)) ≃ (P[U.snoc I]).boundaryPrimes) (a b : Fin (n + m)),
      (∀ i, I.blowupToBase (e' i.castSucc).val = (e i).val) ∧
      I.blowupToBase (e' (Fin.last (n + m))).val = C.ambientNode j ∧
      (∀ i, C.ambientNode j ∈ closure {(e i).val} ↔ i = a ∨ i = b) ∧
      ∀ (hPV : (P[U.snoc I]).IsEffectiveCartier) i,
        weight(hPV,(P[U.snoc I]).boundaryPrimeEmbedding (e' i)) = (r.snoc a b).weights i := by
  rw [toBase_snoc, comap_comp]
  let f := Z ↘ Spec (CommRingCat.of k)
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : IsRegular Z := IsRegular.of_smooth f
  have hx := C.isClosed_ambientNode j
  have hsupport : (P[U]).support = (B[U]).support := (support_radical _).symm
  have hxP : C.ambientNode j ∈ (P[U]).support := by
    rw [hsupport, C.ambientNode_def]
    exact (B[U]).range_subschemeι.le (Set.mem_range_self _)
  obtain ⟨e', he', he'₀⟩ :=
    exists_equiv_boundaryPrimes_snoc (f := f) (P[U]) _ hx hxP hI.symm e
  let b := Set.equivOfEq (boundaryPrimes_eq_of_support_eq hsupport)
  let l := (C.boundaryPrimeEquiv hB).trans (b.symm.trans e.symm)
  have hl (d : ZMod (n + m)) : (e (l d)).val = (C.boundaryPrimeEquiv hB d).val := by
    simp only [l, Equiv.trans_apply, Equiv.apply_symm_apply, b, Set.equivOfEq_symm_apply]
  refine ⟨e', l j, l (j + 1), he', he'₀, ?_, fun hPV ↦ ?_⟩
  · intro i
    obtain ⟨d, rfl⟩ := l.surjective i
    rw [hl, l.injective.eq_iff, l.injective.eq_iff]
    simpa [Fin.exists_fin_two, eq_comm] using C.ambientNode_mem_closure_boundaryPrime_iff hB j d
  · refine Fin.lastCases ?_ (fun i ↦ ?_)
    · -- Present the bound of the last index in the form used by the recurrence lemma.
      change _ = ((r.snoc (l j) (l (j + 1))).weights (Fin.last (n + m)) : ℤ)
      rw [BoundaryWeightRecurrence.weights_snoc_last r (l j) (l (j + 1)),
        Nat.cast_add, ← hr (l j), ← hr (l (j + 1))]
      have hl' (d : ZMod (n + m)) :
          (P[U]).boundaryPrimeEmbedding (e (l d)) =
            (B[U]).boundaryPrimeEmbedding (C.boundaryPrimeEquiv hB d) := by
        apply Subtype.ext
        simpa only [coe_boundaryPrimeEmbedding] using hl d
      rw [hl', hl']
      let q := ((P[U]).comap I.blowupToBase).boundaryPrimeEmbedding (e' (Fin.last (n + m)))
      have : IsDiscreteValuationRing (I.blowup.presheaf.stalk (q : I.blowup)) :=
        IsNormalScheme.isDiscreteValuationRing_stalk q.val q.property
      exact C.coeff_toWeilDivisor_comap_pointBlowup_of_over_node hB hP hsupport j hI q
        (by simpa only [q, coe_boundaryPrimeEmbedding] using he'₀)
    · rw [BoundaryWeightRecurrence.weights_snoc_castSucc, ← hr]
      have hx₂ := coheight_eq_of_isClosed_of_smoothOfRelativeDimension (n := 2) f hx
      exact hP.coeff_toWeilDivisor_comap_pointBlowup_of_strict hx (by rw [hx₂]; norm_num) hI hPV _ _
        (by simpa only [coe_boundaryPrimeEmbedding] using he' i)

end Step

private theorem hasBoundaryWeights_toBase
    (hT : IsNodalBoundaryTower D s (𝟙 X) T) (hD : D.IsEffectiveCartier)
    (A : Scheme.NodalCycleNumbering p n) :
    letI := hT.isClosedPointTower.isIntegral s
    letI := T.isNoetherian
    ∀ hP, HasBoundaryWeights hD A T hP := by
  have hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s) := by
    rw [← D.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  induction hT with
  | nil => exact hasBoundaryWeights_id hD A
  | @snoc m Z U I hU x hx hI hnode ih =>
    have hU : IsNodalBoundaryTower D s (𝟙 X) U := hU
    let f := U.toBase ≫ s
    let : Z.Over (Spec (.of k)) := ⟨f⟩
    have : SmoothOfRelativeDimension 2 f := hU.isClosedPointTower.smoothOfRelativeDimension s
    have : SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k)) :=
      hU.isClosedPointTower.smoothOfRelativeDimension s
    have : IsIntegral Z := hU.isClosedPointTower.isIntegral s
    have : IsNoetherian Z := U.isNoetherian
    let : PrestableFamily ((B[U]).subscheme ↘ Spec (.of k)) :=
      hU.prestableFamily_radical_comap_toBase hD
    let : NeZero (n + m) := ⟨by have := NeZero.ne n; omega⟩
    have hB := (hU.radical_comap_toBase hD hN).1
    obtain ⟨C, -, -⟩ := hU.exists_isOrientedCycleSubdivision_nodalBoundaryTower hD A
      (PEmpty.elim : PEmpty.{v + 1} → _)
    have hxB : (B[U]).IsNodeOfReducedBoundary f x := by
      simpa only [isNodeOfReducedBoundary_radical, Category.comp_id] using hnode
    obtain ⟨j, hj⟩ := C.exists_ambientNode_eq hxB (B[U]).over_eq_subschemeι_comp
    have hcenter : I = (Z.fromSpecResidueField (C.ambientNode j)).ker := by rw [hj, hI]
    let hP := hU.isClosedPointTower.isEffectiveCartier_totalTransform s hD
    have hstep : IsClosedPointTower Z ((BlowupTower.nil (X := Z)).snoc I) :=
      .snoc .nil x hx hI
    have : SmoothOfRelativeDimension 2 (I.blowupToBase ≫ f) := by
      simpa only [toBase_snoc, toBase_nil, Category.comp_id] using hstep.smoothOfRelativeDimension f
    have : Smooth (I.blowupToBase ≫ f) := SmoothOfRelativeDimension.smooth 2 _
    have : IsRegular I.blowup := IsRegular.of_smooth (I.blowupToBase ≫ f)
    have : IsIntegral I.blowup := hstep.isIntegral f
    have : IsNoetherian I.blowup := (U.snoc I).isNoetherian
    have : Surjective I.blowupToBase := by
      simpa only [toBase_snoc, toBase_nil, Category.comp_id] using hstep.surjective f
    obtain ⟨e, r, hmatch, he, hr⟩ := ih hP
    obtain ⟨e', a, b, he', hnew, hbranch, hw⟩ :=
      exists_boundaryWeights_snoc_of_numbering (U := U) (I := I) C hB j hcenter hP e r hr
    intro hPV
    refine ⟨e', r.snoc a b, BoundaryWeightRecurrence.MatchesTower.snoc_iff.mpr
      ⟨e, x, hmatch, hx, hI, he', hj ▸ hnew, hj ▸ hbranch⟩, ?_, hw hPV⟩
    intro i
    rw (occs := .pos [1]) [toBase_snoc]
    rw [Scheme.Hom.comp_apply, ← Fin.castSucc_castAdd, he', he]

/-- The total-transform Weil coefficients of a numbered nodal cycle are computed
by the integer recurrence that starts from ones and adds the two incident
weights at each successive blowup. The labels of the original components lift
their numbering. The recurrence matches the actual centers and branch components
at every stage, retaining strict-transform labels and appending each exceptional prime. -/
theorem exists_boundaryWeightRecurrence
    (hT : IsNodalBoundaryTower D s (𝟙 X) T) (hD : D.IsEffectiveCartier)
    (A : Scheme.NodalCycleNumbering p n) :
    letI := hT.isClosedPointTower.isIntegral s
    letI := T.isNoetherian
    let hP := hT.isClosedPointTower.isEffectiveCartier_totalTransform s hD
    ∃ (e : Fin (n + m) ≃ (P[T]).boundaryPrimes) (a : BoundaryWeightRecurrence n m),
      a.MatchesTower D original(A,hD) T e ∧
      (∀ i : Fin n, T.toBase (e (Fin.castAdd m i)).val = original(A,hD) i) ∧
      ∀ i, weight(hP,(P[T]).boundaryPrimeEmbedding (e i)) = a.weights i :=
  hasBoundaryWeights_toBase hT hD A _

end IsNodalBoundaryTower

end QPainleve.BlowupTower

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Boundary
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Isometry
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Subdivision
public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.Subdivision
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField

/-!
# Numbered Picard markings at paired nodal blowups

Blowups at the same numbered node on two surfaces insert their exceptional
components at the same position in the oriented cycles. A Picard isometry
matching the original numbered classes thus extends to an isometry matching the
new numbered classes. This is the corner blowup step of
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*, Theorem 4.7][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S4.Thmtheorem7
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

universe u v w v' w'

namespace QPainleve.BlowupTower

local notation "S(" k ")" => Spec (CommRingCat.of k)
local notation "g(" k ", " X ")" => (X ↘ S(k))
local notation "I(" x ")" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ x)
local notation "T(" x ")" => BlowupTower.nil.snoc (I(x))
local notation "π(" x ")" => blowupToBase (I(x))
local notation "R(" E ", " x ")" => radical (comap E (π(x)))
local notation "P(" E ", " a ")" => Additive.ofMul (primeDivisorClass
  (boundaryPrimeEmbedding E a))

/-- Blowing up a numbered node gives a one-step nodal boundary tower. -/
theorem isNodalBoundaryTower_numbered_node
    {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} [X.Over S(k)]
    {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S(k))]
    {n : ℕ} [NeZero n] {ι : Type v} {p : ι → (D.subscheme ↘ S(k)).smoothLocus}
    (A : Scheme.NodalCycleNumbering p n) (i : ZMod n) :
    IsNodalBoundaryTower D (g(k, X)) (𝟙 X) T(A.ambientNode i) := by
  refine .snoc .nil _ (A.isClosed_ambientNode i) rfl ?_
  simpa only [toBase_nil, comap_id, Category.comp_id, Category.id_comp] using
    A.isNodeOfReducedBoundary_ambientNode i rfl

variable {k : Type u} [Field k] [IsAlgClosed k] {X Z : Scheme.{u}}
  [X.Over S(k)] [Z.Over S(k)] [IsIntegral X] [IsIntegral Z]
  [X.IsProjectiveOver k] [Z.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (g(k, X))] [SmoothOfRelativeDimension 2 (g(k, Z))]
  {D : X.IdealSheafData} {F : Z.IdealSheafData}
  [PrestableFamily (D.subscheme ↘ S(k))] [PrestableFamily (F.subscheme ↘ S(k))]
  {n : ℕ} [NeZero n] {ι : Type v} {κ : Type w}
  {p : ι → (D.subscheme ↘ S(k)).smoothLocus} {q : κ → (F.subscheme ↘ S(k)).smoothLocus}

local notation "node(" A ", " i ")" => Scheme.NodalCycleNumbering.ambientNode A i
local notation "β(" E ", " x ")" =>
  subschemeMap (R(E, x)) E (π(x)) (le_map_iff_comap_le.mpr (le_radical _))

private theorem exists_numbering_pointBlowup (A : Scheme.NodalCycleNumbering p n)
    (hD : D.IsEffectiveCartier) (i : ZMod n) :
    let x := node(A, i)
    let : (I(x)).blowup.Over S(k) := ⟨π(x) ≫ g(k, X)⟩
    ∀ [PrestableFamily ((R(D, x)).subscheme ↘ S(k))]
      {ι' : Type v'} (p' : ι' → ((R(D, x)).subscheme ↘ S(k)).smoothLocus),
      ∃ A' : Scheme.NodalCycleNumbering p' (n + 1),
        (β(D, x)).IsOrientedCycleSubdivision A' A ∧
        ∀ a, (π(x)) ((R(D, x)).subschemeι (A'.componentGenericPoint a)) =
          if a.val < n then D.subschemeι (A.componentGenericPoint ((a.val : ZMod n) + (i + 1)))
          else x := by
  dsimp only
  rw [A.ambientNode_def, Scheme.ker_fromSpecResidueField_eq_vanishingIdeal]
  intro hpre ι' p'
  let C := Scheme.singularLocus k D.subscheme
  have hs : C.subschemeι (A.node i) ∈ C.support :=
    C.range_subschemeι.le ⟨_, rfl⟩
  have hc : IsClosed ({D.subschemeι (C.subschemeι (A.node i))} : Set X) :=
    A.ambientNode_def i ▸ A.isClosed_ambientNode i
  let J := vanishingIdeal
    (⟨closure ({D.subschemeι (C.subschemeι (A.node i))} : Set X), isClosed_closure⟩ : Closeds X)
  let : J.blowup.Over S(k) := ⟨J.blowupToBase ≫ g(k, X)⟩
  have : PrestableFamily ((D.comap J.blowupToBase).radical.subscheme ↘ S(k)) := hpre
  exact D.exists_isOrientedCycleSubdivision_nodalBlowup_at hc hs rfl rfl hD A i rfl p'

/-- An isometry matching the numbered boundary prime classes extends through blowups
at the corresponding numbered node. Both reduced total boundaries have oriented
subdivision numberings and the extended isometry matches every new numbered class.
The surface projections identify each strict transform and the exceptional
prime at the same index, including for self-nodes and two-component cycles. -/
theorem picardIsometryCongr_of_numbered_nodal_blowups
    (A : Scheme.NodalCycleNumbering p n) (B : Scheme.NodalCycleNumbering q n)
    (hD : D.IsEffectiveCartier) (hF : F.IsEffectiveCartier) (i : ZMod n)
    (e : (Chow.intersectionBilinForm k X).IsometryEquiv (Chow.intersectionBilinForm k Z)) :
    let : Smooth (g(k, X)) := SmoothOfRelativeDimension.smooth 2 _
    let : Smooth (g(k, Z)) := SmoothOfRelativeDimension.smooth 2 _
    let : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
    let : IsNoetherian Z := isNoetherian_of_finiteType (g(k, Z))
    let := (g(k, X)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let := (g(k, Z)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (∀ a, e P(D, A.boundaryPrimeEquiv hD a) = P(F, B.boundaryPrimeEquiv hF a)) →
    let x := node(A, i)
    let z := node(B, i)
    let hT : IsNodalBoundaryTower D (g(k, X)) (𝟙 X) T(x) :=
      isNodalBoundaryTower_numbered_node A i
    let hU : IsNodalBoundaryTower F (g(k, Z)) (𝟙 Z) T(z) :=
      isNodalBoundaryTower_numbered_node B i
    let : (I(x)).blowup.Over S(k) := ⟨π(x) ≫ g(k, X)⟩
    let : (I(z)).blowup.Over S(k) := ⟨π(z) ≫ g(k, Z)⟩
    let R := R(D, x)
    let W := R(F, z)
    let hπ : T(x).toBase = π(x) := by simp only [toBase_snoc, toBase_nil, Category.comp_id]
    let hτ : T(z).toBase = π(z) := by simp only [toBase_snoc, toBase_nil, Category.comp_id]
    let hnd : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ g(k, X)) :=
      PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := D.subscheme ↘ S(k))
    let hnf : AtWorstNodalOfRelativeDimensionOne (F.subschemeι ≫ g(k, Z)) :=
      PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := F.subscheme ↘ S(k))
    let hR : R.IsEffectiveCartier := by simpa only [hπ] using (hT.radical_comap_toBase hD hnd).1
    let hW : W.IsEffectiveCartier := by simpa only [hτ] using (hU.radical_comap_toBase hF hnf).1
    let hxOver : g(k, (I(x)).blowup) = π(x) ≫ g(k, X) := rfl
    let hzOver : g(k, (I(z)).blowup) = π(z) ≫ g(k, Z) := rfl
    let : PrestableFamily (R.subscheme ↘ S(k)) := by
      rw [R.over_eq_subschemeι_comp, hxOver]
      dsimp only [R]
      rw [← hπ]
      exact hT.prestableFamily_radical_comap_toBase hD
    let : PrestableFamily (W.subscheme ↘ S(k)) := by
      rw [W.over_eq_subschemeι_comp, hzOver]
      dsimp only [W]
      rw [← hτ]
      exact hU.prestableFamily_radical_comap_toBase hF
    let : IsNoetherian (I(x)).blowup := T(x).isNoetherian
    let : IsNoetherian (I(z)).blowup := T(z).isNoetherian
    let : IsIntegral (I(x)).blowup := hT.isClosedPointTower.isIntegral (g(k, X))
    let : IsIntegral (I(z)).blowup := hU.isClosedPointTower.isIntegral (g(k, Z))
    let : SmoothOfRelativeDimension 2 (g(k, (I(x)).blowup)) := by
      simpa only [hπ, hxOver] using hT.isClosedPointTower.smoothOfRelativeDimension (g(k, X))
    let : SmoothOfRelativeDimension 2 (g(k, (I(z)).blowup)) := by
      simpa only [hτ, hzOver] using hU.isClosedPointTower.smoothOfRelativeDimension (g(k, Z))
    let := (g(k, (I(x)).blowup)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let := (g(k, (I(z)).blowup)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    ∀ {ι' : Type v'} {κ' : Type w'}
      (p' : ι' → (R.subscheme ↘ S(k)).smoothLocus)
      (q' : κ' → (W.subscheme ↘ S(k)).smoothLocus),
      ∃ (A' : Scheme.NodalCycleNumbering p' (n + 1)) (B' : Scheme.NodalCycleNumbering q' (n + 1)),
        (β(D, x)).IsOrientedCycleSubdivision A' A ∧
        (β(F, z)).IsOrientedCycleSubdivision B' B ∧
        ∀ a : ZMod (n + 1),
          let j := (a.val : ZMod n) + (i + 1)
          (π(x)) (R.subschemeι (A'.componentGenericPoint a)) =
            (if a.val < n then D.subschemeι (A.componentGenericPoint j) else x) ∧
          (π(z)) (W.subschemeι (B'.componentGenericPoint a)) =
            (if a.val < n then F.subschemeι (B.componentGenericPoint j) else z) ∧
          picardIsometryCongr k hT.isClosedPointTower hU.isClosedPointTower e
          P(R, A'.boundaryPrimeEquiv hR a) = P(W, B'.boundaryPrimeEquiv hW a) := by
  intro _ _ _ _ _ _ he x z hT hU _ _ R W hπ hτ hnd hnf hR hW _ _ _ _ _ _ _ _ _ _ _ _ ι' κ' p' q'
  obtain ⟨A', hA', hA⟩ := exists_numbering_pointBlowup A hD i p'
  obtain ⟨B', hB', hB⟩ := exists_numbering_pointBlowup B hF i q'
  let σ := (A.boundaryPrimeEquiv hD).symm.trans (B.boundaryPrimeEquiv hF)
  have hσ (a : ZMod n) : σ (A.boundaryPrimeEquiv hD a) = B.boundaryPrimeEquiv hF a := by
    simp [σ]
  have hcenter (a : D.boundaryPrimes) : x ∈ closure {a.val} ↔ z ∈ closure {(σ a).val} := by
    obtain ⟨a, rfl⟩ := (A.boundaryPrimeEquiv hD).surjective a
    rw [hσ, A.ambientNode_mem_closure_boundaryPrime_iff hD,
      B.ambientNode_mem_closure_boundaryPrime_iff hF]
  have he' (a : D.boundaryPrimes) : e P(D, a) = P(F, σ a) := by
    obtain ⟨a, rfl⟩ := (A.boundaryPrimeEquiv hD).surjective a
    rw [hσ]
    exact he a
  refine ⟨A', B', hA', hB', fun a ↦ ⟨hA a, hB a, ?_⟩⟩
  apply picardIsometryCongr_nodal_boundaryPrimes_of_projection σ hcenter hD hF
    (A.isClosed_ambientNode i) (B.isClosed_ambientNode i)
    (A.isNodeOfReducedBoundary_ambientNode i rfl) (B.isNodeOfReducedBoundary_ambientNode i rfl)
    hnd hnf e he'
  simp only [Scheme.NodalCycleNumbering.boundaryPrimeEquiv_apply_val]
  by_cases ha : a.val < n
  · let j : ZMod n := (a.val : ZMod n) + (i + 1)
    refine Or.inr ⟨A.boundaryPrimeEquiv hD j, ?_, ?_⟩
    · simpa only [Scheme.NodalCycleNumbering.boundaryPrimeEquiv_apply_val, ha, ite_true]
        using hA a
    · simpa only [hσ, Scheme.NodalCycleNumbering.boundaryPrimeEquiv_apply_val, ha, ite_true]
        using hB a
  · exact Or.inl ⟨by simpa only [ha, ite_false] using hA a,
      by simpa only [ha, ite_false] using hB a⟩

end QPainleve.BlowupTower

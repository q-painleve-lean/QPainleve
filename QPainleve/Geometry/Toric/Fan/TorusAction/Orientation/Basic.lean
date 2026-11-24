/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.GenericPoint
public import QPainleve.AlgebraicGeometry.Curves.Node.Period.Orientation
public import QPainleve.Geometry.Toric.Fan.Boundary.Contraction
public import QPainleve.Geometry.Toric.Fan.TorusAction.Branches
public import QPainleve.Geometry.Toric.Fan.TorusAction.Comparison

import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

/-!
# Ordered boundary actions detected by fixed-center X evaluation

Equality of the rational evaluations at fixed centers detects a translating lift
when the charges have finite index. If the boundary projections are oriented
conductor subdivisions, the orientation of the translation descends to the two
contracted boundaries. Matching the ray of the initial component then identifies
the action on every numbered branch, including at a self-node.

The proof uses the subdivision and isomorphism formulas for the gluing period
of Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
[§2](https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup Multiplicative
open QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Scheme (NodalCycleNumbering)

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  {r : ℕ} (b : Module.Basis (Fin 2) ℤ N) (s : Fin r → Φ.Ray)
  (c d : Multiplicative (Fin r → ℤ) →* ℂˣ) (hΦ : Φ.IsRegular)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "center" a:arg => (fun j : Fin r ↦ a (ofAdd (Pi.single j 1)))
local notation "M" a:arg => internalBlowupTower b s (center a)
local notation "π" a:arg => toBase (WithBoundary.toTower (Sigma.snd (M a)))
local notation "ι" a:arg => WithBoundary.boundaryι (Sigma.snd (M a))
local notation "prime[" a "]" => internalBlowupBoundaryPrimeEquiv hΦ b s (center a)

/-- A lift of a torus translation that descends to the two surfaces induces
a commuting square on their specified boundary restrictions. -/
theorem commSq_boundaryTranslation_of_isLift
    {X Y U V : Scheme} {iU : U ⟶ X} {iV : V ⟶ Y} [Mono iV]
    {p : (M c).1 ⟶ X} {q : (M d).1 ⟶ Y}
    {f : (Φ.boundaryIdeal h₀).subscheme ⟶ U} {g : (Φ.boundaryIdeal h₀).subscheme ⟶ V}
    {e : X ⟶ Y} {eB : U ⟶ V}
    (hf : f ≫ iU = ι c ≫ p) (hg : g ≫ iV = ι d ≫ q)
    (heB : eB ≫ iV = iU ≫ e)
    {χ : Multiplicative (N →+ ℤ) →* ℂˣ} {t : (M c).1 ≅ (M d).1}
    (ht : IsLift (Φ.torusTranslation χ) (M c).2.toTower (M d).2.toTower t)
    (htq : p ≫ e = t.hom ≫ q) :
    CommSq (boundaryTranslation (Φ := Φ) χ).hom f g eB := by
  constructor
  apply (cancel_mono iV).mp
  simp only [Category.assoc, hg, heB, reassoc_of% hf]
  rw [← Category.assoc, ←
    boundaryι_comp_of_isLift_internalBlowupTower_torusTranslation b s (center c) (center d) χ ht,
    Category.assoc, htq]

variable {X Y : Scheme} [X.Over S] [Y.Over S] {D : X.IdealSheafData} {E : Y.IdealSheafData}
  {p : (internalBlowupTower b s (fun j : Fin r ↦ c (ofAdd (Pi.single j 1)))).1 ⟶ X}
  {q : (internalBlowupTower b s (fun j : Fin r ↦ d (ofAdd (Pi.single j 1)))).1 ⟶ Y}

variable [PrestableFamily ((Φ.boundaryIdeal h₀).subscheme ↘ S)]
  [PrestableFamily (D.subscheme ↘ S)] [PrestableFamily (E.subscheme ↘ S)]
  {n m : ℕ} [NeZero n] [NeZero m] {α β γ : Type*}
  {a₀ : α → (D.subscheme ↘ S).smoothLocus} {a₁ : β → (E.subscheme ↘ S).smoothLocus}
  {aT : γ → ((Φ.boundaryIdeal h₀).subscheme ↘ S).smoothLocus}
  (A : NodalCycleNumbering a₀ n) (B : NodalCycleNumbering a₁ n) (T : NodalCycleNumbering aT m)

variable {f : (Φ.boundaryIdeal h₀).subscheme ⟶ D.subscheme}
  {g : (Φ.boundaryIdeal h₀).subscheme ⟶ E.subscheme} [f.IsOver S] [g.IsOver S]
  (hf : f ≫ D.subschemeι =
    (internalBlowupTower b s (fun j : Fin r ↦ c (ofAdd (Pi.single j 1)))).2.boundaryι ≫ p)
  (hg : g ≫ E.subschemeι =
    (internalBlowupTower b s (fun j : Fin r ↦ d (ofAdd (Pi.single j 1)))).2.boundaryι ≫ q)
  (hfs : f.IsOrientedCycleSubdivision T A) (hgs : g.IsOrientedCycleSubdivision T B)
  {e : X ≅ Y} {eB : D.subscheme ≅ E.subscheme} [eB.hom.IsOver S]
  (heB : eB.hom ≫ E.subschemeι = D.subschemeι ≫ e.hom)

include hΦ hf hg hfs hgs heB in
/-- If an isomorphism of contractions lifts to a torus translation, its boundary
action preserves the orientation induced by the common numbered toric boundary. -/
theorem cycleOrientationSign_eq_one_of_isLift_torusTranslation
    (hc : Φ.IsComplete) {χ : Multiplicative (N →+ ℤ) →* ℂˣ} {t : (M c).1 ≅ (M d).1}
    (ht : IsLift (Φ.torusTranslation χ) ((M c).2.toTower) ((M d).2.toTower) t)
    (htq : p ≫ e.hom = t.hom ≫ q) :
    cycleOrientationSign (eB.boundaryCycleAction A B) = 1 := by
  let τ := boundaryTranslation (Φ := Φ) χ
  have hτ := commSq_boundaryTranslation_of_isLift b s c d hf hg heB ht htq
  have hsign := eB.cycleOrientationSign_eq_of_orientedCycleSubdivisions A B T T τ hfs hgs hτ
  rw [hsign, boundaryCycleAction_boundaryTranslation hΦ hc
    ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)), map_one]

include hΦ hf hg hfs hgs heB in
/-- A translating lift acts by rotation by `j` if a common ray maps to component
zero of the source and component `j` of the target under the boundary projections. -/
theorem boundaryCycleAction_of_translation_of_common_ray
    (hc : Φ.IsComplete) {χ : Multiplicative (N →+ ℤ) →* ℂˣ} {t : (M c).1 ≅ (M d).1}
    (ht : IsLift (Φ.torusTranslation χ) (M c).2.toTower (M d).2.toTower t)
    (htq : p ≫ e.hom = t.hom ≫ q) (j : ZMod n) (ρ : Φ.Ray)
    (hρ : p (prime[c] ρ).val = D.subschemeι (A.componentGenericPoint 0))
    (hρ' : q (prime[d] ρ).val = E.subschemeι (B.componentGenericPoint j)) :
    eB.boundaryCycleAction A B = DihedralGroup.r j := by
  have hsign := cycleOrientationSign_eq_one_of_isLift_torusTranslation b s c d hΦ A B T
    hf hg hfs hgs heB hc ht htq
  apply (DihedralGroup.eq_r_iff_cycleVertexPerm_zero_eq hsign).mpr
  apply (E.subschemeι.injective.comp B.componentGenericPoint_injective)
  have hpoint := congrArg (fun k : (M c).1 ⟶ Y ↦ k (prime[c] ρ).val) htq
  simp only [Function.comp_apply]
  rw [← eB.apply_componentGenericPoint, ← Scheme.Hom.comp_apply, heB, Scheme.Hom.comp_apply]
  simpa only [Scheme.Hom.comp_apply, hρ, hρ',
    apply_internalBlowupBoundaryPrimeEquiv_of_isLift_torusTranslation b s hΦ
      (center c) (center d) ht] using hpoint

variable [IsIntegral X] [IsIntegral Y] [IsNormalScheme X] [IsNormalScheme Y]
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsModification p] [IsModification q]

include hΦ hf hg hfs hgs heB in
/-- A translating lift acts by rotation by `j` exactly when component zero
of the source and component `j` of the target represent the same surviving ray. -/
theorem boundaryCycleAction_eq_r_iff_of_isLift_torusTranslation
    (hc : Φ.IsComplete) {χ : Multiplicative (N →+ ℤ) →* ℂˣ} {t : (M c).1 ≅ (M d).1}
    (ht : IsLift (Φ.torusTranslation χ) ((M c).2.toTower) ((M d).2.toTower) t)
    (htq : p ≫ e.hom = t.hom ≫ q)
    (hD : (D.comap p).support = (ι c).ker.support)
    (hE : (E.comap q).support = (ι d).ker.support)
    (j : ZMod n) (x : D.boundaryPrimes) (y : E.boundaryPrimes)
    (hx : x.val = D.subschemeι (A.componentGenericPoint 0))
    (hy : y.val = E.subschemeι (B.componentGenericPoint j)) :
    eB.boundaryCycleAction A B = DihedralGroup.r j ↔
      contractedBoundaryRayEmbedding hΦ b s (center c) p hD x =
        contractedBoundaryRayEmbedding hΦ b s (center d) q hE y := by
  have hsign := cycleOrientationSign_eq_one_of_isLift_torusTranslation b s c d hΦ A B T
    hf hg hfs hgs heB hc ht htq
  let a := eB.boundaryCycleAction A B
  have hxy : e.hom x.val = E.subschemeι (B.componentGenericPoint (cycleVertexPerm a 0)) := by
    rw [hx, ← Scheme.Hom.comp_apply, ← heB, Scheme.Hom.comp_apply,
      eB.apply_componentGenericPoint]
  have hvertex : e.hom x.val = y.val ↔ cycleVertexPerm a 0 = j := by
    rw [hxy, hy]
    exact (E.subschemeι.injective.comp B.componentGenericPoint_injective).eq_iff
  exact (eq_r_iff_cycleVertexPerm_zero_eq hsign).trans (hvertex.symm.trans
    (apply_contractedBoundaryPrime_eq_iff_of_isLift_torusTranslation b s hΦ
      (center c) (center d) p q e hD hE ht htq x y))

variable [IsSeparated (Y ↘ S)] [e.hom.IsOver S]

include hf hg hfs hgs heB in
/-- Equality of the rational X evaluations determines the entire boundary action.
The action is rotation by `j` exactly when component zero of the source and
component `j` of the target label the same surviving ray. The subdivisions use the
common toric orientation, and the charge index is finite. -/
theorem boundaryCycleAction_eq_r_iff_of_comp_contractedXEvaluation_eq
    (hc : Φ.IsComplete) (hindex : (rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    (hp : p ≫ (X ↘ S) = π c ≫ Φ.algebraicRealizationStructureMap)
    (hq : q ≫ (Y ↘ S) = π d ≫ Φ.algebraicRealizationStructureMap)
    (hD : (D.comap p).support = (ι c).ker.support)
    (hE : (E.comap q).support = (ι d).ker.support)
    (heval : e.hom.toRationalMap.comp (contractedXEvaluation b s d hΦ q) =
      contractedXEvaluation b s c hΦ p)
    (j : ZMod n) (x : D.boundaryPrimes) (y : E.boundaryPrimes)
    (hx : x.val = D.subschemeι (A.componentGenericPoint 0))
    (hy : y.val = E.subschemeι (B.componentGenericPoint j)) :
    eB.boundaryCycleAction A B = DihedralGroup.r j ↔
      contractedBoundaryRayEmbedding hΦ b s (center c) p hD x =
        contractedBoundaryRayEmbedding hΦ b s (center d) q hE y := by
  have : IsReduced D.subscheme :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := D.subscheme ↘ S)).isReduced
  have : IsReduced E.subscheme :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := E.subscheme ↘ S)).isReduced
  obtain ⟨χ, ⟨t, ht, htq, -, -⟩, -⟩ :=
    existsUnique_translation_of_comp_contractedXEvaluation_eq b s c d hΦ p q e
      hindex hp hq hD hE heval
  exact boundaryCycleAction_eq_r_iff_of_isLift_torusTranslation b s c d hΦ A B T
    hf hg hfs hgs heB hc ht htq hD hE j x y hx hy

end TauCeti.Toric.Fan

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Period.PairIso
public import QPainleve.Geometry.Toric.Fan.Picard.Period.Alignment
public import QPainleve.Geometry.Toric.Fan.TorusAction.Orientation.Basic

import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

/-!
# Reconstructing a marked pair isomorphism from periods

Once the two ordered models use the same fan and Picard coordinates, equal periods
align the internal centers. The translating lift descends when the projections
retain the same boundary rays. Its Picard pullback is determined by the full
markings, and its action on the ordered branches follows from the oriented
subdivisions and the surviving ray above component zero.

This is the reconstruction in a common presentation used in the proof of
[Gross, Hacking and Keel, Theorem 1.8](https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData
open Scheme (NodalCycleNumbering)

namespace TauCeti.Toric.Fan

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones] {r : ℕ}
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) (s : Fin r → Φ.Ray)
  (c d : Multiplicative (Fin r → ℤ) →* k₀ˣ)

local notation "S" => Spec (CommRingCat.of k₀)
local notation "Btor" => Scheme.IdealSheafData.subscheme (Φ.toricBoundaryIdeal k₀ h₀)
local notation "center" a:arg => (fun j : Fin r ↦ a (ofAdd (Pi.single j 1)))
local notation "M" a:arg => internalBlowupTower k₀ b s (center a)
local notation "π" a:arg => toBase (WithBoundary.toTower (Sigma.snd (M a)))
local notation "ι" a:arg => WithBoundary.boundaryι (Sigma.snd (M a))
local notation "mark" a:arg => internalBlowupPicardMarking k₀ b s (center a) hΦ
local notation "prime[" a "]" => internalBlowupBoundaryPrimeEquiv k₀ hΦ b s (center a)
local notation "base" => (Φ.finiteFanSchemeToSpec k₀)

variable {X Y W Z : Scheme} [X.Over (Spec (.of k₀))] [Y.Over (Spec (.of k₀))]
  {D : X.IdealSheafData} {E : Y.IdealSheafData}
  {l l' : ℕ} {T : BlowupTower X l W} {U : BlowupTower Y l' Z}
  (e : W ≅ (internalBlowupTower k₀ b s (fun j : Fin r ↦ c (ofAdd (Pi.single j 1)))).1)
  (e' : Z ≅ (internalBlowupTower k₀ b s (fun j : Fin r ↦ d (ofAdd (Pi.single j 1)))).1)

local notation "p" => (Iso.inv e ≫ toBase T)
local notation "q" => (Iso.inv e' ≫ toBase U)

variable [PrestableFamily ((Φ.toricBoundaryIdeal k₀ h₀).subscheme ↘ Spec (.of k₀))]
  [PrestableFamily (D.subscheme ↘ Spec (.of k₀))]
  [PrestableFamily (E.subscheme ↘ Spec (.of k₀))]
  {n m : ℕ} [NeZero n] [NeZero m] {α β γ : Type*}
  {a₀ : α → (D.subscheme ↘ Spec (.of k₀)).smoothLocus} {a₁ : β →
    (E.subscheme ↘ Spec (.of k₀)).smoothLocus}
  {aT : γ → ((Φ.toricBoundaryIdeal k₀ h₀).subscheme ↘ Spec (.of k₀)).smoothLocus}
  (A : NodalCycleNumbering a₀ n) (B : NodalCycleNumbering a₁ n) (C : NodalCycleNumbering aT m)

variable [IsIntegral X] [IsIntegral Y] [QuasiCompact (X ↘ Spec (.of k₀))] [QuasiCompact (Y ↘ Spec
  (.of k₀))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k₀))] [SmoothOfRelativeDimension 2 (Y ↘ Spec
    (.of k₀))]
  [(Φ.finiteFanScheme k₀).IsProjectiveOver k₀]
  [SmoothOfRelativeDimension 2 ((Φ.finiteFanScheme k₀) ↘ Spec (.of k₀))]
  [LinearMap.IsPerfPair
    ((Chow.intersectionBilinForm k₀ (Φ.finiteFanScheme k₀)).prod
      (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ))))]

/-- Equal ordered periods in a common toric presentation realize a prescribed Picard
pullback matching the full markings when the two nodal projections retain the same
boundary rays. The target numbering is aligned with the toric orientation according to the sign
of the prescribed dihedral action. The common lifted ray over component zero
determines its image. The action includes the ordered branches at self-nodes
and two-component cycles. -/
theorem exists_iso_of_eq_period_of_matching_picard_markings
    (hc : Φ.IsComplete) (u : ZMod m ≃ Φ.Ray)
    (hvertices : ∀ j, (Btor).dualGraphVertexEquiv aT (C.vertex j) =
      Φ.boundaryNormalizationComponentEquiv k₀ hΦ (u j))
    (hdet : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1)
    (hnodes : ∀ j, ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ ∧
      (Φ.toricBoundaryIdeal k₀ h₀).subschemeι ((Btor).dualGraphEdgeEquiv aT (C.edge j)).val =
        (Φ.distinguishedSection (R := k₀) σ) (IsLocalRing.closedPoint k₀))
    (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (hU : IsNodalBoundaryTower E (Y ↘ S) (𝟙 Y) U)
    (hp : p ≫ (X ↘ S) = π c ≫ base) (hq : q ≫ (Y ↘ S) = π d ≫ base)
    (hD : (D.comap p).support = (ι c).ker.support)
    (hE : (E.comap q).support = (ι d).ker.support)
    (hkeep : ∀ ρ : Φ.Ray, p (prime[c] ρ).val ∈ D.boundaryPrimes ↔
      q (prime[d] ρ).val ∈ E.boundaryPrimes)
    (hperiod : orderedBoundaryPeriod k₀ hΦ b s C (center c) =
      orderedBoundaryPeriod k₀ hΦ b s C (center d))
    (G : LineBundleClass Y → LineBundleClass X)
    (hPic : ∀ L : LineBundleClass Y, (mark c).symm (Additive.ofMul (pullback p (G L))) =
      (mark d).symm (Additive.ofMul (pullback q L)))
    {f : Btor ⟶ D.subscheme} {g : Btor ⟶ E.subscheme} [f.IsOver S] [g.IsOver S]
    (hf : f ≫ D.subschemeι = ι c ≫ p) (hg : g ≫ E.subschemeι = ι d ≫ q)
    (hfs : f.IsOrientedCycleSubdivision C A) (act : DihedralGroup n)
    (hgs : g.IsOrientedCycleSubdivision C
      (if DihedralGroup.cycleOrientationSign act = -1 then B.reverse else B))
    (ρ : Φ.Ray)
    (hρ : p (prime[c] ρ).val = D.subschemeι (A.componentGenericPoint 0))
    (hρ' : q (prime[d] ρ).val =
      E.subschemeι (B.componentGenericPoint (DihedralGroup.cycleVertexPerm act 0))) :
    Nonempty (SignedTorelliPairIso (D := D) (E := E) A B G act) := by
  have : IsReduced D.subscheme :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := D.subscheme ↘ S)).isReduced
  have : IsReduced E.subscheme :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := E.subscheme ↘ S)).isReduced
  obtain ⟨a, haOver, haD, ⟨t⟩⟩ :=
    exists_iso_of_eq_orderedBoundaryPeriod k₀ hΦ b s c d C u hvertices hdet hnodes
      hT hU e e' hp hq hD hE hkeep hperiod
  have haPic (L : LineBundleClass Y) : pullback a.hom L = G L := by
    have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
    apply hT.isClosedPointTower.injective_pullback_toBase (X ↘ S)
    apply (pullbackEquiv e.symm).injective
    apply Additive.ofMul.injective
    apply (mark c).symm.injective
    simpa only [pullbackEquiv_apply, Iso.symm_hom, pullback_comp, Category.assoc] using
      (t.pullback_marking k₀ hΦ L).trans (hPic L).symm
  obtain ⟨aB, haB⟩ := E.exists_iso_of_comap_eq_ker a D.subschemeι
    (haD.trans D.ker_subschemeι.symm)
  let : a.hom.IsOver S := ⟨haOver⟩
  let hover : aB.hom.IsOver S := ⟨by
    rw [E.over_eq_subschemeι_comp, reassoc_of% haB, haOver, D.over_eq_subschemeι_comp]⟩
  suffices hAction : aB.boundaryCycleAction A B = act from
    ⟨SignedTorelliPairIso.ofIsos a aB haB haPic hAction⟩
  cases act with
  | r j =>
    have hsign : (1 : ℤˣ) ≠ -1 := by decide
    simp only [DihedralGroup.cycleOrientationSign_r, ite_eq_right hsign] at hgs
    simp only [DihedralGroup.cycleVertexPerm_r_apply, zero_add] at hρ'
    exact boundaryCycleAction_of_translation_of_common_ray k₀ b s c d hΦ A B C
      hf hg hfs hgs haB hc t.isLift t.commutes j ρ hρ hρ'
  | sr j =>
    simp only [DihedralGroup.cycleOrientationSign_sr, ite_true] at hgs
    have hρ'' : q (prime[d] ρ).val = E.subschemeι (B.reverse.componentGenericPoint j) := by
      simpa only [DihedralGroup.cycleVertexPerm_sr_apply, sub_zero,
        NodalCycleNumbering.componentGenericPoint_def, NodalCycleNumbering.reverse_component]
        using hρ'
    have h := boundaryCycleAction_of_translation_of_common_ray k₀ b s c d hΦ A B.reverse C
      hf hg hfs hgs haB hc t.isLift t.commutes j ρ hρ hρ''
    have : (Iso.refl E.subscheme).hom.IsOver S := by
      rw [Iso.refl_hom]
      infer_instance
    have hm : DihedralGroup.r j = DihedralGroup.sr 0 * aB.boundaryCycleAction A B := by
      simpa only [Iso.trans_refl, Iso.boundaryCycleAction_refl_reverse, h] using
        Iso.boundaryCycleAction_trans aB A B (Iso.refl _) B.reverse
    simpa only [← mul_assoc, DihedralGroup.sr_mul_sr, sub_self, ← DihedralGroup.one_def,
      one_mul, DihedralGroup.sr_mul_r, zero_add] using
      congrArg (DihedralGroup.sr 0 * ·) hm.symm

end TauCeti.Toric.Fan

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Automorphism
public import QPainleve.Geometry.Toric.Fan.TorusAction.NodalDescent

import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Automorphism
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.BranchDescent
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Component
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import QPainleve.Geometry.Toric.Fan.Boundary.Prestable
import QPainleve.Geometry.Toric.Fan.TorusAction.Branches
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The Picard kernel of a nodal pair with a toric presentation

The quotient characters of an ordered toric presentation give exactly the
Picard-trivial automorphisms fixing all boundary components and nodal branches.
The specified nodal blowups relate the branch action on the ordered model to the
branch action on the original pair. This is the toric proof of [Gross, Hacking
and Keel, Proposition 2.6](https://arxiv.org/html/1211.6367v5#S2).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Multiplicative
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  {n : ℕ} (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ)
  (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)

local notation "M" => internalBlowupTower b s c
local notation "C" => Scheme.IdealSheafData.subscheme (Φ.boundaryIdeal h₀)
local notation "ι" => WithBoundary.boundaryι (Sigma.snd M)
local notation "base" => Spec (CommRingCat.of ℂ)
local notation "Chars" => (Multiplicative (N ⧸ LinearMap.range (rayChargeMap s)) →* ℂˣ)

variable {X Y : Scheme} {f : X ⟶ Spec (.of ℂ)} {D : X.IdealSheafData}
  {m : ℕ} {T : BlowupTower X m Y} (e : Y ≅ (internalBlowupTower b s c).1)
  (he : e.hom ≫ (internalBlowupTower b s c).2.toTower.toBase ≫
    Φ.algebraicRealizationStructureMap = T.toBase ≫ f)
  (hB : (D.comap T.toBase).support =
    ((internalBlowupTower b s c).2.boundaryι.ker.comap e.hom).support)

local notation "P" => radical (D.comap T.toBase)
local notation "toTop" => Aut.autMulEquivOfIso (Iso.symm e)

include hΦ hc he hB in
private theorem exists_totalBoundaryIso :
    ∃ q : (P).subscheme ≅ C,
      q.hom ≫ ι = (P).subschemeι ≫ e.hom ∧
      q.hom ≫ (C ↘ base) = (P).subschemeι ≫ T.toBase ≫ f := by
  have hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  have hnodal := Φ.atWorstNodalOfRelativeDimensionOne_boundary hΦ hc hdim
  have : IsReduced C := hnodal.isReduced
  let j := ι ≫ e.inv
  have hj : j.ker = (ι).ker.comap e.hom :=
    ker_eq_comap_of_isPullback ι (IsPullback.of_vert_isIso (snd := 𝟙 C) ⟨by simp [j]⟩)
  have hk : j.ker = (P).subschemeι.ker := by
    rw [j.ker_eq_vanishingIdeal_support, hj, ← hB, ker_subschemeι, vanishingIdeal_support]
  let q := IsClosedImmersion.lift j (P).subschemeι hk.le
  have : IsIso q := IsClosedImmersion.isIso_lift _ _ hk
  have hq : q ≫ ι = (P).subschemeι ≫ e.hom := by
    have hqj := IsClosedImmersion.lift_fac j (P).subschemeι hk.le
    simpa only [j, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (· ≫ e.hom) hqj
  refine ⟨asIso q, hq, ?_⟩
  simp only [asIso_hom]
  rw [over_eq_subschemeι_comp, Φ.algebraicRealization_over,
    ← WithBoundary.boundaryι_toBase_assoc (Sigma.snd M), reassoc_of% hq, he]

variable [IsIntegral X] [IsNoetherian X] [IsProper f] [SmoothOfRelativeDimension 2 f]
  (hCartier : D.IsEffectiveCartier)
  (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ f))
  (hT : IsNodalBoundaryTower D f (𝟙 X) T)

local notation "action" =>
  toricPresentationCharacterHom b s c hΦ f e hT.isClosedPointTower hc

include he hB hCartier hT in
private theorem toricPresentationCharacterHom_fixes_branches (z : Chars)
    (hover : (action z).asIso.hom ≫ f = f)
    (d : D.subscheme ≅ D.subscheme)
    (hd : d.hom ≫ D.subschemeι = D.subschemeι ≫ (action z).asIso.hom) :
    d.FixesNodalBranches _ hN (by rw [reassoc_of% hd, hover]) := by
  let : X.Over base := ⟨f⟩
  have : SmoothOfRelativeDimension 2 (X ↘ base) := ‹SmoothOfRelativeDimension 2 f›
  have : QuasiCompact (X ↘ base) := inferInstanceAs (QuasiCompact f)
  let u := internalBlowupPicardBoundaryAutMulEquiv b s c hΦ hc z
  let g := (toTop (u : Aut (M).1)).asIso
  have hg := toricPresentationCharacterHom_isLift b s c hΦ f e hT.isClosedPointTower hc z
  obtain ⟨r, hr⟩ := D.exists_radicalComapSubschemeIso T.toBase hd hg.hom_toBase
  obtain ⟨q, hq, hqOver⟩ := exists_totalBoundaryIso b s c hΦ hc e he hB
  have hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  have : IsProper T.toBase := T.isProper_toBase
  have : IsProper (q.hom ≫ (C ↘ base)) := hqOver ▸ inferInstanceAs
    (IsProper ((P).subschemeι ≫ T.toBase ≫ f))
  have : IsProper (C ↘ base) :=
    (MorphismProperty.cancel_left_of_respectsIso @IsProper q.hom _).mp inferInstance
  have hbase : C ↘ base = (Φ.boundaryIdeal h₀).subschemeι ≫ Φ.algebraicRealizationStructureMap :=
    (over_eq_subschemeι_comp _).trans (congrArg (_ ≫ ·) Φ.algebraicRealization_over)
  have : PrestableFamily (C ↘ base) := {
    toIsProper := inferInstance
    toGeometricallyConnected := hbase.symm ▸ Φ.geometricallyConnected_boundary hΦ hc hdim
    atWorstNodalOfRelativeDimensionOne :=
      hbase.symm ▸ Φ.atWorstNodalOfRelativeDimensionOne_boundary hΦ hc hdim }
  obtain ⟨a, ⟨haOver, ha, haBranch⟩, -⟩ :=
    existsUnique_boundaryIso_of_internalBlowupPicardBoundaryAut b s hΦ hc u
  have hge : g.hom ≫ e.hom = e.hom ≫ u.val.asIso.hom := by simp [g]
  have hcomm : r ≪≫ q = q ≪≫ a := by
    apply Iso.ext
    apply (cancel_mono ι).mp
    simp only [Iso.trans_hom, Category.assoc]
    rw [hq, reassoc_of% hr, hge, ← reassoc_of% hq, ha]
  have hNP := (hT.radical_comap_toBase (k := ℂ) hCartier hN).2
  have hrOver : r.hom ≫ (P).subschemeι ≫ T.toBase ≫ f = (P).subschemeι ≫ T.toBase ≫ f := by
    rw [reassoc_of% hr, hg.hom_toBase_assoc, hover]
  let ha' : a.hom ≫ (C ↘ base) = (C ↘ base) := haOver.comp_over
  have hab : a.FixesNodalBranches _ PrestableFamily.atWorstNodalOfRelativeDimensionOne ha' := by
    let : a.hom.IsOver base := haOver
    rw [Iso.fixesNodalBranches_iff_branchScheme]
    intro p
    exact congrArg (fun v : (C).branchScheme ℂ ≅ (C).branchScheme ℂ ↦ v.hom p) haBranch
  exact hT.fixes_nodal_branches_of_isLift (k := ℂ) hCartier hN hover hd hg hr
    ((Iso.fixesNodalBranches_iff_of_comm (hC := hNP) (ha := hrOver) q hqOver hcomm).mpr hab)

include he hB hCartier in
/-- The quotient-character action has image exactly the intrinsic Picard kernel fixing
the components and branches of the original boundary. -/
theorem toricPresentationCharacterHom_range_eq_picardNodalBoundaryAut :
    (toricPresentationCharacterHom b s c hΦ f e hT.isClosedPointTower hc).range =
      D.picardNodalBoundaryAut hN := by
  let : X.Over base := ⟨f⟩
  have : SmoothOfRelativeDimension 2 (X ↘ base) := ‹SmoothOfRelativeDimension 2 f›
  have : QuasiCompact (X ↘ base) := inferInstanceAs (QuasiCompact f)
  ext a
  rw [D.mem_picardNodalBoundaryAut]
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨hover, hPic, hfix, -⟩ :=
      (mem_range_toricPresentationCharacterHom_iff b s c hΦ f e he hB
        hT.isClosedPointTower hc _).mp ⟨z, rfl⟩
    have hred : IsReduced D.subscheme := hN.isReduced
    have hD := hCartier.comap_radical_eq_of_fixes_components _ hfix
    rw [D.isReduced_subscheme_iff_radical_eq.mp hred] at hD
    obtain ⟨d, hd⟩ := D.exists_iso_of_comap_eq_ker _ D.subschemeι
      (by simpa only [ker_subschemeι] using hD)
    exact ⟨hover, hPic, hfix, d, hd,
      toricPresentationCharacterHom_fixes_branches b s c hΦ hc e he hB hCartier hN hT z hover d hd⟩
  · rintro ⟨hover, hPic, hfix, d, hd, hb⟩
    have hlift := hT.exists_isLift_of_fixes_nodal_branches (k := ℂ) hCartier hN _ d hover hd
      ((d.fixesNodalBranches_iff _ hN _).mp hb)
    exact (mem_range_toricPresentationCharacterHom_iff b s c hΦ f e he hB
      hT.isClosedPointTower hc a).mpr ⟨hover, hPic, hfix, hlift.exists⟩

include he hB hCartier in
/-- The quotient characters are isomorphic to the Picard-trivial automorphism group
of the pair fixing each boundary component and branch. -/
def toricPresentationCharacterMulEquiv : Chars ≃* D.picardNodalBoundaryAut hN :=
  (MonoidHom.ofInjective
    (toricPresentationCharacterHom_injective b s c hΦ f e hT.isClosedPointTower hc)).trans
      (MulEquiv.subgroupCongr
        (toricPresentationCharacterHom_range_eq_picardNodalBoundaryAut
          b s c hΦ hc e he hB hCartier hN hT))

include he hB hCartier in
/-- The quotient-character equivalence acts by the descended torus translation. -/
@[simp]
theorem toricPresentationCharacterMulEquiv_apply (z : Chars) :
    (toricPresentationCharacterMulEquiv b s c hΦ hc e he hB hCartier hN hT z : Aut X) =
      toricPresentationCharacterHom b s c hΦ f e hT.isClosedPointTower hc z := by
  rw [toricPresentationCharacterMulEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply]

include hΦ hc he hB hCartier hT in
/-- For finite-index charges, the Picard kernel with fixed boundary components and
branches has order equal to the charge index. -/
theorem natCard_picardNodalBoundaryAut_of_toricPresentation
    [Finite (N ⧸ LinearMap.range (rayChargeMap s))] :
    Nat.card (D.picardNodalBoundaryAut hN) = (rayChargeMap s).range.toAddSubgroup.index := by
  rw [← Nat.card_congr
    (toricPresentationCharacterMulEquiv b s c hΦ hc e he hB hCartier hN hT).toEquiv]
  exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ ℂ

end TauCeti.Toric.Fan

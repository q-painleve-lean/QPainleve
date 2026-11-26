/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
public import QPainleve.Geometry.Toric.Fan.TorusAction.Alignment
public import QPainleve.Geometry.Toric.Fan.TorusAction.Orientation.Basic

import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Orientation
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.Geometry.Toric.Fan.TorusAction.ContractedEvaluation
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

/-!
# Comparing marked pullbacks of contracted X evaluation

At a fixed toric presentation, pullback of rational X evaluation depends only
on the Picard pullback and the action on the numbered boundary. The difference
between two isomorphisms with the same actions lies in the quotient-character
group of [Gross, Hacking and Keel, Proposition 2.6](
https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup Multiplicative QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData
open Scheme (NodalCycleNumbering)

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones] {r : ℕ}
  (b : Module.Basis (Fin 2) ℤ N) (s : Fin r → Φ.Ray) (hΦ : Φ.IsRegular)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "center" c:arg => (fun j : Fin r ↦ c (ofAdd (Pi.single j 1)))
local notation "M" c:arg => internalBlowupTower b s (center c)
local notation "π" c:arg => toBase (WithBoundary.toTower (Sigma.snd (M c)))
local notation "ι" c:arg => WithBoundary.boundaryι (Sigma.snd (M c))
local notation "mark" c:arg => internalBlowupPicardMarking b s (center c) hΦ
local notation "prime" c:arg => internalBlowupBoundaryPrimeEquiv hΦ b s (center c)
local notation "Dtor" => Φ.boundaryIdeal h₀

section SameCenter

variable (c : Multiplicative (Fin r → ℤ) →* ℂˣ)

variable {W X Y : Scheme} [W.Over S] [X.Over S] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ S)] [QuasiCompact (X ↘ S)]
  {D : X.IdealSheafData} {E : W.IdealSheafData}
  [PrestableFamily (D.subscheme ↘ S)] [PrestableFamily (E.subscheme ↘ S)]
  {n : ℕ} [NeZero n] {α β : Type*}
  {a : α → (D.subscheme ↘ S).smoothLocus} {d : β → (E.subscheme ↘ S).smoothLocus}

open Scheme.RationalMap in
/-- Two isomorphisms to the same contracted toric presentation give equal
pullbacks of X evaluation if they induce the same Picard pullback and the same
action on the numbered branches. The charge lattice may have any rank. -/
theorem comp_contractedXEvaluation_eq_of_matching_actions
    (hc : Φ.IsComplete) (hD : D.IsEffectiveCartier)
    {m : ℕ} {T : BlowupTower X m Y} (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (e : Y ≅ (M c).1)
    (he : e.hom ≫ π c ≫ Φ.algebraicRealizationStructureMap = T.toBase ≫ X ↘ S)
    (hB : (D.comap T.toBase).support = ((ι c).ker.comap e.hom).support)
    (u v : W ≅ X) [u.hom.IsOver S] [v.hom.IsOver S]
    (uB vB : E.subscheme ≅ D.subscheme) [uB.hom.IsOver S] [vB.hom.IsOver S]
    (hu : uB.hom ≫ D.subschemeι = E.subschemeι ≫ u.hom)
    (hv : vB.hom ≫ D.subschemeι = E.subschemeι ≫ v.hom)
    (A : NodalCycleNumbering a n) (B : NodalCycleNumbering d n)
    (hPic : ∀ L, pullback u.hom L = pullback v.hom L)
    (hact : uB.boundaryCycleAction B A = vB.boundaryCycleAction B A) :
    let : IsIntegral W := IsIntegral.of_isIso u.inv
    let : IsModification T.toBase :=
      hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
    u.hom.toRationalMap.comp (contractedXEvaluation b s c hΦ (e.inv ≫ T.toBase)) =
      v.hom.toRationalMap.comp (contractedXEvaluation b s c hΦ (e.inv ≫ T.toBase)) := by
  let : IsIntegral W := IsIntegral.of_isIso u.inv
  let : IsModification T.toBase :=
    hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let w := u.symm ≪≫ v
  let wB := uB.symm ≪≫ vB
  let : uB.symm.hom.IsOver S := inferInstanceAs (uB.inv.IsOver S)
  let : w.hom.IsOver S := inferInstanceAs ((u.inv ≫ v.hom).IsOver S)
  let : wB.hom.IsOver S := inferInstanceAs ((uB.inv ≫ vB.hom).IsOver S)
  have huw : u.hom ≫ w.hom = v.hom := by simp [w]
  have hw : wB.hom ≫ D.subschemeι = D.subschemeι ≫ w.hom := by
    apply (cancel_epi uB.hom).mp
    simp only [w, wB, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
      hv, reassoc_of% hu]
  have ha : wB.boundaryCycleAction A A = 1 := by
    rw [Iso.boundaryCycleAction_trans uB.symm A B vB A,
      Iso.boundaryCycleAction_symm uB B A, hact, mul_inv_cancel]
  have hp (L : LineBundleClass X) : pullback w.hom L = L := by
    apply (pullbackEquiv u).injective
    simpa only [pullbackEquiv_apply, pullback_comp, huw] using (hPic L).symm
  have hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S) := by
    rw [← D.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have hfix := hD.fixes_components_of_boundaryCycleAction_eq_one w wB hw A ha
  have hb := (wB.fixesNodalBranches_iff_boundaryCycleAction_eq_one A).mpr ha
  have hwOver : wB.hom ≫ D.subschemeι ≫ (X ↘ S) = D.subschemeι ≫ (X ↘ S) := by
    rw [reassoc_of% hw, HomIsOver.comp_over]
  have heval := comp_contractedXEvaluation_eq_of_fixes_nodal_branches b s hΦ hD hN
    hT e hc he hB (Aut.of w) (HomIsOver.comp_over (f := w.hom)) hp hfix wB hw
    (by
      apply (wB.fixesNodalBranches_iff _ hN hwOver).mp
      -- Transport the branch condition to the composite defining the boundary structure map.
      convert hb using 1
      exact D.over_eq_subschemeι_comp.symm)
  simpa only [← comp_assoc, comp_toRationalMap, Scheme.Hom.toRationalMap_compHom, huw]
    using congrArg (u.hom.toRationalMap.comp ·) heval.symm

end SameCenter

section AlignedCenters

variable (c d : Multiplicative (Fin r → ℤ) →* ℂˣ)
  {X X' Y Y' : Scheme} [X.Over S] [X'.Over S] [IsIntegral X] [IsIntegral X']
  [SmoothOfRelativeDimension 2 (X ↘ S)] [SmoothOfRelativeDimension 2 (X' ↘ S)]
  [QuasiCompact (X ↘ S)] [QuasiCompact (X' ↘ S)]
  {D : X.IdealSheafData} {D' : X'.IdealSheafData}
  [PrestableFamily (D.subscheme ↘ S)] [PrestableFamily (D'.subscheme ↘ S)]
  [PrestableFamily ((Φ.boundaryIdeal h₀).subscheme ↘ Spec (.of ℂ))]
  {m m' : ℕ} {T : BlowupTower X m Y} {U : BlowupTower X' m' Y'}
  {n a : ℕ} [NeZero n] [NeZero a] {α β γ : Type*}
  {p₀ : α → (D.subscheme ↘ S).smoothLocus} {p₁ : β → (D'.subscheme ↘ S).smoothLocus}
  {pT : γ → ((Φ.boundaryIdeal h₀).subscheme ↘ Spec (.of ℂ)).smoothLocus}

local notation "p[" e "]" => (Iso.inv e ≫ toBase T)
local notation "q[" e "]" => (Iso.inv e ≫ toBase U)

/-- After the labeled centers are aligned on the charge kernel, a pair isomorphism
with the marked Picard pullback and the prescribed oriented surviving-ray action
intertwines the two fixed-center rational evaluations. The subdivisions refer to
the actual ordered branches, even on cycles with one or two components. -/
theorem comp_contractedXEvaluation_eq_of_eq_center_character
    (hc : Φ.IsComplete) (hCartier : D'.IsEffectiveCartier)
    (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (hU : IsNodalBoundaryTower D' (X' ↘ S) (𝟙 X') U)
    (e : Y ≅ (M c).1) (e' : Y' ≅ (M d).1)
    (hp : p[e] ≫ (X ↘ S) = π c ≫ Φ.algebraicRealizationStructureMap)
    (hq : q[e'] ≫ (X' ↘ S) = π d ≫ Φ.algebraicRealizationStructureMap)
    (hD : (D.comap p[e]).support = (ι c).ker.support)
    (hD' : (D'.comap q[e']).support = (ι d).ker.support)
    (hkeep : ∀ ρ : Φ.Ray, p[e] ((prime c) ρ).val ∈ D.boundaryPrimes ↔
      q[e'] ((prime d) ρ).val ∈ D'.boundaryPrimes)
    (hcenters : ∀ x ∈ (rayChargeMap s).ker,
      (∏ j, (center c) j ^ x j) = ∏ j, (center d) j ^ x j)
    (A : NodalCycleNumbering p₀ n) (B : NodalCycleNumbering p₁ n) (C : NodalCycleNumbering pT a)
    (f : (Dtor).subscheme ⟶ D.subscheme) (g : (Dtor).subscheme ⟶ D'.subscheme)
    [f.IsOver S] [g.IsOver S]
    (hf : f ≫ D.subschemeι = ι c ≫ p[e]) (hg : g ≫ D'.subschemeι = ι d ≫ q[e'])
    (hfs : f.IsOrientedCycleSubdivision C A) (hgs : g.IsOrientedCycleSubdivision C B)
    (v : X ≅ X') [v.hom.IsOver S] (vB : D.subscheme ≅ D'.subscheme) [vB.hom.IsOver S]
    (hv : vB.hom ≫ D'.subschemeι = D.subschemeι ≫ v.hom)
    (hPic : ∀ L : LineBundleClass X',
      (mark c).symm (Additive.ofMul (pullback p[e] (pullback v.hom L))) =
        (mark d).symm (Additive.ofMul (pullback q[e'] L)))
    (j : ZMod n) (hact : vB.boundaryCycleAction A B = DihedralGroup.r j)
    (x : D.boundaryPrimes) (y : D'.boundaryPrimes)
    (hx : x.val = D.subschemeι (A.componentGenericPoint 0))
    (hy : y.val = D'.subschemeι (B.componentGenericPoint j))
    (ρ : Φ.Ray) (hxρ : p[e] ((prime c) ρ).val = x.val) (hyρ : q[e'] ((prime d) ρ).val = y.val) :
    let : IsModification T.toBase :=
      hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
    let : IsModification U.toBase :=
      hU.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X' ↘ S)
    v.hom.toRationalMap.comp (contractedXEvaluation b s d hΦ q[e']) =
      contractedXEvaluation b s c hΦ p[e] := by
  let : IsModification T.toBase :=
    hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
  let : IsModification U.toBase :=
    hU.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X' ↘ S)
  have : IsReduced D.subscheme :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := D.subscheme ↘ S)).isReduced
  have : IsReduced D'.subscheme :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := D'.subscheme ↘ S)).isReduced
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : Smooth (X' ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  have : IsNoetherian X' := isNoetherian_of_finiteType (X' ↘ S)
  have : AlgebraicGeometry.IsRegular X := AlgebraicGeometry.IsRegular.of_smooth (X ↘ S)
  have : AlgebraicGeometry.IsRegular X' := AlgebraicGeometry.IsRegular.of_smooth (X' ↘ S)
  obtain ⟨u, hover, hcomap, ⟨t⟩⟩ :=
    exists_iso_of_eq_center_character hΦ b s c d hT hU e e' hp hq hD hD' hkeep hcenters
  obtain ⟨uB, hu⟩ := D'.exists_iso_of_comap_eq_ker u D.subschemeι
    (hcomap.trans D.ker_subschemeι.symm)
  let : u.hom.IsOver S := ⟨hover⟩
  let : uB.hom.IsOver S := ⟨by
    rw [D'.over_eq_subschemeι_comp, reassoc_of% hu, hover, D.over_eq_subschemeι_comp]⟩
  have hray := ((contractedBoundaryRayEmbedding_eq_iff hΦ b s (center c) p[e] hD x ρ).mpr hxρ).trans
    (((contractedBoundaryRayEmbedding_eq_iff hΦ b s (center d) q[e'] hD' y ρ).mpr hyρ).symm)
  have huact := (boundaryCycleAction_eq_r_iff_of_isLift_torusTranslation b s c d hΦ A B C
    hf hg hfs hgs hu hc t.isLift t.commutes hD hD' j x y hx hy).mpr hray
  have hPic' (L : LineBundleClass X') : pullback v.hom L = pullback u.hom L := by
    apply hT.isClosedPointTower.injective_pullback_toBase (X ↘ S)
    apply (pullbackEquiv e.symm).injective
    have hmark := (hPic L).trans (t.pullback_marking hΦ L).symm
    simpa only [pullbackEquiv_apply, Iso.symm_hom, pullback_comp, Category.assoc] using
      Additive.ofMul.injective ((mark c).symm.injective hmark)
  have he' : e'.hom ≫ π d ≫ Φ.algebraicRealizationStructureMap = U.toBase ≫ (X' ↘ S) := by
    rw [← hq, Category.assoc, Iso.hom_inv_id_assoc]
  have hD'' : (D'.comap U.toBase).support = ((ι d).ker.comap e'.hom).support := calc
    _ = ((D'.comap q[e']).comap e'.hom).support := by
      rw [← comap_comp, Iso.hom_inv_id_assoc]
    _ = _ := by rw [support_comap (D'.comap q[e']), support_comap ((ι d).ker), hD']
  exact (comp_contractedXEvaluation_eq_of_matching_actions b s hΦ d hc hCartier hU e' he' hD''
    v u vB uB hv hu B A hPic' (hact.trans huact.symm)).trans (t.comp_contractedXEvaluation hΦ)

end AlignedCenters

end TauCeti.Toric.Fan

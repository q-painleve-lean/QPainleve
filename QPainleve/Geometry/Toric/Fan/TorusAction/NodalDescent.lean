/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Automorphism
public import QPainleve.Geometry.Toric.Fan.TorusAction.Automorphism

import QPainleve.AlgebraicGeometry.Blowup.Tower.Descent

/-!
# Quotient-character translations on contracted toric presentations

Translations fixing the ordered internal centers descend through the point blowups of
a toric presentation. The descent is faithful, acts trivially on the Picard group, and
fixes every prime boundary component. Its image consists of the automorphisms with
these properties which lift through the specified point blowups.

This is the descent of torus translations in the toric proof of [Gross, Hacking and
Keel, Proposition 2.6](https://arxiv.org/html/1211.6367v5#S2).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative TopologicalSpace
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  {n : ℕ} (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ)
  (hΦ : Φ.IsRegular)

local notation "M" => Sigma.fst (internalBlowupTower b s c)
local notation "B" =>
  Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd (internalBlowupTower b s c)))
local notation "A" => internalBlowupPicardBoundaryAut b s c hΦ
local notation "Chars" => (Multiplicative (N ⧸ LinearMap.range (rayChargeMap s)) →* ℂˣ)

variable {X Y : Scheme} (f : X ⟶ Spec (.of ℂ))
  {m : ℕ} {T : BlowupTower X m Y} {D : X.IdealSheafData}
  (e : Y ≅ (internalBlowupTower b s c).1)
  (he : e.hom ≫ (internalBlowupTower b s c).2.toTower.toBase ≫
    Φ.algebraicRealizationStructureMap = T.toBase ≫ f)
  (hB : (D.comap T.toBase).support =
    ((internalBlowupTower b s c).2.boundaryι.ker.comap e.hom).support)

local notation "toTop" => Aut.autMulEquivOfIso (Iso.symm e)

include he hB in
private theorem conjugate_internalBlowupPicardBoundaryAut_iff (g : Aut M) :
    g ∈ A ↔
      (toTop g).asIso.hom ≫ T.toBase ≫ f = T.toBase ≫ f ∧
      (∀ L, pullback (toTop g).asIso.hom L = L) ∧
      ∀ y : CodimensionOnePoint Y, y.val ∈ (D.comap T.toBase).support →
        (toTop g).asIso.hom y.val = y.val := by
  have hcomm : (toTop g).asIso.hom ≫ e.hom = e.hom ≫ g.asIso.hom := by
    simp
  rw [mem_internalBlowupPicardBoundaryAut_iff_fixes_boundary_primes]
  refine and_congr ?_ (and_congr ?_ ?_)
  · rw [← he, reassoc_of% hcomm, cancel_epi]
  · constructor
    · intro hg L
      obtain ⟨L', hL⟩ := (pullbackEquiv e).surjective L
      rw [pullbackEquiv_apply] at hL
      rw [← hL, pullback_comp, hcomm, ← pullback_comp, hg]
    · intro hh L
      apply (pullbackEquiv e).injective
      rw [pullbackEquiv_apply, pullbackEquiv_apply, pullback_comp, ← hcomm, ← pullback_comp, hh]
  · have hm (y : Y) : y ∈ (D.comap T.toBase).support ↔ e.hom y ∈ (B).support := by
      rw [hB, support_comap]
      rfl
    have hp (y : Y) : e.hom ((toTop g).asIso.hom y) = g.asIso.hom (e.hom y) :=
      congrArg (fun q : Y ⟶ M ↦ q y) hcomm
    constructor
    · intro hg y hy
      apply e.hom.injective
      rw [hp]
      exact hg ⟨e.hom y, (coheight_eq_of_isOpenImmersion e.hom).trans y.property⟩
        ((hm y).mp hy)
    · intro hh x hx
      obtain ⟨y, hy⟩ := e.hom.surjective x.val
      have hy₁ : Order.coheight y = 1 :=
        (coheight_eq_of_isOpenImmersion e.hom).symm.trans (hy ▸ x.property)
      have hfix := hh ⟨y, hy₁⟩ ((hm y).mpr (hy.symm ▸ hx))
      simpa only [hfix, hy] using (hp y).symm

variable [IsIntegral X] [IsNoetherian X] [SmoothOfRelativeDimension 2 f]
  (hT : IsClosedPointTower X T)

include f hT in
private theorem existsUnique_descend_model_aut (g : A) :
    ∃! a : X ≅ X, IsLift a T T (toTop (g : Aut M)).asIso ∧
      ∀ L, pullback a.hom L = L := by
  apply hT.existsUnique_isLift_of_picard_trivial f
  intro L
  have hPic := ((mem_internalBlowupPicardBoundaryAut b s c hΦ g.val).mp g.property).2.1
  obtain ⟨L', rfl⟩ := (pullbackEquiv e).surjective L
  rw [pullbackEquiv_apply, pullback_comp, Aut.autMulEquivOfIso_apply_asIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, ← pullback_comp, hPic]

private def descendModelAut : A →* Aut X where
  toFun g := Aut.of (existsUnique_descend_model_aut b s c hΦ f e hT g).exists.choose
  map_one' := by
    have := hT.epi_toBase f
    apply Aut.ext
    apply Iso.ext
    have hlift := (existsUnique_descend_model_aut b s c hΦ f e hT
      (1 : A)).exists.choose_spec.1
    apply (cancel_epi T.toBase).mp
    simpa only [Subgroup.coe_one, map_one, Aut.one_asIso, Iso.refl_hom, Category.id_comp,
      Category.comp_id] using hlift.hom_toBase.symm
  map_mul' g g' := by
    have := hT.epi_toBase f
    apply Aut.ext
    apply Iso.ext
    have lift (a : A) :=
      (existsUnique_descend_model_aut b s c hΦ f e hT a).exists.choose_spec.1
    apply (cancel_epi T.toBase).mp
    have h : (toTop ((g * g' : A) : Aut M)).asIso =
        (toTop (g' : Aut M)).asIso ≪≫ (toTop (g : Aut M)).asIso := by
      rw [Subgroup.coe_mul, map_mul, Aut.mul_asIso]
    have hcomp := congrArg (fun a : Y ≅ Y ↦ a.hom ≫ T.toBase) h
    simpa only [Aut.mul_asIso] using (lift (g * g')).hom_toBase.symm.trans
      (hcomp.trans ((lift g').trans (lift g)).hom_toBase)

/-- Quotient characters act on the original surface of a toric presentation by
descending their lifts to the ordered internal blowups. -/
def toricPresentationCharacterHom (hc : Φ.IsComplete) : Chars →* Aut X :=
  (descendModelAut b s c hΦ f e hT).comp
    (internalBlowupPicardBoundaryAutMulEquiv b s c hΦ hc).toMonoidHom

variable (hc : Φ.IsComplete)

/-- The ordered lift of the descended automorphism is the conjugate of the canonical
character action on the internal blowup model. -/
theorem toricPresentationCharacterHom_isLift (z : Chars) :
    IsLift (toricPresentationCharacterHom b s c hΦ f e hT hc z).asIso T T
      (toTop ((internalBlowupPicardBoundaryAutMulEquiv b s c hΦ hc z : A) : Aut M)).asIso :=
  (existsUnique_descend_model_aut b s c hΦ f e hT
    (internalBlowupPicardBoundaryAutMulEquiv b s c hΦ hc z)).exists.choose_spec.1

/-- A quotient character is determined by its descended automorphism. -/
theorem toricPresentationCharacterHom_injective :
    Function.Injective (toricPresentationCharacterHom b s c hΦ f e hT hc) := by
  intro z w hzw
  have hz := toricPresentationCharacterHom_isLift b s c hΦ f e hT hc z
  have hw := toricPresentationCharacterHom_isLift b s c hΦ f e hT hc w
  have heq := hz.unique (hzw.symm ▸ hw)
  exact (internalBlowupPicardBoundaryAutMulEquiv b s c hΦ hc).injective
    (Subtype.ext ((toTop).injective (Aut.ext heq)))

include he hB in
/-- The image of the character action is precisely the Picard-trivial automorphisms
over the field that fix the boundary components and lift through the specified tower. -/
theorem mem_range_toricPresentationCharacterHom_iff (a : Aut X) :
    a ∈ (toricPresentationCharacterHom b s c hΦ f e hT hc).range ↔
      a.asIso.hom ≫ f = f ∧ (∀ L, pullback a.asIso.hom L = L) ∧
      (∀ x : CodimensionOnePoint X, (x : X) ∈ D.support → a.asIso.hom x = x) ∧
      ∃ g : Y ≅ Y, IsLift a.asIso T T g := by
  constructor
  · rintro ⟨z, rfl⟩
    let g := internalBlowupPicardBoundaryAutMulEquiv b s c hΦ hc z
    have hlift := toricPresentationCharacterHom_isLift b s c hΦ f e hT hc z
    obtain ⟨hover, hPic, hfix⟩ :=
      (conjugate_internalBlowupPicardBoundaryAut_iff b s c hΦ f e he hB g.val).mp g.property
    have := hT.epi_toBase f
    refine ⟨(cancel_epi T.toBase).mp ?_, (hlift.forall_pullback_eq_iff f hT).mp hPic,
      (hlift.fixes_boundary_components_iff f hT D).mp hfix, _, hlift⟩
    rw [← hlift.hom_toBase_assoc]
    exact hover
  · rintro ⟨hover, hPic, hfix, g, hg⟩
    let gM := (toTop).symm (Aut.of g)
    have hgM : (toTop gM).asIso = g := by simp [gM]
    have hmem : gM ∈ A := by
      apply (conjugate_internalBlowupPicardBoundaryAut_iff b s c hΦ f e he hB gM).mpr
      rw [hgM]
      exact ⟨by rw [hg.hom_toBase_assoc, hover],
        (hg.forall_pullback_eq_iff f hT).mpr hPic,
        (hg.fixes_boundary_components_iff f hT D).mpr hfix⟩
    obtain ⟨z, hz⟩ := (internalBlowupPicardBoundaryAutMulEquiv b s c hΦ hc).surjective ⟨gM, hmem⟩
    have hlift := toricPresentationCharacterHom_isLift b s c hΦ f e hT hc z
    rw [hz, hgM] at hlift
    have := hT.epi_toBase f
    exact ⟨z, Aut.ext (Iso.ext ((cancel_epi T.toBase).mp
      (hlift.hom_toBase.symm.trans hg.hom_toBase)))⟩

end TauCeti.Toric.Fan

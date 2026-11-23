/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import QPainleve.AlgebraicGeometry.Blowup.Point.Cohomology
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.Descent.Contraction
import TauCeti.AlgebraicGeometry.Morphisms.Epi

/-!
# Descent along point blowups

A morphism out of a point blowup descends uniquely if its restriction to the exceptional
fiber is constant on points. The isomorphism over the complement of the center accounts
for every other fiber. The section isomorphisms for a regular point blowup give the
hypotheses of Tau Ceti's `Scheme.Hom.existsUnique_comp_eq_of_universallyClosed`.

In particular, a scheme isomorphism that carries one exceptional fiber onto another descends
to an isomorphism of the bases.
-/

public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y S : Scheme.{u}}

/-- The blowup projection is injective on the inverse image of the complement of the center. -/
theorem injOn_blowupToBase_compl_support (I : X.IdealSheafData) :
    Set.InjOn I.blowupToBase (I.blowupToBase ⁻¹' (I.support : Set X)ᶜ) := by
  let U := I.support.compl
  intro x hx y hy hxy
  let x' : (I.blowupToBase ⁻¹ᵁ U).toScheme := ⟨x, hx⟩
  let y' : (I.blowupToBase ⁻¹ᵁ U).toScheme := ⟨y, hy⟩
  have h : (I.blowupToBase ∣_ U) x' = (I.blowupToBase ∣_ U) y' :=
    Subtype.ext (by simpa only [morphismRestrict_base_coe] using hxy)
  exact congrArg Subtype.val ((I.blowupToBase ∣_ U).isOpenEmbedding.injective h)

variable {p : X}

local notation "Iₚ" =>
  vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)
local notation "πₚ" => blowupToBase Iₚ
local notation "Eₚ" => IdealSheafData.comap Iₚ πₚ

/-- The underlying set of the exceptional subscheme is the fiber over the blowup center. -/
theorem range_subschemeι_comap_pointBlowup (hp : IsClosed ({p} : Set X)) :
    Set.range (Eₚ).subschemeι = πₚ ⁻¹' {p} := by
  rw [range_subschemeι, support_comap, Closeds.coe_preimage, coe_support_vanishingIdeal,
    Closeds.coe_mk]
  exact congrArg (fun v : Set X ↦ πₚ ⁻¹' v) hp.closure_eq

/-- A map on a point blowup is constant on the fibers of the blowup projection exactly when its
restriction to the exceptional subscheme is constant on points. -/
theorem factorsThrough_blowupToBase_point_iff (hp : IsClosed ({p} : Set X))
    (h : (Iₚ).blowup ⟶ Y) :
    Function.FactorsThrough h πₚ ↔ Set.Subsingleton (Set.range ((Eₚ).subschemeι ≫ h)) := by
  have hE : Set.range (Eₚ).subschemeι = πₚ ⁻¹' {p} :=
    range_subschemeι_comap_pointBlowup hp
  constructor
  · rintro hh _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    simp only [Scheme.Hom.comp_apply]
    have hpoint (z : (Eₚ).subscheme) : πₚ ((Eₚ).subschemeι z) = p := by
      have hz : (Eₚ).subschemeι z ∈ πₚ ⁻¹' {p} := hE ▸ Set.mem_range_self z
      exact hz
    exact hh ((hpoint x).trans (hpoint y).symm)
  · intro hh x y hxy
    by_cases hx : πₚ x = p
    · obtain ⟨x', rfl⟩ : x ∈ Set.range (Eₚ).subschemeι := hE.symm ▸ hx
      obtain ⟨y', rfl⟩ : y ∈ Set.range (Eₚ).subschemeι := hE.symm ▸ (hxy.symm.trans hx)
      simpa only [Scheme.Hom.comp_apply] using
        hh (Set.mem_range_self x') (Set.mem_range_self y')
    · have hs : ((Iₚ).support : Set X) = {p} := by
        rw [coe_support_vanishingIdeal, Closeds.coe_mk]
        exact hp.closure_eq
      have hmem {z : (Iₚ).blowup} (hz : πₚ z ≠ p) :
          z ∈ πₚ ⁻¹' ((Iₚ).support : Set X)ᶜ := by
        rw [hs, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
        exact hz
      exact congrArg h ((Iₚ).injOn_blowupToBase_compl_support
        (hmem hx) (hmem (hxy ▸ hx)) hxy)

section RegularPoint

variable [IsLocallyNoetherian X] [IsRegularLocalRing (X.presheaf.stalk p)]

/-- The projection of the blowup of a regular closed point of local dimension two is
surjective. It is proper and scheme-theoretically dominant by the section isomorphisms. -/
theorem surjective_blowupToBase_point (hp : IsClosed ({p} : Set X))
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) : Surjective πₚ := by
  have : IsSchemeTheoreticallyDominant πₚ := by
    constructor
    apply IdealSheafData.ext
    funext U
    rw [Scheme.Hom.ker_apply, ideal_bot, Pi.bot_apply, ← RingHom.injective_iff_ker_eq_bot]
    have := isIso_app_pointBlowup hp hdim U.val
    exact (ConcreteCategory.bijective_of_isIso ((πₚ).app U.val)).1
  infer_instance

/-- The point blowup projection is an epimorphism of schemes. -/
theorem epi_blowupToBase_point (hp : IsClosed ({p} : Set X))
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) : Epi πₚ := by
  have := surjective_blowupToBase_point hp hdim
  exact (πₚ).epi_of_surjective_of_app_injective fun U ↦ by
    have := isIso_app_pointBlowup hp hdim U
    exact (ConcreteCategory.bijective_of_isIso ((πₚ).app U)).1

/-- A morphism out of the blowup of a regular closed point of local dimension two descends
uniquely when it is constant on the exceptional fiber. -/
theorem existsUnique_comp_eq_pointBlowup (hp : IsClosed ({p} : Set X))
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) (h : (Iₚ).blowup ⟶ Y)
    (hh : Set.Subsingleton (Set.range ((Eₚ).subschemeι ≫ h))) :
    ∃! g : X ⟶ Y, πₚ ≫ g = h := by
  have := surjective_blowupToBase_point hp hdim
  exact (πₚ).existsUnique_comp_eq_of_universallyClosed
    (isIso_app_pointBlowup hp hdim) h ((factorsThrough_blowupToBase_point_iff hp h).mpr hh)

/-- Descent along a point blowup preserves the structure maps to any base scheme. -/
theorem existsUnique_comp_eq_pointBlowup_over [X.Over S] [Y.Over S]
    (hp : IsClosed ({p} : Set X)) (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (h : (Iₚ).blowup ⟶ Y) (hS : h ≫ (Y ↘ S) = πₚ ≫ (X ↘ S))
    (hh : Set.Subsingleton (Set.range ((Eₚ).subschemeι ≫ h))) :
    ∃! g : X ⟶ Y, πₚ ≫ g = h ∧ g.IsOver S := by
  obtain ⟨g, hg, huniq⟩ := existsUnique_comp_eq_pointBlowup hp hdim h hh
  have := epi_blowupToBase_point hp hdim
  refine ⟨g, ⟨hg, ⟨?_⟩⟩, fun _ h' ↦ huniq _ h'.1⟩
  apply (cancel_epi πₚ).mp
  rwa [← Category.assoc, hg]

variable {q : Y} [IsLocallyNoetherian Y] [IsRegularLocalRing (Y.presheaf.stalk q)]

local notation "I_q" =>
  vanishingIdeal (Closeds.mk (closure (Set.singleton q)) isClosed_closure)
local notation "π_q" => blowupToBase I_q
local notation "E_q" => IdealSheafData.comap I_q π_q

/-- An isomorphism between two regular point blowups that carries one exceptional fiber onto
the other descends to a unique isomorphism of the bases. -/
theorem existsUnique_iso_of_pointBlowup (hp : IsClosed ({p} : Set X))
    (hq : IsClosed ({q} : Set Y)) (hdp : ringKrullDim (X.presheaf.stalk p) = 2)
    (hdq : ringKrullDim (Y.presheaf.stalk q) = 2) (e : (Iₚ).blowup ≅ (I_q).blowup)
    (he : e.hom '' Set.range (Eₚ).subschemeι = Set.range (E_q).subschemeι) :
    ∃! f : X ≅ Y, πₚ ≫ f.hom = e.hom ≫ π_q := by
  have hE := range_subschemeι_comap_pointBlowup hp
  have hF := range_subschemeι_comap_pointBlowup hq
  have hInv (y : (I_q).blowup) : e.hom (e.inv y) = y := by simp
  have hfiber : Set.Subsingleton (Set.range ((Eₚ).subschemeι ≫ e.hom ≫ π_q)) := by
    refine Set.Subsingleton.anti (Set.subsingleton_singleton (a := q)) ?_
    rintro _ ⟨x, rfl⟩
    have hx : e.hom ((Eₚ).subschemeι x) ∈ π_q ⁻¹' {q} := by
      rw [← hF, ← he]
      exact Set.mem_image_of_mem _ (Set.mem_range_self x)
    simpa only [Scheme.Hom.comp_apply, Set.mem_preimage] using hx
  have hback : Set.Subsingleton (Set.range ((E_q).subschemeι ≫ e.inv ≫ πₚ)) := by
    refine Set.Subsingleton.anti (Set.subsingleton_singleton (a := p)) ?_
    rintro _ ⟨y, rfl⟩
    have hy : (E_q).subschemeι y ∈ e.hom '' Set.range (Eₚ).subschemeι :=
      he.symm ▸ Set.mem_range_self y
    obtain ⟨x, hx, hxy⟩ := hy
    have hInvEq : e.inv ((E_q).subschemeι y) = x :=
      e.hom.isOpenEmbedding.injective ((hInv _).trans hxy.symm)
    have hx' : x ∈ πₚ ⁻¹' {p} := hE ▸ hx
    simpa only [Scheme.Hom.comp_apply, hInvEq, Set.mem_preimage] using hx'
  obtain ⟨f, hf, huniq⟩ := existsUnique_comp_eq_pointBlowup hp hdp (e.hom ≫ π_q) hfiber
  obtain ⟨g, hg, -⟩ := existsUnique_comp_eq_pointBlowup hq hdq (e.inv ≫ πₚ) hback
  have := epi_blowupToBase_point hp hdp
  have := epi_blowupToBase_point hq hdq
  refine ⟨⟨f, g, ?_, ?_⟩, hf, fun f' hf' ↦ Iso.ext (huniq f'.hom hf')⟩
  · apply (cancel_epi πₚ).mp
    rw [← Category.assoc, hf, Category.assoc, hg, e.hom_inv_id_assoc, Category.comp_id]
  · apply (cancel_epi π_q).mp
    rw [← Category.assoc, hg, Category.assoc, hf, e.inv_hom_id_assoc, Category.comp_id]

end RegularPoint

end AlgebraicGeometry.Scheme.IdealSheafData

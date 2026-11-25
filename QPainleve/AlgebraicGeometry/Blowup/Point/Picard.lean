/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Class
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.AlgebraicGeometry.CartierDivisor.Excision

import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Picard
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# Descent of point blowup isomorphisms from their Picard action

Matching the exceptional Picard classes identifies the exceptional ideals. Contraction
then recovers the base isomorphism using `existsUnique_iso_of_pointBlowup`. The
commuting square identifies the reduced center ideals.

The prime divisor over the center has the exceptional class.
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X Y : Scheme.{u}} {p : X} {q : Y}

local notation "Iₚ" => Scheme.Hom.ker (Scheme.fromSpecResidueField X p)
local notation "I_q" => Scheme.Hom.ker (Scheme.fromSpecResidueField Y q)

/-- An isomorphism of blowups at regular closed points of local dimension two that matches
the exceptional Picard classes is the canonical lift of a unique isomorphism matching the
reduced center ideals. -/
theorem existsUnique_baseIso_of_pullback_blowupExceptionalClass_eq
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsRegularLocalRing (X.presheaf.stalk p)] [IsRegularLocalRing (Y.presheaf.stalk q)]
    (hp : IsClosed ({p} : Set X)) (hq : IsClosed ({q} : Set Y))
    (hdp : ringKrullDim (X.presheaf.stalk p) = 2)
    (hdq : ringKrullDim (Y.presheaf.stalk q) = 2) (e : (Iₚ).blowup ≅ (I_q).blowup)
    (he : LineBundleClass.pullback e.hom (I_q).blowupExceptionalClass =
      (Iₚ).blowupExceptionalClass) :
    ∃! f : X ≅ Y, ∃ h : (I_q).comap f.hom = Iₚ, e = blowupIso f h.symm := by
  let E := (Iₚ).comap (Iₚ).blowupToBase
  let F := (I_q).comap (I_q).blowupToBase
  have hE : E.IsExceptionalCurveOfFirstKind :=
    isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hdp
  have hF : F.IsExceptionalCurveOfFirstKind :=
    isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint q hq hdq
  have : IsLocallyNoetherian (Iₚ).blowup :=
    LocallyOfFiniteType.isLocallyNoetherian (Iₚ).blowupToBase
  have := hF.isIntegral_subscheme
  have hEF : F.comap e.hom = E :=
    hE.comap_eq_of_pullback_mk_toInvertibleSheaf_eq hF.isEffectiveCartier e
      (inv_injective (by simpa only [blowupExceptionalClass_def, LineBundleClass.pullback_inv]
        using he))
  have hfiber : e.hom '' Set.range E.subschemeι = Set.range F.subschemeι := by
    rw [range_subschemeι, range_subschemeι, ← hEF, support_comap, Closeds.coe_preimage]
    have hsurj : Function.Surjective e.hom := e.hom.homeomorph.surjective
    exact Set.image_preimage_eq _ hsurj
  -- Abstract both centers together so the blowup schemes and their fiber types are transported.
  let Descends (A : X.IdealSheafData) (B : Y.IdealSheafData) : Prop :=
    ∀ g : A.blowup ≅ B.blowup,
      g.hom '' Set.range (A.comap A.blowupToBase).subschemeι =
        Set.range (B.comap B.blowupToBase).subschemeι →
      ∃! f : X ≅ Y, A.blowupToBase ≫ f.hom = g.hom ≫ B.blowupToBase
  have hdescend : Descends Iₚ I_q :=
    (congrArg₂ Descends (X.ker_fromSpecResidueField_eq_vanishingIdeal p)
      (Y.ker_fromSpecResidueField_eq_vanishingIdeal q)).mpr
      (existsUnique_iso_of_pointBlowup hp hq hdp hdq)
  obtain ⟨f, hf, huniq⟩ := hdescend e hfiber
  have hcomap : ((I_q).comap f.hom).comap (Iₚ).blowupToBase = E := by
    rw [← comap_comp, hf, comap_comp, hEF]
  have hsurj : Surjective (Iₚ).blowupToBase := by
    rw [X.ker_fromSpecResidueField_eq_vanishingIdeal p]
    exact surjective_blowupToBase_point hp hdp
  have hs := congrArg (fun J : (Iₚ).blowup.IdealSheafData ↦
    (J.support : Set (Iₚ).blowup)) hcomap
  simp only [E, support_comap _ (Iₚ).blowupToBase, Closeds.coe_preimage] at hs
  have hsupport : ((I_q).comap f.hom).support = (Iₚ).support :=
    SetLike.coe_injective (hsurj.surj.preimage_injective hs)
  have hpRed := (X.fromSpecResidueField p).ker_eq_vanishingIdeal_support
  have hqRed := (Y.fromSpecResidueField q).ker_eq_vanishingIdeal_support
  have hcenter' : (I_q).comap f.hom = Iₚ := by
    calc
      (I_q).comap f.hom = (vanishingIdeal (I_q).support).comap f.hom :=
        congrArg (fun J ↦ J.comap f.hom) hqRed
      _ = vanishingIdeal ((I_q).comap f.hom).support := by
        rw [comap_vanishingIdeal_of_isOpenImmersion, support_comap]
        rfl
      _ = Iₚ := (congrArg vanishingIdeal hsupport).trans hpRed.symm
  refine ⟨f, ⟨hcenter', (I_q).blowupIso_unique f hcenter' e hf.symm⟩, ?_⟩
  rintro g ⟨h, rfl⟩
  exact huniq g (blowupIso_hom_blowupToBase g h.symm).symm

end AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.AlgebraicGeometry.LineBundleClass

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} {p : X}

local notation "Iₚ" => Scheme.Hom.ker (Scheme.fromSpecResidueField X p)
local notation "π" => blowupToBase Iₚ

/-- The prime of a point blowup lying over its center has the class of the
exceptional divisor. -/
theorem primeDivisorClass_eq_blowupExceptionalClass_of_over_center
    [IsLocallyNoetherian X] [IsRegularLocalRing (X.presheaf.stalk p)]
    [∀ y : (Iₚ).blowup, IsDomain ((Iₚ).blowup.presheaf.stalk y)]
    [∀ y : (Iₚ).blowup, UniqueFactorizationMonoid ((Iₚ).blowup.presheaf.stalk y)]
    (s : CodimensionOnePoint (Iₚ).blowup) (hs : π s = p)
    (hp : IsClosed ({p} : Set X)) (hd : ringKrullDim (X.presheaf.stalk p) = 2) :
    letI : IsLocallyNoetherian (Iₚ).blowup := LocallyOfFiniteType.isLocallyNoetherian π
    primeDivisorClass s = (Iₚ).blowupExceptionalClass := by
  have : IsLocallyNoetherian (Iₚ).blowup := LocallyOfFiniteType.isLocallyNoetherian π
  let E := (Iₚ).comap π
  have hE := isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hd
  let : IsIntegral E.subscheme := hE.isIntegral_subscheme
  have hs' : (s : (Iₚ).blowup) ∈ E.support := by
    simp only [E, support_comap, ← SetLike.mem_coe, Closeds.coe_preimage, Set.mem_preimage,
      Scheme.support_ker_fromSpecResidueField_of_isClosed hp, hs, Set.mem_singleton_iff]
  have he := (hE.isEffectiveCartier.mem_support_iff_eq_subschemeι_genericPoint s.property).mp hs'
  rw [primeDivisorClass_def, blowupExceptionalClass_def]
  congr 1
  exact mk_toInvertibleSheaf_congr _ _ (by
    rw [he, E.vanishingIdeal_closure_subschemeι_genericPoint])

end TauCeti.AlgebraicGeometry.LineBundleClass

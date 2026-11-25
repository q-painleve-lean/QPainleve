/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Fiber
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import QPainleve.AlgebraicGeometry.Morphisms.Smooth.EtaleCoordinates
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# Blowing up a rational point on a smooth surface

Centered étale coordinates give two parameters generating the ideal of a rational
point on an affine neighbourhood in a smooth surface. The pair is regular
in both orders, so the two polynomial charts describe the blowup there.

The fiber computation uses `Scheme.IdealSheafData.isPullback_blowupChart_projectiveLine`,
which identifies the projectivized associated graded ring of a regular pair as in
[The Stacks Project, Lemma 54.3.1](https://stacks.math.columbia.edu/tag/0AGQ).
-/

public section

open CategoryTheory Limits
open TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {Y : Scheme.{u}}

local notation "SpecK" => Spec (CommRingCat.of k)

/-- The exceptional closed subscheme of the blowup of a rational point on a smooth surface
is a projective line. Under the isomorphism, the projective line's structure morphism and
its inclusion into the blowup exhibit it as the scheme-theoretic fiber over the point. -/
theorem exists_iso_projectiveLine_exceptional_blowup_ker (p : SpecK ⟶ Y) (π : Y ⟶ SpecK)
    [SmoothOfRelativeDimension 2 π] (hp : p ≫ π = 𝟙 SpecK) :
    let E := p.ker.comap p.ker.blowupToBase
    ∃ e : projectiveLine k ≅ E.subscheme,
      IsPullback (e.hom ≫ E.subschemeι) (projectiveLine k ↘ SpecK) p.ker.blowupToBase p := by
  obtain ⟨U, hU, a, b, hab, _, hI, e, he⟩ :=
    p.exists_regular_pair_ker_of_smoothOfRelativeDimension_two π hp
  let R := Γ(Y, U) ⧸ p.ker.ideal ⟨U, hU⟩
  let : Algebra R k := e.toRingHom.toAlgebra
  have hp' : Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ hU.fromSpec = p := by
    rw [← Category.assoc, ← Spec.map_comp]
    exact he
  have H := (projectiveLine.isPullback_baseChangeProjection R k).paste_horiz
    (p.ker.isPullback_blowupChart_projectiveLine hU hab.toIsWeaklyRegular hI)
  rw [hp'] at H
  have : IsClosedImmersion p := AlgebraicGeometry.isClosedImmersion_of_comp_eq_id π p hp
  let E := p.ker.comap p.ker.blowupToBase
  obtain ⟨i, H⟩ : ∃ i, IsPullback i (projectiveLine k ↘ SpecK) p.ker.blowupToBase p := ⟨_, H⟩
  have hi : IsClosedImmersion i := MorphismProperty.of_isPullback H.flip inferInstance
  have hker : i.ker = E := ker_eq_comap_of_isPullback p H
  let eE : projectiveLine k ≅ E.subscheme :=
    asIso i.toImage ≪≫ eqToIso (congrArg Scheme.IdealSheafData.subscheme hker)
  have heE : eE.hom ≫ E.subschemeι = i := by
    rw [Iso.trans_hom, asIso_hom, eqToIso.hom, Category.assoc,
      ← eqToHom_naturality Scheme.IdealSheafData.subschemeι hker]
    simp
  exact ⟨eE, heE.symm ▸ H⟩

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.SmoothOfRelativeDimension

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}}

/-- The exceptional subscheme of the blowup of the reduced ideal of a closed point on a
smooth surface over an algebraically closed field is a projective line over that point. -/
theorem exists_iso_projectiveLine_exceptional_blowup_closedPoint
    (π : Y ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 π] (x : Y) (hx : IsClosed {x}) :
    letI : Smooth π := SmoothOfRelativeDimension.smooth 2 π
    let I := vanishingIdeal ⟨{x}, hx⟩
    let E := I.comap I.blowupToBase
    ∃ e : projectiveLine k ≅ E.subscheme,
      IsPullback (e.hom ≫ E.subschemeι) (projectiveLine k ↘ Spec (.of k)) I.blowupToBase
        (pointOfClosedPoint π x hx) := by
  dsimp only
  have : Smooth π := SmoothOfRelativeDimension.smooth 2 π
  let p := pointOfClosedPoint π x hx
  have hp : p ≫ π = 𝟙 (Spec (.of k)) := pointOfClosedPoint_comp π x hx
  have : IsClosedImmersion p := AlgebraicGeometry.isClosedImmersion_of_comp_eq_id π p hp
  have hrange : Set.range p = {x} := Set.range_eq_singleton (pointOfClosedPoint_apply π x hx)
  have hsupp : p.ker.support = ⟨{x}, hx⟩ := SetLike.coe_injective (by
    rw [p.support_ker, hrange, hx.closure_eq]
    rfl)
  have hI : p.ker = vanishingIdeal ⟨{x}, hx⟩ := by
    apply le_antisymm
    · rw [← hsupp, vanishingIdeal_support]
      exact le_radical _
    · exact vanishingIdeal_le_ker_of_range_subset p hrange.le
  have H := p.exists_iso_projectiveLine_exceptional_blowup_ker π hp
  dsimp only at H
  rw [hI] at H
  exact H

/-- The exceptional subscheme of a closed-point blowup of a smooth surface over an
algebraically closed field is isomorphic to the projective line over the ground field. -/
theorem exists_iso_projectiveLine_exceptional_blowup_closedPoint_over
    (π : Y ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 π] (x : Y) (hx : IsClosed {x}) :
    let I := vanishingIdeal ⟨closure ({x} : Set Y), isClosed_closure⟩
    let E := I.comap I.blowupToBase
    ∃ e : projectiveLine k ≅ E.subscheme,
      e.hom ≫ E.subschemeι ≫ I.blowupToBase ≫ π = projectiveLine k ↘ Spec (.of k) := by
  dsimp only
  have hI : vanishingIdeal ⟨closure ({x} : Set Y), isClosed_closure⟩ = vanishingIdeal ⟨{x}, hx⟩ :=
    congrArg vanishingIdeal (SetLike.coe_injective hx.closure_eq)
  rw [hI]
  obtain ⟨e, he⟩ := exists_iso_projectiveLine_exceptional_blowup_closedPoint π x hx
  exact ⟨e, by
    simpa only [Category.assoc, pointOfClosedPoint_comp, Category.comp_id] using
      congrArg (· ≫ π) he.w⟩

end AlgebraicGeometry.SmoothOfRelativeDimension

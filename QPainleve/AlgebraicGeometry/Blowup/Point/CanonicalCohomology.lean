/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Canonical
public import QPainleve.AlgebraicGeometry.Blowup.Point.Cohomology
public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Cohomology
import QPainleve.AlgebraicGeometry.Cohomology.LongExactSequence
import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# Canonical cohomology under point blowup

For a point blowup of a smooth surface, the pullback on top differentials has cokernel
the restriction of the canonical bundle to the exceptional line. That restriction is
`𝒪(-1)` over the residue field, and has zero cohomology in every degree. The actual map
on top forms therefore gives the comparison on canonical cohomology, including the
top degree used to transport a trace.

The canonical class and the ramification description use Hacking's blowup formula
([*583C Lecture notes*, Proposition 7.2][Hacking]). The exceptional quotient is the
Cartier quotient in the blowup filtration of [Stacks, Lemma 54.3.4][Stacks].

[Hacking]: https://paulhacking.github.io/surfaces.pdf#page=35
[Stacks]: https://stacks.math.columbia.edu/tag/0AGS
-/

public noncomputable section

open CategoryTheory Limits TopologicalSpace QPainleve
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} {p : X}

local notation "Iₚ" => vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)
local notation "Y" => blowup Iₚ
local notation "π" => blowupToBase Iₚ

variable (k : Type u) [Field k] [PerfectField k] [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

private local instance : (Y).Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
private local instance : (π).IsOver (Spec (.of k)) := ⟨rfl⟩

/-- On a smooth surface point blowup, the map from the pulled-back canonical bundle
to the new canonical bundle induces a bijection on every cohomology group. -/
theorem bijective_cohomologyMap_topDifferentialFormsMap_pointBlowup
    (hp : IsClosed ({p} : Set X)) (q : ℕ) :
    letI : (Y).Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    letI : (π).IsOver (Spec (.of k)) := ⟨rfl⟩
    letI : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
    Function.Bijective (cohomologyMap (topDifferentialFormsMap k π 2) q) := by
  let : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
    smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
  have := SmoothOfRelativeDimension.smooth 2 (X ↘ Spec (.of k))
  have := SmoothOfRelativeDimension.smooth 2 (Y ↘ Spec (.of k))
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of k))
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
    (X ↘ Spec (.of k)) 2).mp inferInstance).2 p hp
  let ω := canonicalBundle k Y 2
  let d := topDifferentialFormsMap k π 2
  have hram := ramificationIdealSheaf_blowup_of_smoothSurface k hp
  have : Mono d :=
    mono_topDifferentialFormsMap_of_ramification k π 2
      (Iₚ).isEffectiveCartier_comap_blowupToBase hram
  let e := cokernelTopDifferentialFormsMapIso k π 2
    (Iₚ).isEffectiveCartier_comap_blowupToBase hram
  have hvan (i : ℕ) : Subsingleton (Cohomology (cokernel d) i) := by
    have h := subsingleton_cohomology_pointBlowup_exceptional_quotient_of_twist_one hp hdim
      (LineBundleClass.mk (canonicalBundle k X 2)) ω (mk_canonicalBundle_pointBlowup k hp) i
    exact @Function.Injective.subsingleton _ _ _
      ((cohomologyFunctor _ i).mapIso e).addCommGroupIsoToAddEquiv.injective h
  exact bijective_cohomologyMap_of_subsingleton_quotient
    (TauCeti.cokernelSequence_shortExact d) q (hvan q) (fun _ ↦ hvan (q - 1))

/-- The point blowup comparison for the canonical bundle, obtained from the acyclic
pullback comparison followed by the map on top forms. -/
def cohomologyCanonicalBundlePointBlowupLinearEquiv
    (hp : IsClosed ({p} : Set X)) (q : ℕ) :
    letI : (Y).Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    letI : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
    Cohomology (canonicalBundle k X 2).obj q ≃ₗ[k] Cohomology (canonicalBundle k Y 2).obj q := by
  letI : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
    smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
  have := SmoothOfRelativeDimension.smooth 2 (X ↘ Spec (.of k))
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of k))
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
    (X ↘ Spec (.of k)) 2).mp inferInstance).2 p hp
  let d := topDifferentialFormsMap k π 2
  let pull := pointBlowupCohomologyLinearEquiv k hp hdim
    ((InvertibleSheaf.toFiniteLocallyFree X).obj (canonicalBundle k X 2)) q
  refine pull.trans (LinearEquiv.ofBijective (cohomologyMapBaseLinear k Y d q) ?_)
  rw [coe_cohomologyMapBaseLinear]
  exact bijective_cohomologyMap_topDifferentialFormsMap_pointBlowup k hp q

/-- The forward blowup comparison is the acyclic pullback comparison followed by the
cohomology map induced by the actual pullback of top differential forms. -/
theorem cohomologyCanonicalBundlePointBlowupLinearEquiv_apply
    (hp : IsClosed ({p} : Set X)) (q : ℕ) (x : Cohomology (canonicalBundle k X 2).obj q) :
    letI : (Y).Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    letI : (π).IsOver (Spec (.of k)) := ⟨rfl⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
    let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    let : IsRegularLocalRing (X.presheaf.stalk p) :=
      isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k)) p
    let hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
      (X ↘ Spec (.of k)) 2).mp inferInstance).2 p hp
    cohomologyCanonicalBundlePointBlowupLinearEquiv k hp q x =
      cohomologyMapBaseLinear k Y (topDifferentialFormsMap k π 2) q
        (pointBlowupCohomologyLinearEquiv k hp hdim
          ((InvertibleSheaf.toFiniteLocallyFree X).obj (canonicalBundle k X 2)) q x) := (rfl)

end AlgebraicGeometry.Scheme.IdealSheafData

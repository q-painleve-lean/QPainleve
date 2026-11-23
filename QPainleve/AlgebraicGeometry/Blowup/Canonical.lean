/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Class
public import QPainleve.AlgebraicGeometry.Blowup.Ramification
public import QPainleve.AlgebraicGeometry.Blowup.Smooth
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical

/-!
# The canonical bundle of a point blowup

The canonical bundle of the blowup of a smooth surface at a closed point is the pullback
of the surface's canonical bundle twisted by the exceptional divisor. The comparison uses
the actual map on top differential forms and the calculation of the blowup's ramification
ideal. The resulting Picard class formula gives the canonical correction in intersection
and Riemann–Roch computations.

See [Hacking, *Compact Complex Surfaces*, Proposition 7.2][Hacking].

[Hacking]: https://paulhacking.github.io/surfaces.pdf#page=35
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {p : X} (k : Type u) [Field k] [PerfectField k]
    [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "Iₚ" => vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)

/-- On the blowup at a closed point of a smooth surface, the canonical bundle is the
pullback of the base canonical bundle tensored with the dual of the exceptional ideal. -/
noncomputable def canonicalBundleIsoPointBlowup (hp : IsClosed ({p} : Set X)) :
    let I := Iₚ
    letI : I.blowup.Over (Spec (.of k)) := ⟨I.blowupToBase ≫ X ↘ Spec (.of k)⟩
    letI : SmoothOfRelativeDimension 2 (I.blowup ↘ Spec (.of k)) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
    (QPainleve.canonicalBundle k I.blowup 2).obj ≅
      (InvertibleSheaf.tensorProduct
        ((InvertibleSheaf.pullback I.blowupToBase).obj (QPainleve.canonicalBundle k X 2))
        (InvertibleSheaf.dual I.isEffectiveCartier_comap_blowupToBase.toInvertibleSheaf)).obj := by
  let I := Iₚ
  letI : I.blowup.Over (Spec (.of k)) := ⟨I.blowupToBase ≫ X ↘ Spec (.of k)⟩
  haveI : I.blowupToBase.IsOver (Spec (.of k)) := ⟨rfl⟩
  haveI : SmoothOfRelativeDimension 2 (I.blowup ↘ Spec (.of k)) :=
    smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
  exact QPainleve.canonicalBundleIsoPullbackTensorDualRamification k I.blowupToBase 2
    I.isEffectiveCartier_comap_blowupToBase (ramificationIdealSheaf_blowup_of_smoothSurface k hp)

/-- The canonical class changes by the exceptional class under a smooth surface point blowup. -/
theorem mk_canonicalBundle_pointBlowup (hp : IsClosed ({p} : Set X)) :
    let I := Iₚ
    letI : I.blowup.Over (Spec (.of k)) := ⟨I.blowupToBase ≫ X ↘ Spec (.of k)⟩
    letI : SmoothOfRelativeDimension 2 (I.blowup ↘ Spec (.of k)) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
    LineBundleClass.mk (QPainleve.canonicalBundle k I.blowup 2) =
      LineBundleClass.pullback I.blowupToBase
        (LineBundleClass.mk (QPainleve.canonicalBundle k X 2)) *
        I.blowupExceptionalClass := by
  simpa only [LineBundleClass.mk_tensorProduct, ← LineBundleClass.pullback_mk,
    ← LineBundleClass.inv_mk, blowupExceptionalClass_def] using
    LineBundleClass.mk_eq_mk_iff.mpr ⟨canonicalBundleIsoPointBlowup k hp⟩

end AlgebraicGeometry.Scheme.IdealSheafData

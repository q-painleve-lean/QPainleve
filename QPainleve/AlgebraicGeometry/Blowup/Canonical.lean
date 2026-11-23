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
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.LineBundle.Power
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.GlobalSections
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField

/-!
# The canonical bundle of a point blowup

The canonical bundle of the blowup of a smooth surface at a closed point is the pullback
of the surface's canonical bundle twisted by the exceptional divisor. The comparison uses
the actual map on top differential forms and the calculation of the blowup's ramification
ideal. The resulting Picard class formula gives the canonical correction in intersection
and Riemann–Roch computations.

The formula also identifies the global sections of each nonnegative tensor power of the
canonical bundle before and after the blowup, using the comparison for exceptional twists.

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

open QPainleve TauCeti.AlgebraicGeometry.Scheme.Modules in
/-- A point blowup of a smooth surface preserves the space of sections of each
nonnegative tensor power of the relative canonical bundle. -/
noncomputable def cohomologyZeroPluricanonicalLinearEquiv {p : X}
    (hp : IsClosed ({p} : Set X)) (m : ℕ) :
    let I := vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)
    letI : I.blowup.Over (Spec (.of k)) := ⟨I.blowupToBase ≫ X ↘ Spec (.of k)⟩
    letI : SmoothOfRelativeDimension 2 (I.blowup ↘ Spec (.of k)) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
    Cohomology ((canonicalBundle k X 2).tensorPow m).obj 0 ≃ₗ[k]
      Cohomology ((canonicalBundle k I.blowup 2).tensorPow m).obj 0 := by
  let I := vanishingIdeal (X := X) (Closeds.mk (closure (Set.singleton p)) isClosed_closure)
  letI : I.blowup.Over (Spec (.of k)) := ⟨I.blowupToBase ≫ X ↘ Spec (.of k)⟩
  haveI : SmoothOfRelativeDimension 2 (I.blowup ↘ Spec (.of k)) :=
    smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hp
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsRegular X := IsRegular.of_smooth (X ↘ Spec (.of k))
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
    (X ↘ Spec (.of k)) 2).mp inferInstance).2 p hp
  let L := (canonicalBundle k X 2).tensorPow m
  let M := (canonicalBundle k I.blowup 2).tensorPow m
  have hM : LineBundleClass.mk M =
      LineBundleClass.pullback I.blowupToBase (LineBundleClass.mk L) *
        I.blowupExceptionalClass ^ m := by
    dsimp only [L, M]
    rw [LineBundleClass.mk_tensorPow, LineBundleClass.mk_tensorPow,
      mk_canonicalBundle_pointBlowup k hp, mul_pow, LineBundleClass.pullback_pow]
  -- The exceptional-twist comparison presents the same center as a residue-field kernel.
  have compare (J : X.IdealSheafData) (hJ : J = (X.fromSpecResidueField p).ker) :
      ∀ (N : InvertibleSheaf J.blowup),
        LineBundleClass.mk N = LineBundleClass.pullback J.blowupToBase (LineBundleClass.mk L) *
          J.blowupExceptionalClass ^ m →
        letI : J.blowup.Over (Spec (.of k)) := ⟨J.blowupToBase ≫ X ↘ Spec (.of k)⟩
        Cohomology L.obj 0 ≃ₗ[k] Cohomology N.obj 0 := by
    subst J
    intro N hN
    refine cohomologyZeroPointBlowupExceptionalTwistLinearEquiv p k hp hdim L m N ?_
    simpa only [blowupExceptionalClass_def, inv_pow, zpow_neg, zpow_natCast] using hN
  exact compare I (X.ker_fromSpecResidueField_eq_vanishingIdeal p).symm M hM

end AlgebraicGeometry.Scheme.IdealSheafData

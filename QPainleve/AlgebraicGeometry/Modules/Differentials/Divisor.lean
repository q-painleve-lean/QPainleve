/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import TauCeti.AlgebraicGeometry.CartierDivisor.IdealSheaf
import QPainleve.AlgebraicGeometry.CartierDivisor.Comparison
import QPainleve.AlgebraicGeometry.IdealSheaf.Image
import QPainleve.AlgebraicGeometry.IdealSheaf.Image.Pullback
import QPainleve.AlgebraicGeometry.LineBundle.ZeroLocus

/-!
# Divisors of pulled-back top forms

A top form with divisor `-D`, for an effective Cartier divisor `D`, is specified
by an isomorphism from the ideal of `D` to the canonical bundle. On the domain
where that ideal is the unit ideal, the form is the image of `1`.

After pullback, the same denominator maps into the source canonical bundle by
the given isomorphism followed by pullback on top differential forms. The
divisor of this fraction is the Cartier divisor of the numerator map minus
the total transform of the denominator.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme (CartierDivisor)

namespace QPainleve

universe u

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] (f : X ⟶ Y) [f.IsOver (Spec (.of R))]
  (n : ℕ) [SmoothOfRelativeDimension n (X ↘ Spec (.of R))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (.of R))]

/-- The numerator of the pullback of a top form with a specified Cartier denominator
has zero ideal equal to the ramification ideal. -/
theorem imageIdealSheaf_twistedToUnit_pullback_topForm
    {L : InvertibleSheaf Y} (e : L ≅ canonicalBundle R Y n) :
    letI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
    let F := InvertibleSheaf.pullback f
    ((F.obj L).twistedToUnit (canonicalBundle R X n)
      ((F.map e.hom).hom ≫ topDifferentialFormsMap R f n)).imageIdealSheaf =
        ramificationIdealSheaf R f := by
  let F := InvertibleSheaf.pullback f
  let e' := (SheafOfModules.isInvertible X).ι.mapIso (F.mapIso e)
  exact (InvertibleSheaf.imageIdealSheaf_twistedToUnit_comp_iso e'
    (topDifferentialFormsMap R f n)).trans
      (ramificationIdealSheaf_eq_imageIdealSheaf_topDifferentialFormsMap R f n).symm

variable [IsIntegral X] {D : Y.IdealSheafData}
  (hD : D.IsEffectiveCartier) (e : hD.toInvertibleSheaf ≅ canonicalBundle R Y n)
  (hTotal : (D.comap f).IsEffectiveCartier)

/-- The divisor of the pulled-back top form specified by `e`. Its numerator is the
pullback of `e` followed by the map on canonical bundles, and its denominator is
the pullback of the inclusion of the effective Cartier ideal `D`. -/
def pullbackTopFormDivisor
    (hRam : letI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
      (ramificationIdealSheaf R f).IsEffectiveCartier) :
    CartierDivisor X :=
  letI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
  let F := InvertibleSheaf.pullback f
  let numerator := ((F.obj hD.toInvertibleSheaf).twistedToUnit (canonicalBundle R X n)
    ((F.map e.hom).hom ≫ topDifferentialFormsMap R f n)).imageIdealSheaf
  let hNum : numerator.IsEffectiveCartier :=
    Eq.mpr (congrArg Scheme.IdealSheafData.IsEffectiveCartier
      (imageIdealSheaf_twistedToUnit_pullback_topForm R f n e)) hRam
  let denominator := ((Scheme.Modules.pullback f).map D.sheafι ≫
    (Scheme.Modules.pullbackObjUnitIso f).hom).imageIdealSheaf
  let hDen : denominator.IsEffectiveCartier := by
    dsimp only [denominator]
    rw [Scheme.Modules.Hom.imageIdealSheaf_pullback, D.imageIdealSheaf_sheafι]
    exact hTotal
  hNum.toCartierDivisor - hDen.toCartierDivisor

/-- The divisor of the pulled-back form is the ramification divisor minus the total
transform of its pole divisor. -/
theorem pullbackTopFormDivisor_eq_ramification_sub
    (hRam : letI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
      (ramificationIdealSheaf R f).IsEffectiveCartier) :
    pullbackTopFormDivisor R f n hD e hTotal hRam =
      hRam.toCartierDivisor - hTotal.toCartierDivisor := by
  dsimp only [pullbackTopFormDivisor]
  apply congrArg₂ (· - ·)
  · exact (Scheme.IdealSheafData.IsEffectiveCartier.toCartierDivisor_eq_iff _ _).mpr
      (imageIdealSheaf_twistedToUnit_pullback_topForm R f n e)
  · rw [Scheme.IdealSheafData.IsEffectiveCartier.toCartierDivisor_eq_iff,
      Scheme.Modules.Hom.imageIdealSheaf_pullback, D.imageIdealSheaf_sheafι]

/-- The pulled-back top form has no zeros precisely when the total-transform ideal
of its poles is contained in the ramification ideal. -/
theorem neg_pullbackTopFormDivisor_isEffective_iff
    (hRam : letI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
      (ramificationIdealSheaf R f).IsEffectiveCartier) :
    letI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
    (-(pullbackTopFormDivisor R f n hD e hTotal hRam)).IsEffective ↔
      D.comap f ≤ ramificationIdealSheaf R f := by
  rw [pullbackTopFormDivisor_eq_ramification_sub, neg_sub]
  exact (hTotal.le_iff_isEffective_sub hRam).symm

/-- The pullback has divisor `-P` precisely when its total-transform ideal is the
product of the pole ideal `P` and the ramification ideal. -/
theorem pullbackTopFormDivisor_eq_neg_iff {P : X.IdealSheafData} (hP : P.IsEffectiveCartier)
    (hRam : letI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
      (ramificationIdealSheaf R f).IsEffectiveCartier) :
    letI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
    pullbackTopFormDivisor R f n hD e hTotal hRam = -hP.toCartierDivisor ↔
      D.comap f = P * ramificationIdealSheaf R f := by
  rw [pullbackTopFormDivisor_eq_ramification_sub, ← neg_sub, neg_inj, sub_eq_iff_eq_add]
  rw [← Scheme.IdealSheafData.IsEffectiveCartier.toCartierDivisor_mul hP hRam]
  exact hTotal.toCartierDivisor_eq_iff (TauCeti.isEffectiveCartier_mul hP hRam)

end QPainleve

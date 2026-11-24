/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Modules.Differentials.Ramification
public import QPainleve.AlgebraicGeometry.CartierDivisor.Comparison

import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# Pole ideals under composition

For a top form with pole ideal `D` and no zeros, the pullback along `g` has pole
ideal `P` and no zeros when `D.comap g = P * ramificationIdealSheaf R g`.
The chain rule composes these factorizations. If `g` is one of two projections of
a link with the same pole ideal, the comparison allows either projection to
compute the pole ideal after further pullback. A modification also reflects the
factorization from its source to its target.

This is the pole comparison used for volume-preserving links in
[Lutz's appendix to Hacking and Keating, Definition 8.1][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public section

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [Z.Over (Spec (.of R))]
  (f : X ⟶ Y) (g : Y ⟶ Z) [f.IsOver (Spec (.of R))] [g.IsOver (Spec (.of R))]
  (n : ℕ) [SmoothOfRelativeDimension n (X ↘ Spec (.of R))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (.of R))]
  [SmoothOfRelativeDimension n (Z ↘ Spec (.of R))]

local notation "ram(" f ")" => ramificationIdealSheaf R f

variable {D : Z.IdealSheafData} {P : Y.IdealSheafData} {Q : X.IdealSheafData}

/-- Successive pole-ideal factorizations give the pole-ideal factorization for the
composite, with the ramification of both maps accounted for. -/
theorem comap_eq_mul_ramificationIdealSheaf_comp :
    letI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
    letI := SmoothOfRelativeDimension.smooth n (Y ↘ Spec (.of R))
    D.comap g = P * ram(g) → P.comap f = Q * ram(f) →
      D.comap (f ≫ g) = Q * ram(f ≫ g) := by
  have := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
  have := SmoothOfRelativeDimension.smooth n (Y ↘ Spec (.of R))
  intro hg hf
  rw [comap_comp, hg, comap_mul, hf, ramificationIdealSheaf_comp R f g n, mul_assoc]

/-- After a map with a specified pole ideal, computing the poles of a further pullback
can be done using that ideal on the intermediate model. -/
theorem comap_eq_mul_ramificationIdealSheaf_comp_iff :
    letI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
    letI := SmoothOfRelativeDimension.smooth n (Y ↘ Spec (.of R))
    ((ram(g)).comap f).IsEffectiveCartier → D.comap g = P * ram(g) →
      (D.comap (f ≫ g) = Q * ram(f ≫ g) ↔ P.comap f = Q * ram(f)) := by
  have := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
  have := SmoothOfRelativeDimension.smooth n (Y ↘ Spec (.of R))
  intro hCart hg
  refine ⟨fun h ↦ ?_, comap_eq_mul_ramificationIdealSheaf_comp R f g n hg⟩
  rw [comap_comp, hg, comap_mul, ramificationIdealSheaf_comp R f g n, ← mul_assoc] at h
  apply hCart.mul_left_cancel
  simpa only [mul_comm ((ram(g)).comap f)] using h

/-- If a modification pulls the intermediate pole ideal back to a specified pole ideal,
one can check the factorization for a map out of the intermediate scheme on the modified
source. Both sides of the equality on the intermediate scheme are effective Cartier. -/
theorem comap_eq_mul_ramificationIdealSheaf_comp_iff_of_isModification
    [IsReduced X] [IsIntegral Y] [IsNoetherian Y] [IsNormalScheme Y] [IsModification f]
    (hD : (D.comap g).IsEffectiveCartier) (hP : P.IsEffectiveCartier) :
    letI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
    letI := SmoothOfRelativeDimension.smooth n (Y ↘ Spec (.of R))
    (ram(g)).IsEffectiveCartier → P.comap f = Q * ram(f) →
      (D.comap (f ≫ g) = Q * ram(f ≫ g) ↔ D.comap g = P * ram(g)) := by
  have := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
  have := SmoothOfRelativeDimension.smooth n (Y ↘ Spec (.of R))
  intro hCart hf
  refine ⟨fun h ↦ ?_, fun hg ↦ comap_eq_mul_ramificationIdealSheaf_comp R f g n hg hf⟩
  have hEq : (D.comap g).comap f = (P * ram(g)).comap f := by
    rw [← comap_comp, h, comap_mul, hf, ramificationIdealSheaf_comp R f g n, mul_assoc]
  have hProd := TauCeti.isEffectiveCartier_mul hP hCart
  exact le_antisymm ((hD.comap_le_comap_iff_of_isModification f hProd).mp hEq.le)
    ((hProd.comap_le_comap_iff_of_isModification f hD).mp hEq.ge)

/-- If the projections of a resolved link have a common pole ideal, a prescribed pole
factorization along the first projection gives the same factorization along the second.
The pullback of the first ramification ideal is Cartier so it can be cancelled. -/
theorem comap_eq_mul_ramificationIdealSheaf_comp_of_common_poleIdeal
    {W : Scheme.{u}} [W.Over (Spec (.of R))]
    (g' : Y ⟶ W) [g'.IsOver (Spec (.of R))]
    [SmoothOfRelativeDimension n (W ↘ Spec (.of R))] {D' : W.IdealSheafData} :
    letI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
    letI := SmoothOfRelativeDimension.smooth n (Y ↘ Spec (.of R))
    ((ram(g)).comap f).IsEffectiveCartier → D.comap g = P * ram(g) →
    D'.comap g' = P * ram(g') → D.comap (f ≫ g) = Q * ram(f ≫ g) →
      D'.comap (f ≫ g') = Q * ram(f ≫ g') := by
  have := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
  have := SmoothOfRelativeDimension.smooth n (Y ↘ Spec (.of R))
  intro hCart hg hg' h
  exact comap_eq_mul_ramificationIdealSheaf_comp R f g' n hg'
    ((comap_eq_mul_ramificationIdealSheaf_comp_iff R f g n hCart hg).mp h)

end TauCeti.AlgebraicGeometry

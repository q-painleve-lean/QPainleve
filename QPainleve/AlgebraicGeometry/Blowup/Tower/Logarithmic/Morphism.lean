/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Factorization
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Divisor
public import TauCeti.AlgebraicGeometry.IdealSheaf.Colon
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction

/-!
# Pole ideals of factored birational morphisms

When a birational morphism of smooth projective surfaces pulls back a logarithmic
top form to a form with divisor `-P`, the point-blowup factorization of the
specified morphism has no zeros of the pulled-back form. On the final blowup,
the ideal obtained by dividing the total transform of the original poles by
ramification corresponds to the actual ideal of `P`. This is the input to
classifying the centers as smooth boundary points or nodes, as in
[Lutz's appendix to Hacking and Keating, Definition 8.1 and Theorem 8.4][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of k))]
  {D : Y.IdealSheafData} (hD : D.IsEffectiveCartier)
  (ω : hD.toInvertibleSheaf ≅ canonicalBundle k Y 2)
  {P : X.IdealSheafData} (hP : P.IsEffectiveCartier)
  (hTotal : (D.comap f).IsEffectiveCartier)
  (hRam : letI := SmoothOfRelativeDimension.smooth 2 (X ↘ Spec (.of k))
    (ramificationIdealSheaf k f).IsEffectiveCartier)

namespace QPainleve.BlowupTower.IsClosedPointTower

variable [PerfectField k] {Z : Scheme.{u}} {n : ℕ} {T : BlowupTower Y n Z}

/-- On any point-blowup factorization of the morphism, the formula `div(f*ω) = -P`
is equivalent to containment in the ramification ideal together with the exact
identification of the resulting pole ideal under the factorization isomorphism. -/
theorem pullbackTopFormDivisor_eq_neg_iff (hT : IsClosedPointTower Y T)
    (e : X ≅ Z) (he : e.hom ≫ T.toBase = f) :
    pullbackTopFormDivisor k f 2 hD ω hTotal hRam = -hP.toCartierDivisor ↔
      D.comap T.toBase ≤ hT.ramificationIdealSheafToBase k ∧
      ((D.comap T.toBase).colon (hT.ramificationIdealSheafToBase k)).comap e.hom = P := by
  have := SmoothOfRelativeDimension.smooth 2 (X ↘ Spec (.of k))
  have htotal : (D.comap T.toBase).comap e.hom = D.comap f := by
    rw [← comap_comp, he]
  have hram := hT.comap_ramificationIdealSheafToBase k e he
  let R := hT.ramificationIdealSheafToBase k
  let A := D.comap T.toBase
  have hbase : (R.comap e.hom).IsEffectiveCartier := hram.symm ▸ hRam
  have hR : R.IsEffectiveCartier := by
    simpa only [← comap_comp, Iso.inv_hom_id, comap_id] using hbase.comap e.inv
  rw [QPainleve.pullbackTopFormDivisor_eq_neg_iff k f 2 hD ω hTotal hP hRam,
    ← htotal, ← hram]
  constructor
  · intro h
    have hleX : A.comap e.hom ≤ R.comap e.hom := by
      rw [h]
      exact fun _ ↦ Ideal.mul_le_right
    have hle : A ≤ R := by
      simpa only [← comap_comp, Iso.inv_hom_id, comap_id] using comap_mono e.inv hleX
    exact ⟨hle, by rw [comap_colon A R hR.locallyPrincipal hle e.hom hbase, h,
      hbase.mul_colon_cancel_right]⟩
  · rintro ⟨hle, h⟩
    rw [← h, ← comap_mul, ← A.eq_colon_mul R hR.locallyPrincipal hle]

end QPainleve.BlowupTower.IsClosedPointTower

namespace AlgebraicGeometry.Scheme.Hom

variable [IsAlgClosed k] [IsIntegral Y] [X.IsProjectiveOver k] [Y.IsProjectiveOver k]

variable (f) in
/-- A specified birational morphism with pullback divisor `-P` factors into closed point
blowups. The factorization identifies `P` with the pole ideal on the final blowup, and
the total-transform ideal is contained in the ramification ideal. -/
theorem exists_isClosedPointTower_factorization_of_pullbackTopFormDivisor
    (hf : BirationalOver f (𝟙 Y))
    (hdiv : pullbackTopFormDivisor k f 2 hD ω hTotal hRam = -hP.toCartierDivisor) :
    ∃ (n : ℕ) (Z : Scheme.{u}) (T : BlowupTower Y n Z) (e : X ≅ Z)
      (hT : IsClosedPointTower Y T),
      e.hom ≫ T.toBase = f ∧
      D.comap T.toBase ≤ hT.ramificationIdealSheafToBase k ∧
      ((D.comap T.toBase).colon (hT.ramificationIdealSheafToBase k)).comap e.hom = P := by
  obtain ⟨n, Z, T, e, hT, he⟩ := f.exists_isClosedPointTower_factorization (k := k) hf
  exact ⟨n, Z, T, e, hT, he, (hT.pullbackTopFormDivisor_eq_neg_iff hD ω hP
    hTotal hRam e he).mp hdiv⟩

end AlgebraicGeometry.Scheme.Hom

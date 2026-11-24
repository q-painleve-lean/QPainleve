/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ample
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform
public import QPainleve.AlgebraicGeometry.Chow.SurfaceIntersection
public import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial

/-!
# Extending Picard isometries through point blowups

A Picard isometry between two smooth projective surfaces extends through equally long
ordered point-blowup towers by matching the total exceptional classes. This extension
carries the canonical class if the base isometry does, and matches strict-transform classes
exactly when their base classes and multiplicities at successive centers correspond.
If the base isometry matches a pair of ample classes, the extension does too.

For the extension along a boundary blowup, see the proof of Theorem 4.7 of
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*][GHK].

[GHK]: https://paulhacking.github.io/mlp.pdf#page=18
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open LineBundleClass

universe u

namespace QPainleve.BlowupTower

variable {X Y Z W : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y} {U : BlowupTower Z n W}
  (k : Type u) [Field k] [IsAlgClosed k]
  [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k))]
  [IsIntegral X] [IsIntegral Z] [X.IsProjectiveOver k] [Z.IsProjectiveOver k]
  (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Z U)

local notation "g(" k ", " S ")" => (S ↘ Spec (CommRingCat.of k))
local notation "Pic(" S ")" => Additive (LineBundleClass S)
local notation "B(" k ", " S ")" => Chow.intersectionBilinForm k S

/-- Extend a Picard isometry by matching the ordered total exceptional classes. The
towers may have infinitely near centers and the extension uses the entire Picard group. -/
def picardIsometryCongr (e : B(k, X).IsometryEquiv B(k, Z)) :
    let : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
    let : IsNoetherian Z := isNoetherian_of_finiteType (g(k, Z))
    let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ g(k, X)⟩
    let : W.Over (Spec (.of k)) := ⟨U.toBase ≫ g(k, Z)⟩
    let : Y.IsProjectiveOver k := T.isProjectiveOver k
    let : W.IsProjectiveOver k := U.isProjectiveOver k
    let : IsIntegral Y := hT.isIntegral (g(k, X))
    let : IsIntegral W := hU.isIntegral (g(k, Z))
    let : SmoothOfRelativeDimension 2 (g(k, Y)) := hT.smoothOfRelativeDimension (g(k, X))
    let : SmoothOfRelativeDimension 2 (g(k, W)) := hU.smoothOfRelativeDimension (g(k, Z))
    B(k, Y).IsometryEquiv B(k, W) := by
  intro _ _ _ _ _ _ _ _ _ _
  let mT := T.picardMarking hT (g(k, X))
  let mU := U.picardMarking hU (g(k, Z))
  let E := (e : Pic(X) ≃ₗ[ℤ] Pic(Z)).prodCongr (LinearEquiv.refl ℤ (Fin n → ℤ))
  refine { mT.symm.trans (E.trans mU) with map_app' := ?_ }
  intro a b
  obtain ⟨a, rfl⟩ := mT.surjective a
  obtain ⟨b, rfl⟩ := mT.surjective b
  simp only [LinearEquiv.toFun_eq_coe, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
    LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv,
    Chow.intersectionBilinForm_apply, mT, mU, E]
  rw [classIntersectionNumber_picardMarking k hU, classIntersectionNumber_picardMarking k hT]
  congr 1
  simpa only [Chow.intersectionBilinForm_apply] using e.map_app b.1 a.1

variable (e : B(k, X).IsometryEquiv B(k, Z))

/-- On marked coordinates the extension acts by the original isometry on the base
and fixes the integer coordinates of the exceptional classes. -/
@[simp]
theorem picardIsometryCongr_picardHom (a : Pic(X)) (b : Fin n → ℤ) :
    picardIsometryCongr k hT hU e (T.picardHom (a, b)) = U.picardHom (e a, b) := by
  have : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
  have : IsNoetherian Z := isNoetherian_of_finiteType (g(k, Z))
  rw [← picardMarking_apply T hT (g(k, X)), ← picardMarking_apply U hU (g(k, Z))]
  -- Project to the underlying linear equivalence to evaluate the composite.
  rw [← LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv]
  simp only [picardIsometryCongr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
    LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv]

/-- The extension intertwines pullbacks from the two base surfaces. -/
@[simp]
theorem picardIsometryCongr_pullback (a : LineBundleClass X) :
    picardIsometryCongr k hT hU e (Additive.ofMul (pullback T.toBase a)) =
      Additive.ofMul (pullback U.toBase (e (Additive.ofMul a)).toMul) := by
  have hp : T.picardHom (Additive.ofMul a, 0) = Additive.ofMul (pullback T.toBase a) :=
    Additive.toMul.injective (T.picardHom_apply_zero _)
  rw [← hp, picardIsometryCongr_picardHom]
  exact Additive.toMul.injective (U.picardHom_apply_zero _)

/-- Each total exceptional class is sent to the class from the same stage on the other side. -/
@[simp]
theorem picardIsometryCongr_exceptionalClass (j : Fin n) :
    picardIsometryCongr k hT hU e (Additive.ofMul (T.exceptionalClass j)) =
      Additive.ofMul (U.exceptionalClass j) := by
  classical
  have hp : T.picardHom (0, Pi.single j 1) = Additive.ofMul (T.exceptionalClass j) :=
    Additive.toMul.injective (by rw [picardHom_apply_single, zpow_one, toMul_ofMul])
  rw [← hp, picardIsometryCongr_picardHom, map_zero]
  exact Additive.toMul.injective (by rw [picardHom_apply_single, zpow_one, toMul_ofMul])

/-- The canonical classes on the final surfaces correspond if the canonical classes on
the base surfaces correspond. -/
theorem picardIsometryCongr_canonicalClass
    (he : e (Additive.ofMul (mk (canonicalBundle k X 2))) =
      Additive.ofMul (mk (canonicalBundle k Z 2))) :
    letI : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ g(k, X)⟩
    letI : W.Over (Spec (.of k)) := ⟨U.toBase ≫ g(k, Z)⟩
    let : SmoothOfRelativeDimension 2 (g(k, Y)) := hT.smoothOfRelativeDimension (g(k, X))
    let : SmoothOfRelativeDimension 2 (g(k, W)) := hU.smoothOfRelativeDimension (g(k, Z))
    picardIsometryCongr k hT hU e (Additive.ofMul (mk (canonicalBundle k Y 2))) =
      Additive.ofMul (mk (canonicalBundle k W 2)) := by
  have : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
  have : IsNoetherian Z := isNoetherian_of_finiteType (g(k, Z))
  let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ g(k, X)⟩
  let : W.Over (Spec (.of k)) := ⟨U.toBase ≫ g(k, Z)⟩
  let : SmoothOfRelativeDimension 2 (g(k, Y)) := hT.smoothOfRelativeDimension (g(k, X))
  let : SmoothOfRelativeDimension 2 (g(k, W)) := hU.smoothOfRelativeDimension (g(k, Z))
  dsimp only
  rw [← picardMarking_canonicalClass k hT, ← picardMarking_canonicalClass k hU,
    picardMarking_apply, picardMarking_apply, picardIsometryCongr_picardHom, he]

local notation "classOf(" h ")" =>
  Additive.ofMul (mk (Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf h))⁻¹

/-- The extended isometry matches strict-transform classes exactly when the original
classes correspond and the strict transforms have the same orders at successive centers. -/
theorem picardIsometryCongr_strictTransform_eq_iff
    {D : X.IdealSheafData} {F : Z.IdealSheafData}
    (hD : D.IsEffectiveCartier) (hF : F.IsEffectiveCartier) :
    let : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
    let : IsNoetherian Z := isNoetherian_of_finiteType (g(k, Z))
    picardIsometryCongr k hT hU e classOf(hT.isEffectiveCartier_strictTransform (g(k, X)) hD) =
      classOf(hU.isEffectiveCartier_strictTransform (g(k, Z)) hF) ↔
      e classOf(hD) = classOf(hF) ∧
        hT.strictTransformCoefficients D = hU.strictTransformCoefficients F := by
  have : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
  have : IsNoetherian Z := isNoetherian_of_finiteType (g(k, Z))
  dsimp only
  rw [← hT.picardMarking_strictTransform (g(k, X)) hD,
    ← hU.picardMarking_strictTransform (g(k, Z)) hF, picardMarking_apply, picardMarking_apply,
    picardIsometryCongr_picardHom, (hU.bijective_picardHom (g(k, Z))).injective.eq_iff,
    Prod.mk.injEq]

/-- An isometry matching a pair of ample base classes still matches a pair of ample
classes after extension through ordered point-blowup towers. -/
theorem exists_isAmple_picardIsometryCongr {H : LineBundleClass X} (hH : H.IsAmple)
    (he : (e (Additive.ofMul H)).toMul.IsAmple) :
    ∃ A : LineBundleClass Y, A.IsAmple ∧
      (picardIsometryCongr k hT hU e (Additive.ofMul A)).toMul.IsAmple := by
  have : IsNoetherian X := isNoetherian_of_finiteType (g(k, X))
  have : IsNoetherian Z := isNoetherian_of_finiteType (g(k, Z))
  obtain ⟨N, b, _, _, hA, hB⟩ := exists_isAmple_picardHom hH he T U
  refine ⟨_, hA, ?_⟩
  rw [ofMul_toMul, picardIsometryCongr_picardHom]
  simpa only [ofMul_pow, ofMul_toMul, map_nsmul] using hB

end QPainleve.BlowupTower

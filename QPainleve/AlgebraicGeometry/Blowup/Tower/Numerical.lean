/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
public import QPainleve.AlgebraicGeometry.Chow.SurfaceIntersection

import QPainleve.AlgebraicGeometry.Chow.Isomorphism
import QPainleve.LinearAlgebra.BilinearForm.Prod
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import TauCeti.LinearAlgebra.FreeModule.PID
import TauCeti.LinearAlgebra.Matrix.Dual
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Numerical invariants from a common point-blowup resolution

The Picard markings of two point-blowup towers with isomorphic final schemes give a stable
isometry of the base pairings. The added summands are negative unit forms, one per point
blowup. This compares finiteness, freeness, and unimodularity of the Picard groups of the
base surfaces. The rank difference cancels the difference of canonical self-intersections.

The surface computations use the point-blowup formulas of
[Hacking, *Compact Complex Surfaces*, Propositions 7.1 and 7.2][Hacking].

[Hacking]: https://paulhacking.github.io/surfaces.pdf#page=34
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti TauCeti.AlgebraicGeometry
open LineBundleClass

universe u

namespace QPainleve.BlowupTower

local notation "Pic(" S ")" => Additive (LineBundleClass S)

variable {X Y Z W : Scheme.{u}} {m n : ℕ}
  {T : BlowupTower X m Y} {U : BlowupTower Z n W}
  (k : Type u) [Field k] [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k))]
  [IsIntegral X] [IsIntegral Z]

local notation "fX" => (X ↘ Spec (CommRingCat.of k))
local notation "fZ" => (Z ↘ Spec (CommRingCat.of k))

section PerfectField

variable [PerfectField k] [IsNoetherian X] [IsNoetherian Z]

/-- The two Picard markings on a common resolution identify the base Picard groups after
adding one integral coordinate for each point blowup on the respective side. -/
noncomputable def picardEquivOfCommonResolution
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Z U) (e : W ≅ Y) :
    (Pic(X) × (Fin m → ℤ)) ≃ₗ[ℤ] (Pic(Z) × (Fin n → ℤ)) :=
  (T.picardMarking hT fX).trans
    (((LineBundleClass.pullbackEquiv e).toAdditive.toIntLinearEquiv).trans
      (U.picardMarking hU fZ).symm)

/-- On the common resolution, the identification of Picard coordinates is pullback
along the isomorphism of the final schemes. -/
@[simp]
theorem picardHom_picardEquivOfCommonResolution
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Z U) (e : W ≅ Y)
    (a : Pic(X) × (Fin m → ℤ)) :
    U.picardHom (picardEquivOfCommonResolution k hT hU e a) =
      Additive.ofMul (LineBundleClass.pullback e.hom (T.picardHom a).toMul) := by
  rw [← U.picardMarking_apply hU fZ, ← T.picardMarking_apply hT fX]
  simp [picardEquivOfCommonResolution, LineBundleClass.pullbackEquiv_apply]

include k in
/-- Finite generation of the integral Picard group transfers across a common
resolution by towers of closed point blowups. -/
theorem finite_picard_iff_of_common_resolution
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Z U) (e : W ≅ Y) :
    Module.Finite ℤ (Pic(X)) ↔ Module.Finite ℤ (Pic(Z)) := by
  let E := picardEquivOfCommonResolution k hT hU e
  exact ⟨fun _ ↦ Module.Finite.of_surjective ((LinearMap.fst ℤ _ _).comp E.toLinearMap)
    ((LinearMap.fst_surjective (R := ℤ)).comp E.surjective),
    fun _ ↦ Module.Finite.of_surjective ((LinearMap.fst ℤ _ _).comp E.symm.toLinearMap)
      ((LinearMap.fst_surjective (R := ℤ)).comp E.symm.surjective)⟩

include k in
/-- Freeness of the integral Picard group transfers across a common resolution
by towers of closed point blowups. -/
theorem free_picard_iff_of_common_resolution
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Z U) (e : W ≅ Y) :
    Module.Free ℤ (Pic(X)) ↔ Module.Free ℤ (Pic(Z)) := by
  let E := picardEquivOfCommonResolution k hT hU e
  exact ⟨fun _ ↦ Module.Free.of_injective_of_projective_of_isPrincipalIdealRing
    (E.symm.toLinearMap.comp (LinearMap.inl ℤ _ _))
    (E.symm.injective.comp LinearMap.inl_injective),
    fun _ ↦ Module.Free.of_injective_of_projective_of_isPrincipalIdealRing
      (E.toLinearMap.comp (LinearMap.inl ℤ _ _))
      (E.injective.comp LinearMap.inl_injective)⟩

include k in
/-- For a finite free Picard group, its rank increases by the length of a tower
of closed point blowups. -/
theorem finrank_picard [Module.Finite ℤ (Pic(X))] [Module.Free ℤ (Pic(X))]
    (hT : IsClosedPointTower X T) :
    Module.finrank ℤ (Pic(Y)) = Module.finrank ℤ (Pic(X)) + m := by
  rw [← (T.picardMarking hT fX).finrank_eq, Module.finrank_prod]
  simp

end PerfectField

section AlgebraicallyClosed

variable [IsAlgClosed k] [X.IsProjectiveOver k] [Z.IsProjectiveOver k]
  (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Z U) (e : W ≅ Y)
  (he : e.hom ≫ T.toBase ≫ (X ↘ Spec (.of k)) = U.toBase ≫ (Z ↘ Spec (.of k)))

include he in
/-- The stabilized Picard pairing on either side of a common resolution is the same
under the equivalence induced by the point-blowup markings. -/
theorem classIntersectionNumber_picardEquivOfCommonResolution
    (a b : Pic(X) × (Fin m → ℤ)) :
    let : IsNoetherian X := isNoetherian_of_finiteType fX
    let : IsNoetherian Z := isNoetherian_of_finiteType fZ
    let a' := picardEquivOfCommonResolution k hT hU e a
    let b' := picardEquivOfCommonResolution k hT hU e b
    Chow.classIntersectionNumber k Z a'.1.toMul b'.1.toMul - ∑ j, a'.2 j * b'.2 j =
      Chow.classIntersectionNumber k X a.1.toMul b.1.toMul - ∑ j, a.2 j * b.2 j := by
  let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ fX⟩
  let : W.Over (Spec (.of k)) := ⟨U.toBase ≫ fZ⟩
  have : e.hom.IsOver (Spec (.of k)) := ⟨he⟩
  dsimp only
  have : IsNoetherian X := isNoetherian_of_finiteType fX
  have : IsNoetherian Z := isNoetherian_of_finiteType fZ
  rw [← classIntersectionNumber_picardMarking k hU,
    ← classIntersectionNumber_picardMarking k hT]
  simpa only [picardMarking_apply, picardHom_picardEquivOfCommonResolution, toMul_ofMul] using
    Chow.classIntersectionNumber_pullback_of_isIso k e.hom
      (T.picardMarking hT fX a).toMul (T.picardMarking hT fX b).toMul

local notation "B₂(" S ")" => Chow.classIntersectionBilinForm k
  (topologicalKrullDim_eq_of_smoothOfRelativeDimension (S ↘ Spec (CommRingCat.of k)) (n := 2))

local notation "negDot(" d ")" =>
  LinearMap.compl₁₂ (dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin d → ℤ))
    (LinearEquiv.toLinearMap (LinearEquiv.neg ℤ (M := Fin d → ℤ)))
    (LinearEquiv.toLinearMap (LinearEquiv.refl ℤ (Fin d → ℤ)))

include hT hU e he in
/-- Unimodularity of the integral Picard pairing transfers across a common resolution
of smooth integral projective surfaces by towers of closed point blowups. -/
theorem isPerfPair_classIntersectionBilinForm_iff_of_common_resolution :
    let : Smooth fX := SmoothOfRelativeDimension.smooth 2 fX
    let : Smooth fZ := SmoothOfRelativeDimension.smooth 2 fZ
    let : IsRegular X := IsRegular.of_smooth fX
    let : IsRegular Z := IsRegular.of_smooth fZ
    let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      fun x ↦ IsRegular.uniqueFactorizationMonoid_stalk x
        (WithBot.coe_le_coe.mp ((coheight_le_topologicalKrullDim x).trans_eq
          (topologicalKrullDim_eq_of_smoothOfRelativeDimension fX (n := 2))))
    let : ∀ z : Z, UniqueFactorizationMonoid (Z.presheaf.stalk z) :=
      fun z ↦ IsRegular.uniqueFactorizationMonoid_stalk z
        (WithBot.coe_le_coe.mp ((coheight_le_topologicalKrullDim z).trans_eq
          (topologicalKrullDim_eq_of_smoothOfRelativeDimension fZ (n := 2))))
    B₂(X).IsPerfPair ↔ B₂(Z).IsPerfPair := by
  intro _ _ _ _ _ _
  have : IsNoetherian X := isNoetherian_of_finiteType fX
  have : IsNoetherian Z := isNoetherian_of_finiteType fZ
  let E := picardEquivOfCommonResolution k hT hU e
  let B := B₂(X).prod negDot(m)
  let C := B₂(Z).prod negDot(n)
  have hE : C.compl₁₂ E E = B := by
    apply LinearMap.ext₂
    intro a b
    simpa only [B, C, E, LinearMap.compl₁₂_apply, LinearMap.BilinForm.prod_apply,
      Chow.classIntersectionBilinForm_apply, LinearEquiv.coe_coe, LinearEquiv.neg_apply,
      LinearEquiv.refl_apply, LinearMap.map_neg₂, dotProductBilin_apply_apply,
      dotProduct, sub_eq_add_neg] using
      classIntersectionNumber_picardEquivOfCommonResolution k hT hU e he a b
  have hPerf : B.IsPerfPair ↔ C.IsPerfPair :=
    ⟨fun _ ↦ LinearMap.IsPerfPair.congr _ E.symm E.symm _
      (by simpa only [LinearEquiv.symm_symm] using hE),
      fun _ ↦ hE ▸ LinearMap.IsPerfPair.compl₁₂ C E E⟩
  have hn (d : ℕ) : negDot(d).IsPerfPair := inferInstance
  simpa only [B, C, LinearMap.BilinForm.isPerfPair_prod_iff, hn, and_true] using hPerf

include hT hU e he in
/-- Along two point-blowup towers with isomorphic final schemes over the base field,
the sum of the Picard rank and the square of the canonical class agrees on the two
base surfaces. -/
theorem finrank_picard_add_canonical_square_of_common_resolution
    [Module.Finite ℤ (Pic(X))] [Module.Free ℤ (Pic(X))] :
    (Module.finrank ℤ (Pic(X)) : ℤ) +
        Chow.classIntersectionNumber k X (mk (canonicalBundle k X 2)) (mk (canonicalBundle k X 2)) =
      (Module.finrank ℤ (Pic(Z)) : ℤ) +
        Chow.classIntersectionNumber k Z (mk (canonicalBundle k Z 2))
          (mk (canonicalBundle k Z 2)) := by
  have : IsNoetherian X := isNoetherian_of_finiteType fX
  have : IsNoetherian Z := isNoetherian_of_finiteType fZ
  have : Module.Free ℤ (Pic(Z)) := (free_picard_iff_of_common_resolution k hT hU e).mp ‹_›
  have : Module.Finite ℤ (Pic(Z)) := (finite_picard_iff_of_common_resolution k hT hU e).mp ‹_›
  let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ fX⟩
  let : W.Over (Spec (.of k)) := ⟨U.toBase ≫ fZ⟩
  have : e.hom.IsOver (Spec (.of k)) := ⟨he⟩
  have : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) := hT.smoothOfRelativeDimension fX
  have : SmoothOfRelativeDimension 2 (W ↘ Spec (.of k)) := hU.smoothOfRelativeDimension fZ
  have hc := Chow.classIntersectionNumber_pullback_of_isIso k e.hom
    (mk (canonicalBundle k Y 2)) (mk (canonicalBundle k Y 2))
  rw [LineBundleClass.pullback_mk, LineBundleClass.mk_pullback_canonicalBundle,
    classIntersectionNumber_canonicalBundle k hU,
    classIntersectionNumber_canonicalBundle k hT] at hc
  have hr := ((LineBundleClass.pullbackEquiv e).toAdditive.toIntLinearEquiv).finrank_eq
  rw [finrank_picard k hT, finrank_picard k hU] at hr
  omega

end AlgebraicallyClosed

end QPainleve.BlowupTower

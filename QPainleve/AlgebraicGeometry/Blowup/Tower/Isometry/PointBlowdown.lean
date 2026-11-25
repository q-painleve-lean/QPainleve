/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Isometry.Descent

import QPainleve.AlgebraicGeometry.Chow.Isomorphism
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic

/-!
# Picard descent along specified point blowdowns

When two surfaces are identified with closed-point blowups over the ground field,
an isometry of their Picard groups that matches the exceptional classes descends
to the specified bases. The descended isometry intertwines pullback along the
actual blowdown morphisms. This uses the ordered exceptional-coordinate criterion
`existsUnique_picardIsometryCongr_eq`.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open LineBundleClass LinearMap.BilinForm

universe u

namespace QPainleve.BlowupTower

local notation "S(" k ")" => Spec (CommRingCat.of k)
local notation "g(" k ", " X ")" => (X ↘ S(k))
local notation "B(" k ", " X ")" => Chow.intersectionBilinForm k X
local notation "I(" p ")" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ p)

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y Z W : Scheme.{u}}
  [X.Over S(k)] [Y.Over S(k)] [Z.Over S(k)] [W.Over S(k)]
  [X.IsProjectiveOver k] [Y.IsProjectiveOver k] [Z.IsProjectiveOver k] [W.IsProjectiveOver k]
  [IsIntegral X] [IsIntegral Y] [IsIntegral Z] [IsIntegral W]
  [SmoothOfRelativeDimension 2 g(k, X)] [SmoothOfRelativeDimension 2 g(k, Y)]
  [SmoothOfRelativeDimension 2 g(k, Z)] [SmoothOfRelativeDimension 2 g(k, W)]

/-- An isometry matching the exceptional classes of two specified closed-point blowdowns
induces the unique isometry of the base Picard groups compatible with pullback. -/
theorem existsUnique_picardIsometry_of_pointBlowdowns {p : X} {q : Z}
    (hp : IsClosed ({p} : Set X)) (hq : IsClosed ({q} : Set Z))
    (a : Y ≅ (I(p)).blowup) (b : W ≅ (I(q)).blowup)
    {f : Y ⟶ X} {h : W ⟶ Z} [f.IsOver S(k)] [h.IsOver S(k)]
    (ha : a.hom ≫ (I(p)).blowupToBase = f) (hb : b.hom ≫ (I(q)).blowupToBase = h)
    (e : B(k, Y).IsometryEquiv B(k, W))
    (he : e (Additive.ofMul (pullback a.hom (I(p)).blowupExceptionalClass)) =
      Additive.ofMul (pullback b.hom (I(q)).blowupExceptionalClass)) :
    ∃! e₀ : B(k, X).IsometryEquiv B(k, Z),
      ∀ c : Additive (LineBundleClass X),
        e (Additive.ofMul (pullback f c.toMul)) =
          Additive.ofMul (pullback h (e₀ c).toMul) := by
  let T := (BlowupTower.nil (X := X)).snoc (I(p))
  let U := (BlowupTower.nil (X := Z)).snoc (I(q))
  let hT : T.IsClosedPointTower X := .snoc .nil p hp rfl
  let hU : U.IsClosedPointTower Z := .snoc .nil q hq rfl
  have hTa : a.hom ≫ T.toBase = f := by simpa only [T, toBase_snoc, toBase_nil, Category.comp_id]
    using ha
  have hUb : b.hom ≫ U.toBase = h := by simpa only [U, toBase_snoc, toBase_nil, Category.comp_id]
    using hb
  let : IsNoetherian X := isNoetherian_of_finiteType g(k, X)
  let : IsNoetherian Z := isNoetherian_of_finiteType g(k, Z)
  let : (I(p)).blowup.Over S(k) := ⟨T.toBase ≫ g(k, X)⟩
  let : (I(q)).blowup.Over S(k) := ⟨U.toBase ≫ g(k, Z)⟩
  let : (I(p)).blowup.IsProjectiveOver k := T.isProjectiveOver k
  let : (I(q)).blowup.IsProjectiveOver k := U.isProjectiveOver k
  let : IsIntegral (I(p)).blowup := hT.isIntegral g(k, X)
  let : IsIntegral (I(q)).blowup := hU.isIntegral g(k, Z)
  let : SmoothOfRelativeDimension 2 g(k, (I(p)).blowup) := hT.smoothOfRelativeDimension g(k, X)
  let : SmoothOfRelativeDimension 2 g(k, (I(q)).blowup) := hU.smoothOfRelativeDimension g(k, Z)
  let : a.hom.IsOver S(k) := ⟨by
    -- The structure map of the blowup is the tower projection followed by the base map.
    change a.hom ≫ T.toBase ≫ g(k, X) = _
    rw [← Category.assoc, hTa, comp_over]⟩
  let : b.hom.IsOver S(k) := ⟨by
    change b.hom ≫ U.toBase ≫ g(k, Z) = _
    rw [← Category.assoc, hUb, comp_over]⟩
  let A := Chow.picardPullbackIsometry k a
  let C := Chow.picardPullbackIsometry k b
  let E := (A.trans e).trans C.symm
  have hE (c : Additive (LineBundleClass (I(p)).blowup)) : C (E c) = e (A c) := by
    have h : E c = C.symm (e (A c)) :=
      (LinearMap.BilinForm.IsometryEquiv.trans_apply (A.trans e) C.symm c).trans
        (congrArg C.symm (LinearMap.BilinForm.IsometryEquiv.trans_apply A e c))
    exact (congrArg C h).trans (LinearMap.BilinForm.IsometryEquiv.apply_symm_apply C _)
  obtain ⟨e₀, he₀, -⟩ := (existsUnique_picardIsometryCongr_eq hT hU E).mpr (by
    intro j
    have hj : j = Fin.last 0 := Fin.ext (by omega)
    subst j
    apply (show Function.Injective C from C.injective)
    rw [hE]
    simpa only [A, C, Chow.picardPullbackIsometry_apply, T, U, exceptionalClass_snoc_last,
      ← Scheme.IdealSheafData.blowupExceptionalClass_def, toMul_ofMul] using he)
  have hpull (c : Additive (LineBundleClass X)) :
      e (Additive.ofMul (pullback f c.toMul)) =
        Additive.ofMul (pullback h (e₀ c).toMul) := by
    have hc := congrArg C (DFunLike.congr_fun he₀ (Additive.ofMul (pullback T.toBase c.toMul)))
    simpa only [picardIsometryCongr_pullback, ofMul_toMul, hE, A, C,
      Chow.picardPullbackIsometry_apply, toMul_ofMul,
      pullback_comp, hTa, hUb] using hc.symm
  refine ⟨e₀, hpull, fun e₁ he₁ ↦ DFunLike.ext _ _ fun c ↦ ?_⟩
  apply Additive.toMul.injective
  apply hU.injective_pullback_toBase g(k, Z)
  apply (pullbackEquiv b).injective
  simpa only [pullbackEquiv_apply, pullback_comp, hUb, toMul_ofMul] using
    congrArg Additive.toMul ((he₁ c).symm.trans (hpull c))

end QPainleve.BlowupTower

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Reframe

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic

/-!
# Changing the target lattice of a resolved Sarkisov path

Appending the inverse frame change to a resolved path recovers the specified
rational map to the original target, including after a refinement of the
resolving surface.

The toric change of target is used in the proof of [Lutz's Theorem 8.4][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.LogarithmicProjection

variable {N V N' V' : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Φ "]" => Fan.algebraicRealization Φ

section Factorization

open scoped Sarkisov

variable {Z W : Scheme} [Z.Over S] [W.Over S]
  [SmoothOfRelativeDimension 2 (Z ↘ S)] [SmoothOfRelativeDimension 2 (W ↘ S)]
  [IsIntegral W] {D : Z.IdealSheafData} {E : W.IdealSheafData}
  {A C : LogarithmicProjection i E} {B : LogarithmicProjection i' D}

/-- A resolved path to a reframed target followed by the inverse change of frame
realizes the specified rational map to the original target exactly when its
composite with the refined source projection gives the refined target projection.
The intermediate links of the path and the last toric isomorphism are resolved on
the same surface. -/
theorem SarkisovPath.rationalMap_comp_reframed_target_eq_iff (p : SarkisovPath A C)
    (L : LogarithmicProjection i D) (e : FanEquiv L.fan B.fan)
    (he : L.hom ≫ e.toFanHom.algebraicMap = B.hom) (f : W ⟶ Z)
    (hC : C.fan = L.fan) (hHom : C.hom ≍ f ≫ L.hom) (φ : X[A.fan] ⤏ X[B.fan]) :
    let e' : FanEquiv C.fan B.fan := hC.symm ▸ e
    p.rationalMap.compHom e'.toFanHom.algebraicMap = φ ↔
      A.hom.toRationalMap.comp φ = (f ≫ B.hom).toRationalMap := by
  intro e'
  have hEnd : C.hom ≫ e'.toFanHom.algebraicMap = f ≫ B.hom := by
    rcases C with ⟨Θ, hreg, hc, g, hg, hdom, hp⟩
    dsimp only at hC hHom ⊢
    subst Θ
    rw [eq_of_heq hHom, Category.assoc, he]
  have hcomp : A.hom.toRationalMap.comp (p.rationalMap.compHom e'.toFanHom.algebraicMap) =
      (f ≫ B.hom).toRationalMap := by
    rw [Scheme.RationalMap.comp_compHom, p.comp_rationalMap,
      Scheme.Hom.toRationalMap_compHom, hEnd]
  exact ⟨fun h ↦ h ▸ hcomp,
    fun h ↦ A.hom.toRationalMap.comp_left_injective (hcomp.trans h.symm)⟩

end Factorization

end TauCeti.Toric.Fan.LogarithmicProjection

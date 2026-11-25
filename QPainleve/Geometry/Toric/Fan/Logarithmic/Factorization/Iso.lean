/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization

import QPainleve.AlgebraicGeometry.Modules.Differentials.PoleIdeal

/-!
# Changing the resolving surface of a Sarkisov path

An isomorphism of resolving surfaces which identifies their pole ideals
transports the regular projections and every resolved link.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.LogarithmicProjection

local notation "S" => Spec (CommRingCat.of ℂ)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X W : Scheme} [X.Over S] [W.Over S]
  [SmoothOfRelativeDimension 2 (X ↘ S)] [SmoothOfRelativeDimension 2 (W ↘ S)]
  {D : X.IdealSheafData} {E : W.IdealSheafData}

/-- If a logarithmic projection factors through an isomorphism of resolving surfaces,
its pole ideal on the new source is the pullback along the inverse isomorphism. -/
theorem comap_boundaryIdeal_of_eq_iso_comp (A : LogarithmicProjection i D)
    (hRank : finrank ℤ N = 2) (k : X ≅ W) [k.hom.IsOver S]
    {Φ : Fan i} (hc : Φ.IsComplete) (p : W ⟶ Φ.algebraicRealization) [p.IsOver S]
    (hfan : A.fan = Φ) (hhom : A.hom ≍ k.hom ≫ p) :
    letI : Smooth (W ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    (Φ.boundaryIdeal hc.nonempty_cones).comap p =
      D.comap k.inv * ramificationIdealSheaf ℂ p := by
  subst Φ
  let : SmoothOfRelativeDimension 2 (A.fan.algebraicRealization ↘ S) :=
    hRank ▸ A.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap A.isRegular
  let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have heq := eq_of_heq hhom
  have h := comap_eq_mul_ramificationIdealSheaf_comp_iff_of_isIso ℂ k.hom p 2
    (D := A.fan.boundaryIdeal hc.nonempty_cones) (Q := D)
  rw [IsIso.inv_eq_of_hom_inv_id k.hom_inv_id] at h
  exact h.mp ((congrArg (A.fan.boundaryIdeal hc.nonempty_cones).comap heq).symm.trans
    (A.comap_boundaryIdeal.trans (congrArg (D * ·) (ramificationIdealSheaf_congr ℂ heq))))

variable [PreirreducibleSpace X] [PreirreducibleSpace W]

local notation "obj[" F "," A "]" => @Prefunctor.obj _ sarkisovQuiver _ sarkisovQuiver F A

/-- Precompose a resolved path by an isomorphism of resolving surfaces identifying
their pole ideals. Each link keeps its rational map between the toric targets. -/
def precomposeSarkisovOfIso (hRank : finrank ℤ N = 2) (k : W ≅ X)
    [k.hom.IsOver S] (hD : D.comap k.hom = E) :
    @Prefunctor (LogarithmicProjection i D) sarkisovQuiver
      (LogarithmicProjection i E) sarkisovQuiver :=
  precomposeSarkisov hRank k.hom (by
    let : Smooth (W ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    rw [ramificationIdealSheaf_eq_top_of_isOpenImmersion, mul_top, hD])

/-- The fan is preserved by precomposition with an isomorphism. -/
@[simp]
theorem precomposeSarkisovOfIso_obj_fan (hRank : finrank ℤ N = 2) (k : W ≅ X)
    [k.hom.IsOver S] (hD : D.comap k.hom = E) (A : LogarithmicProjection i D) :
    (obj[precomposeSarkisovOfIso hRank k hD,A]).fan = A.fan :=
  precomposeSarkisov_obj_fan ..

/-- A projection after precomposition with an isomorphism. -/
theorem precomposeSarkisovOfIso_obj_hom (hRank : finrank ℤ N = 2) (k : W ≅ X)
    [k.hom.IsOver S] (hD : D.comap k.hom = E) (A : LogarithmicProjection i D) :
    (obj[precomposeSarkisovOfIso hRank k hD,A]).hom ≍ k.hom ≫ A.hom :=
  precomposeSarkisov_obj_hom ..

/-- If a projection is already written using the inverse isomorphism,
precomposition cancels it. -/
theorem precomposeSarkisovOfIso_obj_hom_of_comp (hRank : finrank ℤ N = 2) (k : W ≅ X)
    [k.hom.IsOver S] (hD : D.comap k.hom = E) (A : LogarithmicProjection i D)
    {Φ : Fan i} {p : W ⟶ Φ.algebraicRealization} (hfan : A.fan = Φ)
    (hhom : A.hom ≍ k.inv ≫ p) :
    (obj[precomposeSarkisovOfIso hRank k hD,A]).hom ≍ p := by
  have h := (precomposeSarkisovOfIso_obj_hom hRank k hD A).trans
    (heq_comp rfl rfl (congrArg Fan.algebraicRealization hfan) HEq.rfl hhom)
  simpa only [Iso.hom_inv_id_assoc] using h

/-- The isomorphism on the resolving surface preserves each link's rational map. -/
theorem precomposeSarkisovOfIso_map_rationalMap (hRank : finrank ℤ N = 2) (k : W ≅ X)
    [k.hom.IsOver S] (hD : D.comap k.hom = E) {A B : LogarithmicProjection i D}
    (e : SarkisovStep A B) :
    (@Prefunctor.map _ sarkisovQuiver _ sarkisovQuiver
      (precomposeSarkisovOfIso hRank k hD) _ _ e).rationalMap ≍ e.rationalMap :=
  precomposeSarkisov_map_rationalMap ..

/-- Pulling back the projection by an isomorphism and then its inverse recovers
the given projection. -/
@[simp]
theorem precomposeSarkisovOfIso_obj_symm (hRank : finrank ℤ N = 2) (k : W ≅ X)
    [k.hom.IsOver S] [k.symm.hom.IsOver S] (hD : D.comap k.hom = E)
    (hE : E.comap k.inv = D) (A : LogarithmicProjection i D) :
    obj[precomposeSarkisovOfIso hRank k.symm hE,obj[precomposeSarkisovOfIso hRank k hD,A]] = A := by
  refine LogarithmicProjection.ext (by simp) ?_
  exact precomposeSarkisovOfIso_obj_hom_of_comp hRank k.symm hE _
    (precomposeSarkisovOfIso_obj_fan ..) (precomposeSarkisovOfIso_obj_hom hRank k hD A)

end TauCeti.Toric.Fan.LogarithmicProjection

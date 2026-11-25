/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization

import Mathlib.Combinatorics.Quiver.Cast
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
  [PreirreducibleSpace X] [PreirreducibleSpace W]
  {D : X.IdealSheafData} {E : W.IdealSheafData}

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

open scoped Sarkisov in
/-- Transport a Sarkisov path along an isomorphism of resolving surfaces.
If the prescribed starting projection agrees with the transported source,
the path starts there and ends at the precomposition of the original target. -/
theorem exists_path_on_resolving_surface {A : LogarithmicProjection i D}
    {Y : Scheme} [Y.Over S] [SmoothOfRelativeDimension 2 (Y ↘ S)] [PreirreducibleSpace Y]
    (hRank : finrank ℤ N = 2) (k : X ≅ Y) [k.hom.IsOver S]
    {L R : LogarithmicProjection i (D.comap k.inv)}
    (hFan : L.fan = A.fan) (hHom : A.hom ≍ k.hom ≫ L.hom)
    (p : SarkisovPath L R) :
    ∃ C : LogarithmicProjection i D, Nonempty (SarkisovPath A C) ∧
      C.fan = R.fan ∧ C.hom ≍ k.hom ≫ R.hom := by
  have hE : (D.comap k.inv).comap k.hom = D := by simp [← comap_comp]
  let G := precomposeSarkisovOfIso (i := i) hRank k hE
  have hSrc : obj[G,L] = A := LogarithmicProjection.ext
    ((precomposeSarkisovOfIso_obj_fan hRank k hE L).trans hFan)
    ((precomposeSarkisovOfIso_obj_hom hRank k hE L).trans hHom.symm)
  exact ⟨obj[G,R], ⟨(G.mapPath p).cast hSrc rfl⟩,
    precomposeSarkisovOfIso_obj_fan hRank k hE R, precomposeSarkisovOfIso_obj_hom hRank k hE R⟩

end TauCeti.Toric.Fan.LogarithmicProjection

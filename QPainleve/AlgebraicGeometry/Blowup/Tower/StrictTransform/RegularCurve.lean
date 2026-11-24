/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Basic
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.RegularCurve
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Stalk

/-!
# Strict transforms of regular curves in point blowup towers

The iterated strict transform of a regular irreducible curve is isomorphic to
the original curve. On a smooth surface its stalk order is one on its support.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y} {C : X.IdealSheafData}
  [IrreducibleSpace C.subscheme] [TauCeti.AlgebraicGeometry.IsRegular C.subscheme]

/-- The projection of a closed point blowup tower induces an isomorphism from the
iterated strict transform of a regular irreducible curve to the original curve. -/
theorem exists_iso_strictTransform_regularCurve (hT : IsClosedPointTower X T)
    (hdim : topologicalKrullDim C.subscheme = 1) :
    ∃ e : (T.strictTransform C).subscheme ≅ C.subscheme,
      e.hom ≫ C.subschemeι = (T.strictTransform C).subschemeι ≫ T.toBase := by
  induction hT with
  | nil =>
    rw [strictTransform_nil, toBase_nil, Category.comp_id]
    exact ⟨Iso.refl _, Category.id_comp _⟩
  | @snoc d W U I hU p hp hI ih =>
    obtain ⟨e, he⟩ := ih
    have : IrreducibleSpace (U.strictTransform C).subscheme :=
      e.hom.homeomorph.irreducibleSpace_iff.mpr inferInstance
    have : TauCeti.AlgebraicGeometry.IsRegular (U.strictTransform C).subscheme :=
      IsRegular.of_isOpenImmersion e.hom
    have hdim' : topologicalKrullDim (U.strictTransform C).subscheme = 1 :=
      e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans hdim
    subst I
    obtain ⟨g, hg⟩ := (U.strictTransform C).exists_iso_strictTransform_of_regularCurve hdim' hp
    rw [strictTransform_snoc]
    refine ⟨g ≪≫ e, ?_⟩
    rw [Iso.trans_hom, Category.assoc, he, reassoc_of% hg, toBase_snoc]

variable {k : Type u} [Field k] [PerfectField k] [IsIntegral X] [IsNoetherian X]

/-- At each point of its support, the strict transform of a regular curve has
stalk order one on the smooth blown-up surface. -/
theorem stalkOrder_strictTransform_eq_one_of_mem_support
    (hT : IsClosedPointTower X T) (g : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 g]
    (hC : C.IsEffectiveCartier) (hdim : topologicalKrullDim C.subscheme = 1)
    {p : Y} (hp : p ∈ ((T.strictTransform C).support : Set Y)) :
    (T.strictTransform C).stalkOrder p = 1 := by
  let C' := T.strictTransform C
  have h := hT.isEffectiveCartier_strictTransform g hC
  obtain ⟨e, -⟩ := hT.exists_iso_strictTransform_regularCurve hdim
  have : TauCeti.AlgebraicGeometry.IsRegular C'.subscheme := IsRegular.of_isOpenImmersion e.hom
  have : Smooth (T.toBase ≫ g) := (hT.smoothOfRelativeDimension g).smooth
  obtain ⟨q, hq⟩ := C'.range_subschemeι.symm ▸ hp
  have := isRegularLocalRing_stalk_of_smooth (T.toBase ≫ g) (C'.subschemeι q)
  rw [← hq]
  exact (h.stalkOrder_eq_one_iff_isRegularLocalRing q).mpr inferInstance

end QPainleve.BlowupTower.IsClosedPointTower

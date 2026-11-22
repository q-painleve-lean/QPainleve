/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import QPainleve.Geometry.Toric.CharacterTorus.Evaluation

import QPainleve.AlgebraicGeometry.RationalMap.Fiber
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Smooth
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced

/-!
# Comparing evaluated rational maps on center fibers

Agreement after evaluation on each rational center fiber of a common regular
domain determines a rational map on the independent character torus. The proof
uses smoothness of the character tori, via Tau Ceti's
`DiagonalizableGroup.smooth_groupScheme_iff`, and dominance of variable-center evaluation.
-/

public section

open AlgebraicGeometry CategoryTheory Limits TauCeti DiagonalizableGroup

namespace QPainleve.CharacterTorus

universe u

variable (k : Type u) [Field k] [IsSepClosed k]
variable {A N : Type u} [AddCommGroup A] [AddCommGroup N] [IsAddFG A] [IsAddFG N]
  [Module.Free ℤ A] [Module.Free ℤ N]

local notation "L" B => FGCommGrpCat.of (Multiplicative B)
local notation "D" B => groupScheme k (L B)
local notation "Dmap" f => groupSchemeMap k (FGCommGrpCat.ofHom (AddMonoidHom.toMultiplicative f))
local notation "π₁" => Dmap (AddMonoidHom.inl A N)
local notation "S" => Spec (CommRingCat.of k)

/-- Two rational maps on the independent character torus are equal if, after evaluation
over a nonempty open of the center torus, their regular representatives on a common dense
open agree as rational maps on each rational center fiber of that open. -/
theorem eq_of_evaluation_rationalFibers (v : A →+ N) (U : (D A).X.left.Opens) [Nonempty U]
    {Y : Scheme.{u}} (sY : Y ⟶ S) [IsSeparated sY] {f g : (D A).X.left ⤏ Y}
    (W : ((π₁).hom.hom.left ⁻¹ᵁ U).toScheme.Opens)
    (hW : Dense (W : Set ((π₁).hom.hom.left ⁻¹ᵁ U).toScheme))
    (fW gW : W.toScheme ⟶ Y)
    (hfW : fW ≫ sY = W.ι ≫ ((π₁).hom.hom.left ∣_ U) ≫ U.ι ≫ (D A).X.hom)
    (hgW : gW ≫ sY = W.ι ≫ ((π₁).hom.hom.left ∣_ U) ≫ U.ι ≫ (D A).X.hom)
    (hfg : ∀ c : S ⟶ U.toScheme, c ≫ U.ι ≫ (D A).X.hom = 𝟙 S →
      let j := pullback.fst (W.ι ≫ ((π₁).hom.hom.left ∣_ U)) c
      (j ≫ fW).toRationalMap = (j ≫ gW).toRationalMap) :
    let e := ((π₁).hom.hom.left ⁻¹ᵁ U).ι ≫ (evaluation k v).hom.hom.left
    let : IsDominant e := isDominant_evaluation_on_center_open k v U
    e.toRationalMap.comp f = (⟨W, hW, fW⟩ : Scheme.PartialMap _ Y).toRationalMap →
    e.toRationalMap.comp g = (⟨W, hW, gW⟩ : Scheme.PartialMap _ Y).toRationalMap →
    f = g := by
  dsimp only
  intro hf hg
  obtain ⟨p, hp⟩ := ExpChar.exists k
  let : ExpChar k p := hp
  have smoothTorus (B : Type u) [AddCommGroup B] [IsAddFG B] [Module.Free ℤ B] :
      Smooth (D B).X.hom := by
    let : HasUniqueDiv B := .of_isTorsionFree ℤ B
    exact (smooth_groupScheme_iff k p (L B)).mpr fun b hb ↦
      pow_left_injective (expChar_ne_zero k p) (hb.trans (one_pow p).symm)
  have : Smooth (D N).X.hom := smoothTorus N
  have : Smooth (D A).X.hom := smoothTorus A
  have : Smooth (π₁).hom.hom.left := by
    have h : Smooth ((prodIso k A N).inv ≫ pullback.fst (D A).X.hom (D N).X.hom) :=
      inferInstance
    simpa only [← prodIso_hom_fst, Iso.inv_hom_id_assoc] using h
  let π := W.ι ≫ ((π₁).hom.hom.left ∣_ U)
  let sU := U.ι ≫ (D A).X.hom
  have : Smooth π := inferInstanceAs (Smooth (W.ι ≫ ((π₁).hom.hom.left ∣_ U)))
  have : Smooth sU := inferInstanceAs (Smooth (U.ι ≫ (D A).X.hom))
  have hred (c : S ⟶ U.toScheme) : IsReduced (pullback π c) :=
    GeometricallyReduced.geometrically_isReduced c _ _ (IsPullback.of_hasPullback π c)
  have h : fW = gW := (Scheme.Hom.eq_iff_toRationalMap_eq_on_rationalFibers π sU sY
    (fun c _ ↦ hred c)
    (by simpa only [π, sU, Category.assoc] using hfW)
    (by simpa only [π, sU, Category.assoc] using hgW)).mpr hfg
  apply (comp_evaluation_on_center_open_eq_iff k v U f g).mp
  rw [hf, hg, h]

end QPainleve.CharacterTorus

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import QPainleve.AlgebraicGeometry.RationalMap.Composition.Defined
public import QPainleve.Geometry.Toric.CharacterTorus.Evaluation

import QPainleve.AlgebraicGeometry.RationalMap.Fiber
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced

/-!
# Comparing evaluated rational maps on center fibers

Agreement after evaluation on each rational center fiber of a common regular
domain determines a rational map on the independent character torus. The proof
uses smoothness of the character tori and dominance of variable-center evaluation.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TauCeti DiagonalizableGroup

namespace QPainleve.CharacterTorus

universe u

variable (k : Type u)
variable {A N : Type u} [AddCommGroup A] [AddCommGroup N] [IsAddFG A] [IsAddFG N]

local notation "L" B => FGCommGrpCat.of (Multiplicative B)
local notation "D" B => groupScheme k (L B)
local notation "Dmap" f => groupSchemeMap k (FGCommGrpCat.ofHom (AddMonoidHom.toMultiplicative f))
local notation "π₁" => Dmap (AddMonoidHom.inl A N)
local notation "π₂" => Dmap (AddMonoidHom.inr A N)
local notation "S" => Spec (CommRingCat.of k)

section RationalFibers

variable [Field k] [IsSepClosed k] [Module.Free ℤ A] [Module.Free ℤ N]

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
  have : Smooth (D A).X.hom := smooth_groupScheme_of_free k A
  let : Smooth (D N).X.hom := smooth_groupScheme_of_free k N
  let : Smooth (π₁).hom.hom.left := smooth_map_inl k A N
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

end RationalFibers

/-! ### Comparison from fixed-center rational maps -/

local notation3 (prettyPrint := false) "E[" U "]" => ((π₁).hom.hom.left ⁻¹ᵁ U)
local notation3 (prettyPrint := false) "π[" U "]" => ((π₁).hom.hom.left ∣_ U)

local notation3 (prettyPrint := false) "ev[" U "," v "]" =>
  ((E[U]).ι ≫ (evaluation k v).hom.hom.left)

section CenterEvaluation

variable [CommRing k]

/-- The fiber of the center projection over a rational center is the charge torus. -/
def centerFiberIso (U : (D A).X.left.Opens) (c : S ⟶ U.toScheme)
    (hc : c ≫ U.ι ≫ (D A).X.hom = 𝟙 S) :
    pullback π[U] c ≅ (D N).X.left := by
  have hp : IsPullback (π₂).hom.hom.left (π₁).hom.hom.left (D N).X.hom (D A).X.hom :=
    (IsPullback.of_hasPullback (D A).X.hom (D N).X.hom).flip.of_iso' (prodIso k A N).symm
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [Iso.inv_comp_eq])
      (by simp [Iso.inv_comp_eq]) (by simp) (by simp)
  have h := ((IsPullback.of_hasPullback π[U] c).paste_horiz
    (isPullback_morphismRestrict (π₁).hom.hom.left U).flip).paste_horiz hp
  let j := (pullback.fst π[U] c ≫ (E[U]).ι) ≫ (π₂).hom.hom.left
  have h' : IsPullback j (pullback.snd π[U] c) (D N).X.hom (𝟙 S) := by
    simpa only [j, Category.assoc, hc] using h
  have := h'.isIso_fst_of_isIso
  exact asIso j

/-- The fiber isomorphism is the second projection of the joint center and charge torus. -/
@[simp]
theorem centerFiberIso_hom (U : (D A).X.left.Opens) (c : S ⟶ U.toScheme)
    (hc : c ≫ U.ι ≫ (D A).X.hom = 𝟙 S) :
    (centerFiberIso k U c hc).hom = pullback.fst π[U] c ≫ (E[U]).ι ≫ (π₂).hom.hom.left := by
  rw [← Category.assoc]
  rfl

/-- Restrict variable-center evaluation to the fiber over a specified center. -/
def centerFiberEvaluation (U : (D A).X.left.Opens) (v : A →+ N) (c : S ⟶ U.toScheme) :
    pullback π[U] c ⟶ (D A).X.left :=
  pullback.fst π[U] c ≫ ev[U, v]

/-- Fixed-center evaluation is the restriction of the joint torus evaluation. -/
@[simp]
theorem centerFiberEvaluation_def (U : (D A).X.left.Opens) (v : A →+ N) (c : S ⟶ U.toScheme) :
    centerFiberEvaluation k U v c = pullback.fst π[U] c ≫ ev[U, v] := (rfl)

/-- The fiber of variable-center evaluation is evaluation at the corresponding
center of the ambient torus. -/
theorem centerFiberIso_hom_comp_evaluationAtCenter
    (U : (D A).X.left.Opens) (v : A →+ N) (c : S ⟶ U.toScheme)
    (hc : c ≫ U.ι ≫ (D A).X.hom = 𝟙 S) :
    (centerFiberIso k (N := N) U c hc).hom ≫
        evaluationAtCenter k v (c ≫ U.ι) (by simpa using hc) =
      centerFiberEvaluation k U v c := by
  let e := centerFiberIso k (N := N) U c hc
  let j := pullback.fst π[U] c ≫ (E[U]).ι
  let q := pullback.lift (f := (D A).X.hom) (g := (D N).X.hom)
    ((D N).X.hom ≫ c ≫ U.ι) (𝟙 (D N).X.left) (by simp [hc])
  have hf := ((prodIso k A N).inv_comp_eq).2 (prodIso_hom_fst k A N).symm
  have hs := ((prodIso k A N).inv_comp_eq).2 (prodIso_hom_snd k A N).symm
  have h : (e.hom ≫ q) ≫ (prodIso k A N).hom = j := by
    symm
    apply ((prodIso k A N).comp_inv_eq).mp
    apply pullback.hom_ext
    · simp only [q, j, Category.assoc, hf, pullback.lift_fst]
      rw [← morphismRestrict_ι, pullback.condition_assoc]
      have he : e.hom ≫ (D N).X.hom = pullback.snd π[U] c := by
        simp only [e, centerFiberIso_hom, Category.assoc, Over.w]
        rw [← Over.w ((π₁).hom.hom), ← morphismRestrict_ι_assoc,
          pullback.condition_assoc, hc, Category.comp_id]
      rw [reassoc_of% he]
    · simp only [q, j, e, Category.assoc, hs, pullback.lift_snd,
        Category.comp_id, centerFiberIso_hom]
  simpa only [evaluationAtCenter, centerFiberEvaluation_def, e, q, j, Category.assoc]
    using congrArg (· ≫ (evaluation k v).hom.hom.left) h

end CenterEvaluation

variable [Field k] [IsSepClosed k] [Module.Free ℤ A] [Module.Free ℤ N]
  {Y : Scheme.{u}} [Y.IsSeparated]

/-- Agreement after rational composition on every center fiber of a nonempty
open determines the X map. Postcompose evaluation by a dominant morphism `eX`
over the ground field to compare maps on the chosen independent-variable scheme. -/
theorem eq_of_compOfDefined_eq_on_center_fibers (U : (D A).X.left.Opens) [Nonempty U]
    (v : A →+ N) {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    (sX : X ⟶ S) (sY : Y ⟶ S)
    (eX : (D A).X.left ⟶ X) [IsDominant eX] (heX : eX ≫ sX = (D A).X.hom)
    {f g : X ⤏ Y} [f.IsOver sX sY] [g.IsOver sX sY]
    (heq : ∀ (c : S ⟶ U.toScheme) (hc : c ≫ U.ι ≫ (D A).X.hom = 𝟙 S),
      letI : IsIntegral (pullback π[U] c) :=
        IsIntegral.of_isIso (centerFiberIso k (N := N) U c hc).inv
      let j := (centerFiberEvaluation k U v c ≫ eX).toRationalMap
      let x := j.fromFunctionField (IsLocalRing.closedPoint _)
      ∃ (hf : x ∈ f.domain) (hg : x ∈ g.domain),
        j.compOfDefined f hf = j.compOfDefined g hg) :
    f = g := by
  let e := ev[U, v]
  let : IsDominant e := isDominant_evaluation_on_center_open k v U
  have : (E[U]).toScheme.IsSeparated := Scheme.IsSeparated.of_isSeparated (E[U]).ι
  let : Smooth (D A).X.hom := smooth_groupScheme_of_free k A
  let : Smooth (D N).X.hom := smooth_groupScheme_of_free k N
  let : Smooth (π₁).hom.hom.left := smooth_map_inl k A N
  have hb : (e ≫ eX) ≫ sX = π[U] ≫ (U.ι ≫ (D A).X.hom) := by
    simp only [e, Category.assoc, heX, morphismRestrict_ι_assoc, Over.w]
  have hF (c : S ⟶ U.toScheme) (hc : c ≫ (U.ι ≫ (D A).X.hom) = 𝟙 S) :
      IsIntegral (pullback π[U] c : Scheme) :=
    IsIntegral.of_isIso (centerFiberIso k (N := N) U c hc).inv
  apply Scheme.RationalMap.eq_of_compOfDefined_eq_on_rationalFibers
    π[U] (U.ι ≫ (D A).X.hom) sX sY (e ≫ eX) hb hF
  intro c hc
  simpa only [centerFiberEvaluation_def, Category.assoc, e] using heq c hc

end QPainleve.CharacterTorus

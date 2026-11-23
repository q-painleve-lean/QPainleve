/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

import QPainleve.AlgebraicGeometry.Blowup.Point.Picard
import QPainleve.AlgebraicGeometry.Blowup.Tower.Descent
import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Picard-trivial automorphisms of point blowup towers

A Picard-trivial automorphism of the final surface descends through the ordered tower
of closed point blowups. At each stage it preserves the current exceptional curve by
its Picard class. The descended automorphism is Picard-trivial and fixes the center at
that stage, including when the center is infinitely near. Triviality of the pullback
is compared through the existing `BlowupTower.IsLift.pullback_picardHom` marking
formula.

This uses the descent argument in Gross, Hacking and Keel, *Moduli of surfaces with an
anti-canonical cycle*, Proposition 2.6, one blowup at a time.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open LineBundleClass (pullback)

namespace QPainleve.BlowupTower

universe u

variable {k : Type u} [Field k] [PerfectField k]
  {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}
  [IsIntegral X] [IsNoetherian X]
  (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]

include f

namespace IsClosedPointTower

/-- A Picard-trivial automorphism of the final surface of a closed point blowup tower is
the ordered lift of a unique Picard-trivial automorphism of the original surface. -/
theorem existsUnique_isLift_of_picard_trivial (hT : IsClosedPointTower X T)
    (g : Y ≅ Y) (hg : ∀ a, pullback g.hom a = a) :
    ∃! e : X ≅ X, IsLift e T T g ∧ ∀ a, pullback e.hom a = a := by
  induction hT with
  | nil =>
    exact ⟨g, ⟨IsLift.nil_iff.mpr rfl, hg⟩, fun _ h ↦ (IsLift.nil_iff.mp h.1).symm⟩
  | @snoc m W S I hS p hp hI ih =>
    subst I
    let I := (W.fromSpecResidueField p).ker
    let fW := S.toBase ≫ f
    have : IsNoetherian W := S.isNoetherian
    have : IsIntegral W := hS.isIntegral f
    have : SmoothOfRelativeDimension 2 fW := hS.smoothOfRelativeDimension f
    have : Smooth fW := SmoothOfRelativeDimension.smooth 2 fW
    have := isRegularLocalRing_stalk_of_smooth fW p
    have hd := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq fW 2).mp inferInstance).2 p hp
    obtain ⟨a, ⟨ha, heq⟩, huniq⟩ :=
      Scheme.IdealSheafData.existsUnique_baseIso_of_pullback_blowupExceptionalClass_eq
        hp hp hd hd g
        (hg I.blowupExceptionalClass)
    let step := (BlowupTower.nil (X := W)).snoc I
    have hstep : IsLift a step step g :=
      IsLift.snoc_iff.mpr ⟨a, IsLift.nil_iff.mpr rfl, ha, heq⟩
    have hpoint : IsClosedPointTower W step := IsClosedPointTower.nil.snoc p hp rfl
    obtain ⟨e, ⟨he, hePic⟩, huniqBase⟩ := ih a ((hstep.forall_pullback_eq_iff fW hpoint).mp hg)
    refine ⟨e, ⟨IsLift.snoc_iff.mpr ⟨a, he, ha, heq⟩, hePic⟩, ?_⟩
    rintro e' ⟨he', he'Pic⟩
    obtain ⟨a', ha', hcenter, hlift⟩ := IsLift.snoc_iff.mp he'
    have : a' = a := huniq a' ⟨hcenter, hlift⟩
    subst a'
    exact huniqBase e' ⟨ha', he'Pic⟩

/-- Descent of a Picard-trivial automorphism over the field preserves the structure
morphism. The structure map on the final surface is the composite with the tower projection. -/
theorem existsUnique_isLift_over_of_picard_trivial (hT : IsClosedPointTower X T)
    (g : Y ≅ Y) (hg : ∀ a, pullback g.hom a = a)
    (hgOver : g.hom ≫ T.toBase ≫ f = T.toBase ≫ f) :
    ∃! e : X ≅ X, IsLift e T T g ∧ (∀ a, pullback e.hom a = a) ∧ e.hom ≫ f = f := by
  obtain ⟨e, ⟨he, hePic⟩, huniq⟩ := hT.existsUnique_isLift_of_picard_trivial f g hg
  have hdesc := hT.existsUnique_comp_eq_toBase f (T.toBase ≫ f) fun x y hxy ↦ by
    simpa only [Scheme.Hom.comp_apply] using congrArg f hxy
  refine ⟨e, ⟨he, hePic, hdesc.unique ?_ rfl⟩, fun e' he' ↦ huniq e' ⟨he'.1, he'.2.1⟩⟩
  rwa [← Category.assoc, ← he.hom_toBase, Category.assoc]

end IsClosedPointTower

end QPainleve.BlowupTower

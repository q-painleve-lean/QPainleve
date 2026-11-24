/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Ruling

import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.CurveLinearSystem
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.LinearSystem
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.MinimalCurve
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.SquareOne
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.SmoothProjective

/-!
# Minimal models of smooth projective rational surfaces

Successive applications of `IsExceptionalCurveOfFirstKind.exists_smooth_projective_contraction`
exhibit a smooth projective rational surface as an ordered tower of closed point blowups
over a minimal rational surface. The tower length is the difference of the Picard ranks.

The reduction to a minimal pair in
[Gross, Hacking and Keel, Proposition 1.3](https://arxiv.org/html/1106.4977v3#S1.SS1)
starts by contracting exceptional curves. On the minimal surface the complete linear
system of a minimizing rational curve gives either the projective plane or a ruling
by projective lines, as in [Vakil, Class 17, §2](https://math.stanford.edu/~vakil/02-245/sclass17A.pdf).
-/

public section

open CategoryTheory TopologicalSpace QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] [IsAlgClosed k]

local notation "S" => Spec (CommRingCat.of k)
local notation "ρ(" X ")" => Module.finrank ℤ (Additive (LineBundleClass X))

/-- A smooth projective rational surface over an algebraically closed field is an
ordered tower of closed point blowups of a smooth projective rational surface
without exceptional curves of the first kind. The comparison is over the ground
field, and each blowup contributes one to the Picard rank. -/
theorem exists_isClosedPointTower_of_minimal_model (X : Scheme.{u}) [X.Over S]
    [X.IsProjectiveOver k] [SmoothOfRelativeDimension 2 (X ↘ S)]
    [IsRationalOver (X ↘ S)] :
    ∃ (Y : Scheme.{u}) (s : Y ⟶ S) (n : ℕ) (W : Scheme.{u})
      (T : BlowupTower Y n W) (e : X ≅ W),
      letI : Y.Over S := ⟨s⟩
      Y.IsProjectiveOver k ∧ SmoothOfRelativeDimension 2 s ∧ IsRationalOver s ∧
        (∀ E : Y.IdealSheafData, ¬ E.IsExceptionalCurveOfFirstKind) ∧
        T.IsClosedPointTower Y ∧ e.hom ≫ T.toBase ≫ s = (X ↘ S) ∧
        ρ(X) = ρ(Y) + n := by
  generalize hr : ρ(X) = r
  induction r using Nat.strong_induction_on generalizing X with
  | ind r ih =>
    by_cases hmin : ∀ E : X.IdealSheafData, ¬ E.IsExceptionalCurveOfFirstKind
    · exact ⟨X, X ↘ S, 0, X, .nil, .refl _, ‹_›, ‹_›, ‹_›, hmin, .nil, by simp,
        by simpa using hr.symm⟩
    push Not at hmin
    obtain ⟨E, hE⟩ := hmin
    have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    have : IsIntegral X := (inferInstance : IsRationalOver (X ↘ S)).isIntegral_of_smooth
    obtain ⟨Z, t, f, p, hZ, hpZ, hsZ, hf, hmod, hp, -, -, -, a, ha⟩ :=
      hE.exists_smooth_projective_contraction (k := k)
    let : Z.Over S := ⟨t⟩
    have : SmoothOfRelativeDimension 2 (Z ↘ S) := hsZ
    have : f.IsOver S := hf
    have hft : f ≫ t = (X ↘ S) := comp_over f S
    obtain ⟨b, hb⟩ := IsModification.birationalOver f
    have hbir : BirationalOver (X ↘ S) t := ⟨b, by
      simpa only [Category.assoc, Category.comp_id, hft] using congrArg (· ≫ t) hb⟩
    have : IsRationalOver (Z ↘ S) := hbir.symm.isRationalOver t (X ↘ S)
    let I := (Z.fromSpecResidueField p).ker
    let U : BlowupTower Z 1 I.blowup := (BlowupTower.nil (X := Z)).snoc I
    have hU : U.IsClosedPointTower Z := .snoc .nil p hp rfl
    have : IsNoetherian Z := isNoetherian_of_finiteType (Z ↘ S)
    have : Module.Finite ℤ (Additive (LineBundleClass Z)) := Z.finite_picard_of_isRationalOver k
    have hrank : r = ρ(Z) + 1 := hr.symm.trans
      (((LineBundleClass.pullbackEquiv a).toAdditive.toIntLinearEquiv.finrank_eq).symm.trans
        (BlowupTower.finrank_picard k hU))
    obtain ⟨Y, s, n, W, T, e, hY, hsY, hRatY, hminY, hT, he, hρ⟩ :=
      ih _ (by omega : ρ(Z) < r) Z rfl
    -- Append the blowup after transporting its center along the isomorphism from the induction.
    let V := U.transport e
    have hV : V.tower.IsClosedPointTower W := V.isLift.isClosedPointTower hU
    refine ⟨Y, s, n + 1, V.top, T.append V.tower, a ≪≫ V.iso, hY, hsY, hRatY, hminY,
      hT.append hV, ?_, by omega⟩
    simp only [Iso.trans_hom, BlowupTower.toBase_append, Category.assoc,
      V.isLift.hom_toBase_assoc, he, U, BlowupTower.toBase_snoc, BlowupTower.toBase_nil,
      Category.comp_id]
    exact ((reassoc_of% ha) t).trans hft

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A smooth projective rational surface without exceptional curves of the first kind
is either the projective plane or admits a proper flat ruling over the projective line.
Every closed scheme-theoretic fiber of the ruling is a projective line over the ground
field. -/
theorem exists_iso_projectivePlane_or_ruling (X : Scheme.{u}) [X.Over S]
    [X.IsProjectiveOver k] [SmoothOfRelativeDimension 2 (X ↘ S)] [IsRationalOver (X ↘ S)]
    (hmin : ∀ E : X.IdealSheafData, ¬ E.IsExceptionalCurveOfFirstKind) :
    let A := MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 3)) k
    (∃ e : X ≅ Proj A, e.hom ≫ Proj.toSpecCoeff A = X ↘ S) ∨
      ∃ f : X ⟶ projectiveLine k, f.IsOver S ∧ IsProper f ∧ Flat f ∧ Surjective f ∧
        ∀ p : projectiveLine k, IsClosed ({p} : Set (projectiveLine k)) →
          ∃ e : f.fiber p ≅ projectiveLine k,
            e.hom ≫ (projectiveLine k ↘ S) = f.fiberι p ≫ X ↘ S := by
  dsimp only
  obtain ⟨I, hI, hI₂, a, ha⟩ := X.exists_smooth_rational_curve_self_nonneg k hmin
  obtain ⟨C, hC, hC₂, hsys⟩ :=
    exists_minimal_rational_curve_linear_system (k := k) hmin hI hI₂ a ha
  obtain ⟨b, hb⟩ := hsys C hC rfl
  have : b.hom.IsOver S := hb
  have hmembers (J : X.IdealSheafData) (hJ : J.IsEffectiveCartier)
      (heq : LineBundleClass.mk hJ.toInvertibleSheaf.dual =
        LineBundleClass.mk hC.toInvertibleSheaf.dual) :=
    hsys J hJ (by simpa only [LineBundleClass.inv_mk] using heq)
  have hle := hC.classIntersectionNumber_self_le_one_of_regular_linear_system b (by
    intro J hJ heq
    obtain ⟨d, hd⟩ := hmembers J hJ heq
    have : d.hom.IsOver S := hd
    have : Smooth (d.hom ≫ (projectiveLine k ↘ S)) := by
      have : Smooth (projectiveLine k ↘ S) := SmoothOfRelativeDimension.smooth 1 _
      infer_instance
    have : Smooth (J.subscheme ↘ S) := comp_over d.hom S ▸ ‹_›
    exact IsRegular.of_smooth (J.subscheme ↘ S))
  rcases eq_or_lt_of_le hle with hone | hlt
  · left
    obtain ⟨e, he, -⟩ := hC.exists_iso_projectivePlane_of_square_one_linear_system b hone
      (fun J hJ heq ↦ IsIntegral.of_isIso (hmembers J hJ heq).choose.inv)
    exact ⟨e, he⟩
  · right
    have hzero : Chow.classIntersectionNumber k X
        (LineBundleClass.mk hC.toInvertibleSheaf)⁻¹
        (LineBundleClass.mk hC.toInvertibleSheaf)⁻¹ = 0 := by
      simp only [← LineBundleClass.inv_mk] at hlt
      omega
    have : IsIntegral C.subscheme := IsIntegral.of_isIso b.inv
    have : IsProper (C.subscheme ↘ S) := by
      rw [C.over_eq_subschemeι_comp]
      infer_instance
    have : C.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
      ⟨inferInstance, inferInstance, b.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans
        (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := projectiveLine k) k)⟩
    have hg : C.subscheme.genus k = 0 := genus_eq_zero_iff_exists_iso_projectiveLine.mpr ⟨b, hb⟩
    obtain ⟨f, hf, hproper, hflat, hsurj, -, hfiber⟩ :=
      hC.exists_ruling_of_square_zero_rational_curve hmin hzero hg
    exact ⟨f, hf, hproper, hflat, hsurj, hfiber⟩

end AlgebraicGeometry.Scheme

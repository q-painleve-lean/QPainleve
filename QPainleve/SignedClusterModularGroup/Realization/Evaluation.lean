/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Basic

/-!
# Changing source coordinates in geometric realizations

An isomorphism of independent coordinate schemes lets a realization use new source
coordinates. The maps of surface pairs and their integral markings are preserved.
The fixed-center construction uses `FiberRealization.compEvaluation` for the
regular coordinate change.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Scheme TauCeti.AlgebraicGeometry

namespace QPainleve.SignedClusterModularGroup

universe u

variable {k : Type u} [Field k] [IsSepClosed k] [Infinite k] {n : ℕ} [NeZero n]
  {L₀ L₁ : Type u} [AddCommGroup L₀] [AddCommGroup L₁]
  {B₀ : LinearMap.BilinForm ℤ L₀} {B₁ : LinearMap.BilinForm ℤ L₁}
  {X' X Y : Scheme.{u}} [IsIntegral X'] [IsIntegral X]
  [X'.IsSeparated] [X.IsSeparated] [Y.IsSeparated] {F : X ⤏ Y}

namespace FiberRealization

variable {M : MarkedSurface k n B₀ X} {N : MarkedSurface k n B₁ Y}
  {I : B₁.IsometryEquiv B₀} {g : DihedralGroup n}

omit [IsIntegral X'] [IsIntegral X] [X'.IsSeparated] [X.IsSeparated] in
private theorem compEvaluation_inv_hom (M : MarkedSurface k n B₀ X) (e : X' ≅ X) :
    (M.compEvaluation e.inv).compEvaluation e.hom = M := by
  have h : (M.evaluation.compHom e.inv).compHom e.hom = M.evaluation :=
    RationalMap.eq_of_fromFunctionField_eq _ _ (by
      simp only [RationalMap.fromFunctionField_compHom, Category.assoc, e.inv_hom_id,
        Category.comp_id])
  cases M
  dsimp only [MarkedSurface.compEvaluation] at *
  congr

private theorem cast_target_iso_heq {N' : MarkedSurface k n B₁ Y}
    (R : FiberRealization M N F I g) (h : N = N') :
    HEq (Eq.mp (congrArg (fun P ↦ FiberRealization M P F I g) h) R).iso R.iso := by
  subst N'
  rfl

/-- Express a fiber realization in source coordinates given by `e`. -/
private def precompEvaluation (R : FiberRealization M N F I g) (e : X' ≅ X) :
    { R' : FiberRealization (M.compEvaluation e.inv) N (e.hom.toRationalMap.comp F) I g //
      R'.iso = R.iso } := by
  let M' := M.compEvaluation e.inv
  have h := compEvaluation_inv_hom M e
  let r₀ := FiberRealization.compEvaluation M' e.hom
  let r : FiberRealization M' M e.hom.toRationalMap (.refl B₀) 1 :=
    Eq.mp (congrArg (fun P ↦ FiberRealization M' P e.hom.toRationalMap (.refl B₀) 1) h) r₀
  have hr : r.iso = Iso.refl M.pair := by
    have h' := cast_target_iso_heq r₀ h
    exact (eq_of_heq h').trans (FiberRealization.compEvaluation_iso _ _)
  have hI : I.trans (.refl B₀) = I := by
    cases I
    rfl
  have hcomp : (r.comp R).iso = R.iso :=
    (FiberRealization.comp_iso r R).trans
      ((congrArg (fun f : M.pair ≅ M.pair ↦ f ≪≫ R.iso) hr).trans (Iso.refl_trans _))
  let Result (J : B₁.IsometryEquiv B₀) (δ : DihedralGroup n) :=
    { R' : FiberRealization M' N (e.hom.toRationalMap.comp F) J δ // R'.iso = R.iso }
  exact (congrArg₂ Result hI (mul_one g)).mp ⟨r.comp R, hcomp⟩

end FiberRealization

namespace GeometricRealization

variable {T₀ T₁ : Over (Spec (CommRingCat.of k))} [Nonempty T₀.left] [Smooth T₀.hom]
  {P₀ : Point T₀ → MarkedSurface k n B₀ X} {P₁ : Point T₁ → MarkedSurface k n B₁ Y}
  {C : T₀.left.PartialMap T₁.left} [IsDominant C.hom] [C.IsOver T₀.hom T₁.hom]
  [F.IsDominant]

/-- Express a geometric realization in isomorphic source coordinates at every center. -/
def precompEvaluation (R : GeometricRealization P₀ P₁ C F) (e : X' ≅ X) :
    GeometricRealization (fun c ↦ (P₀ c).compEvaluation e.inv) P₁ C
      (e.hom.toRationalMap.comp F) where
  picard := R.picard
  boundaryAction := R.boundaryAction
  fiber c := ((R.fiber c).precompEvaluation e).val

@[simp]
theorem precompEvaluation_picard (R : GeometricRealization P₀ P₁ C F) (e : X' ≅ X) :
    (R.precompEvaluation e).picard = R.picard := (rfl)

@[simp]
theorem precompEvaluation_boundaryAction (R : GeometricRealization P₀ P₁ C F) (e : X' ≅ X) :
    (R.precompEvaluation e).boundaryAction = R.boundaryAction := (rfl)

@[simp]
theorem precompEvaluation_fiber_iso (R : GeometricRealization P₀ P₁ C F) (e : X' ≅ X)
    (c : CenterPoint C) : ((R.precompEvaluation e).fiber c).iso = (R.fiber c).iso :=
  ((R.fiber c).precompEvaluation e).property

end GeometricRealization

end QPainleve.SignedClusterModularGroup

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import QPainleve.AlgebraicGeometry.Chow.ProjectivePlane.Basic
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.TwistingSheaf
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Basic
public import TauCeti.AlgebraicGeometry.Scheme.Normal

import QPainleve.AlgebraicGeometry.Chow.Isomorphism
import QPainleve.AlgebraicGeometry.Chow.ProperIntersection
import QPainleve.AlgebraicGeometry.Morphisms.Finite
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Chart.Sections
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Integral
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Normal
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank
import TauCeti.AlgebraicGeometry.Scheme.LocalDimension
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

/-!
# Degree of a finite morphism to the projective plane

A finite morphism from a normal projective surface to the projective plane is flat.
The intersection of the pullbacks of two coordinate lines has length equal to the degree,
so the square of the pulled-back hyperplane class is the degree. In particular, a finite
morphism given by a linear system of square one is an isomorphism. This is the degree
calculation used in Vakil, *Complex Algebraic Surfaces*, Class 17, §2.

Flatness uses the surface case of miracle flatness, supplied by Tau Ceti's
`Scheme.Hom.flat_of_isDominant_of_locallyQuasiFinite_of_ringKrullDim_le_two`.
See [Stacks Project, Lemma 10.128.1](https://stacks.math.columbia.edu/tag/00R4).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open TauCeti TauCeti.AlgebraicGeometry LineBundleClass

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] MvPolynomial.gradedAlgebra Proj.polynomialFinOver

local notation "P[" k "]" => Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k)
local notation "H[" k "]" => LineBundleClass.mk (Proj.polynomialTwistingBundle (k := k) (n := 2) 1)

private theorem polynomialPlane_structureMap (k : Type u) [Field k] :
    P[k] ↘ Spec (.of k) = Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule (Fin 3) k) :=
  (rfl)

private local instance (k : Type u) [Field k] (m : ℤ) :
    SheafOfModules.isInvertible P[k]
      (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 3) k) m) := by
  rw [← Proj.polynomialTwistingBundle_obj (n := 2)]
  exact (Proj.polynomialTwistingBundle m).property

private theorem isOver_polynomialProjIso_hom {k M : Type u} [Field k] [AddCommMonoid M]
    [Module k M] (b : Module.Basis (Fin 3) k M) :
    b.polynomialProjIso.hom.IsOver (Spec (.of k)) := by
  constructor
  rw [SymmetricAlgebra.over_eq_projToSpec, polynomialPlane_structureMap]
  exact b.polynomialProjIso_hom_over

private theorem pullback_hyperplane_polynomialProjIso_hom {k M : Type u} [Field k]
    [AddCommMonoid M] [Module k M] (b : Module.Basis (Fin 3) k M) :
    pullback b.polynomialProjIso.hom
        (LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle k M 1)) =
      H[k] :=
  (b.pullback_mk_symmetricAlgebraTwistingBundle 1).trans
    (mk_eq_mk_iff.mpr ⟨eqToIso (Proj.polynomialTwistingBundle_obj 1).symm⟩)

section

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X] [IsNormalScheme X]

omit [Infinite k] in
private theorem classIntersectionNumber_hyperplane_self :
    Chow.classIntersectionNumber k P[k] H[k] H[k] = 1 := by
  let b := Pi.basisFun k (Fin 3)
  let e := b.polynomialProjIso
  let a := LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle k (Fin 3 → k) 1)
  have : e.hom.IsOver (Spec (.of k)) := isOver_polynomialProjIso_hom b
  have he : pullback e.hom a = H[k] := pullback_hyperplane_polynomialProjIso_hom b
  rw [← he, Chow.classIntersectionNumber_pullback_of_isIso,
    Chow.classIntersectionNumber_projectivePlane]
  simp [a, Module.Basis.picardTwistEquiv_apply_twist]

omit [Infinite k] [X.Over (Spec (.of k))] [X.IsProjectiveOver k] in
private theorem flat_of_isFinite_to_polynomialPlane (f : X ⟶ P[k]) [IsFinite f]
    (hX : 2 ≤ topologicalKrullDim X) : Flat f := by
  have : IsIntegral P[k] := Proj.isIntegral_polynomialProj
  let s := Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule (Fin 3) k)
  have : SmoothOfRelativeDimension 2 s := Proj.smoothOfRelativeDimension_polynomial k
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 s
  have hP := topologicalKrullDim_eq_of_smoothOfRelativeDimension s (n := 2)
  have : IsDominant f := f.isDominant_of_isFinite_of_topologicalKrullDim_le
    (hP ▸ WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top 2)) (hP.symm ▸ hX)
  have : IsRegular P[k] := IsRegular.of_smooth s
  have : IsLocallyNoetherian P[k] := LocallyOfFiniteType.isLocallyNoetherian s
  refine f.flat_of_isDominant_of_locallyQuasiFinite_of_ringKrullDim_le_two fun y ↦ ?_
  rw [ringKrullDim_stalk_eq_coheight]
  exact (coheight_le_topologicalKrullDim y).trans_eq hP

omit [IsIntegral X] [IsNormalScheme X] in
private theorem classIntersectionNumber_pullback_hyperplane_eq_finrank (f : X ⟶ P[k])
    [f.IsOver (Spec (.of k))] [IsFinite f] [Flat f] (y : P[k]) :
    Chow.classIntersectionNumber k X (pullback f H[k]) (pullback f H[k]) = f.finrank y := by
  have : IsIntegral P[k] := Proj.isIntegral_polynomialProj
  let s := Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule (Fin 3) k)
  have : SmoothOfRelativeDimension 2 s := Proj.smoothOfRelativeDimension_polynomial k
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 s
  have : IsLocallyNoetherian P[k] := LocallyOfFiniteType.isLocallyNoetherian s
  let b := Pi.basisFun k (Fin 3)
  have : b.polynomialProjIso.hom.IsOver (Spec (.of k)) := isOver_polynomialProjIso_hom b
  have : P[k].IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k b.polynomialProjIso.hom
  have hP := (topologicalKrullDim_eq_of_smoothOfRelativeDimension s (n := 2)).le
  have hd := fun z ↦ (f.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace z y)
  have h := Chow.classIntersectionNumber_pullback_of_cartierIntersection k f hP
    (Proj.isEffectiveCartier_coordinateHyperplaneIdeal (k := k) (0 : Fin 3))
    (Proj.isEffectiveCartier_coordinateHyperplaneIdeal (k := k) (1 : Fin 3))
    (Proj.isEffectiveCartier_comap_coordinateHyperplaneIdeal (by decide : (0 : Fin 3) ≠ 1)) hd
  simpa only [Proj.coordinateHyperplaneIdeal_class, classIntersectionNumber_hyperplane_self,
    mul_one] using h

end

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X] [IsNormalScheme X] {ι : Type u}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι k
local notation "Q" => Proj 𝒜
local notation "H'" => LineBundleClass.mk
  (ObjectProperty.FullSubcategory.mk (Proj.twistingSheaf 𝒜 1) inferInstance : InvertibleSheaf Q)

private def polynomialPlaneIso (ε : ι ≃ Fin 3) : Q ≅ P[k] :=
  let b := Pi.basisFun k (Fin 3)
  (b.reindex ε.symm).polynomialProjIso ≪≫ b.polynomialProjIso.symm

omit [Infinite k] [X.Over (Spec (.of k))] [X.IsProjectiveOver k] in
/-- A finite morphism from a normal integral surface to the projective plane is flat. -/
theorem flat_of_isFinite_to_projectivePlane (f : X ⟶ Q) [IsFinite f]
    (hX : 2 ≤ topologicalKrullDim X) (ε : ι ≃ Fin 3) : Flat f := by
  let e := polynomialPlaneIso (k := k) ε
  have : Flat (f ≫ e.hom) := flat_of_isFinite_to_polynomialPlane _ hX
  have hf : f = (f ≫ e.hom) ≫ e.inv := by simp
  exact hf ▸ inferInstance

/-- The square of the pullback of `𝒪(1)` by a finite morphism from a normal projective
surface to the plane is the degree, computed as the rank at any point of the plane.
The coordinate index type can be any type equivalent to `Fin 3`. -/
theorem classIntersectionNumber_pullback_twistingSheaf_projectivePlane (f : X ⟶ Q)
    [f.IsOver (Spec (.of k))] [IsFinite f] (hX : 2 ≤ topologicalKrullDim X) (ε : ι ≃ Fin 3)
    (y : Q) : Chow.classIntersectionNumber k X (pullback f H') (pullback f H') = f.finrank y := by
  let b := Pi.basisFun k (Fin 3)
  let b' := b.reindex ε.symm
  let e := polynomialPlaneIso (k := k) ε
  have heq : e.hom = b'.polynomialProjIso.hom ≫ b.polynomialProjIso.inv := rfl
  have he : e.hom.IsOver (Spec (.of k)) := ⟨by
    rw [Proj.over_polynomial, polynomialPlane_structureMap, ← b.polynomialProjIso_hom_over, heq,
      Category.assoc, Iso.inv_hom_id_assoc,
      b'.polynomialProjIso_hom_over]⟩
  have hH : pullback e.hom H[k] = H' := by
    rw [← pullback_hyperplane_polynomialProjIso_hom b, heq, ← pullback_comp,
      pullback_comp b.polynomialProjIso.inv, Iso.inv_hom_id, pullback_id,
      b'.pullback_mk_symmetricAlgebraTwistingBundle]
  let g := f ≫ e.hom
  have : Flat f := f.flat_of_isFinite_to_projectivePlane hX ε
  have : g.IsOver (Spec (.of k)) := inferInstanceAs ((f ≫ e.hom).IsOver (Spec (.of k)))
  have : IsFinite g := inferInstanceAs (IsFinite (f ≫ e.hom))
  have : Flat g := inferInstanceAs (Flat (f ≫ e.hom))
  rw [← hH, pullback_comp, classIntersectionNumber_pullback_hyperplane_eq_finrank g (e.hom y)]
  exact_mod_cast f.finrank_comp_right_of_isIso e.hom y

/-- A finite morphism from a normal projective surface to the projective plane is
an isomorphism exactly when the pullback of the hyperplane class has square one. -/
theorem isIso_iff_hyperplane_pullback_square_eq_one (f : X ⟶ Q)
    [f.IsOver (Spec (.of k))] [IsFinite f] (hX : 2 ≤ topologicalKrullDim X) (ε : ι ≃ Fin 3) :
    IsIso f ↔ Chow.classIntersectionNumber k X (pullback f H') (pullback f H') = 1 := by
  have : Nonempty ι := Nonempty.map ε.symm inferInstance
  have : IsIntegral Q := Proj.isIntegral_polynomialProj
  have : Finite ι := Finite.of_equiv (Fin 3) ε.symm
  have : IsLocallyNoetherian Q := LocallyOfFiniteType.isLocallyNoetherian (Q ↘ Spec (.of k))
  have : Flat f := f.flat_of_isFinite_to_projectivePlane hX ε
  have hrank := f.classIntersectionNumber_pullback_twistingSheaf_projectivePlane hX ε
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [hrank (genericPoint Q), finrank_eq_one_of_isIso, Pi.one_apply, Nat.cast_one]
  · have h₁ (y : Q) : f.finrank y = 1 := by exact_mod_cast (hrank y).symm.trans h
    exact (f.isIso_iff_finrank_eq).mpr (funext h₁)

end AlgebraicGeometry.Scheme.Hom

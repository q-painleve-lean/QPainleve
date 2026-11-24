/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.ProjectivePlane.Basic
public import QPainleve.AlgebraicGeometry.Chow.ProperIntersection
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Basic
public import TauCeti.AlgebraicGeometry.Scheme.Normal

import QPainleve.AlgebraicGeometry.Chow.Isomorphism
import QPainleve.AlgebraicGeometry.Morphisms.Finite
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Integral
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Smooth
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Normal
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

/-!
# Finite maps of surfaces to the projective plane

A finite map from a normal projective surface to the projective plane is flat
by miracle flatness. Intersecting the inverse images of two coordinate lines
computes its rank from the square of the pulled-back hyperplane class. The rank
one criterion identifies a square-one finite linear-system map with an
isomorphism to the plane.

The degree-one construction occurs in Ravi Vakil, *Complex Algebraic Surfaces*,
Class 17, §2. The rank computation uses the finite flat projection formula
for properly meeting Cartier divisors.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Chow
open TauCeti.AlgebraicGeometry.LineBundleClass
open TauCeti.SymmetricAlgebra

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 3) k
local notation "P" => Proj 𝒜
local notation "H" => LineBundleClass.mk (Proj.polynomialTwistingBundle (k := k) (n := 2) 1)

@[instance_reducible, local instance]
private def polynomialPlaneOver : (P).Over S := ⟨Proj.toSpecCoeff 𝒜⟩

private theorem isProjectiveOver_polynomialPlane : (P).IsProjectiveOver k := by
  let b := Pi.basisFun k (Fin 3)
  have : b.polynomialProjIso.hom.IsOver S := ⟨b.polynomialProjIso_hom_over⟩
  exact Scheme.IsProjectiveOver.of_isClosedImmersion k b.polynomialProjIso.hom

private theorem classIntersectionNumber_polynomialTwistingBundle :
    classIntersectionNumber k P H H = 1 := by
  let b := Pi.basisFun k (Fin 3)
  let E := b.polynomialProjIso
  let H' := Proj.symmetricAlgebraTwistingBundle k (Fin 3 → k) 1
  have : E.hom.IsOver S := ⟨by
    rw [over_eq_projToSpec, b.polynomialProjIso_hom_over]
    rfl⟩
  have hH : pullback E.hom (LineBundleClass.mk H') = H :=
    b.pullback_mk_symmetricAlgebraTwistingBundle 1 (Proj.polynomialTwistingBundle 1)
      (Proj.polynomialTwistingBundle_obj (k := k) (n := 2) 1)
  rw [← hH, classIntersectionNumber_pullback_of_isIso k E.hom,
    classIntersectionNumber_projectivePlane, Module.Basis.picardTwistEquiv_apply_twist]
  norm_num

variable {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X]

private theorem flat_of_finite_to_polynomialPlane (f : X ⟶ P) [IsFinite f]
    (hX : topologicalKrullDim X = 2) : Flat f := by
  have : IsIntegral P := Proj.isIntegral_polynomialProj
  have hrel : SmoothOfRelativeDimension 2 (P ↘ S) :=
    Proj.smoothOfRelativeDimension_toSpecCoeff k 2
  have hP := topologicalKrullDim_eq_of_smoothOfRelativeDimension (P ↘ S) (n := 2)
  have : Smooth (P ↘ S) := hrel.smooth
  have : IsDominant f :=
    f.isDominant_of_isFinite_of_topologicalKrullDim_le (by rw [hP]; decide) (hP.trans hX.symm).le
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (P ↘ S)
  have : ∀ y : P, IsRegularLocalRing ((P).presheaf.stalk y) :=
    isRegularLocalRing_stalk_of_smooth (P ↘ S)
  exact f.flat_of_isDominant_of_locallyQuasiFinite_of_ringKrullDim_le_two fun y ↦ by
    rw [ringKrullDim_stalk_eq_coheight]
    exact_mod_cast (coheight_le_topologicalKrullDim y).trans hP.le

variable [Infinite k] [X.Over (Spec (.of k))] [X.IsProjectiveOver k]

/-- The square of the pulled-back hyperplane class of a finite map from a normal
projective surface to the projective plane equals the degree of the map. -/
theorem classIntersectionNumber_pullback_polynomialTwistingBundle
    (f : X ⟶ P) [IsFinite f] (hf : f ≫ Proj.toSpecCoeff 𝒜 = X ↘ S)
    (hX : topologicalKrullDim X = 2) (p : P) :
    classIntersectionNumber k X (pullback f H) (pullback f H) = f.finrank p := by
  have : IsIntegral P := Proj.isIntegral_polynomialProj
  have : (P).IsProjectiveOver k := isProjectiveOver_polynomialPlane
  have : f.IsOver S := ⟨hf⟩
  have : SmoothOfRelativeDimension 2 (P ↘ S) := Proj.smoothOfRelativeDimension_toSpecCoeff k 2
  have hP := topologicalKrullDim_eq_of_smoothOfRelativeDimension (P ↘ S) (n := 2)
  have : Smooth (P ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (P ↘ S)
  have : Flat f := flat_of_finite_to_polynomialPlane f hX
  have hrank (y : P) : f.finrank y = f.finrank p :=
    f.isLocallyConstant_finrank.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial
  have h := classIntersectionNumber_pullback_of_finite_flat k hX.le hP.le f
    (Proj.isEffectiveCartier_coordinateHyperplaneIdeal (0 : Fin 3))
    (Proj.isEffectiveCartier_coordinateHyperplaneIdeal (1 : Fin 3))
    (Proj.isEffectiveCartier_comap_coordinateHyperplaneIdeal (by decide : (0 : Fin 3) ≠ 1))
    (f.finrank p) hrank
  simpa only [LineBundleClass.inv_mk, Proj.mk_dual_coordinateHyperplaneIdeal,
    classIntersectionNumber_polynomialTwistingBundle, mul_one] using h

/-- A finite morphism from a normal projective surface to the projective plane is
an isomorphism if the pullback of the hyperplane class has self-intersection one.
The coordinate indexing can be any type equipped with a bijection to `Fin 3`. -/
theorem isIso_of_finite_pullback_hyperplane_square_one {ι : Type u}
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule ι k)) [f.IsOver S] [IsFinite f]
    (e : ι ≃ Fin 3) (hX : topologicalKrullDim X = 2)
    (L : InvertibleSheaf (Proj (MvPolynomial.homogeneousSubmodule ι k)))
    (hL : L.obj = Proj.twistingSheaf _ 1)
    (h : classIntersectionNumber k X (pullback f (LineBundleClass.mk L))
      (pullback f (LineBundleClass.mk L)) = 1) :
    IsIso f := by
  let b := Pi.basisFun k (Fin 3)
  let c := b.reindex e.symm
  let E := c.polynomialProjIso ≪≫ b.polynomialProjIso.symm
  let g := f ≫ E.hom
  have hE : E.hom.IsOver S := ⟨by
    have htarget : P ↘ S = Proj.toSpecCoeff 𝒜 := rfl
    rw [Iso.trans_hom, Category.assoc, htarget,
      ← b.polynomialProjIso_hom_over, Iso.symm_hom, Iso.inv_hom_id_assoc,
      c.polynomialProjIso_hom_over, Proj.over_polynomial]⟩
  have hg : pullback E.hom H = LineBundleClass.mk L := by
    let H' := Proj.symmetricAlgebraTwistingBundle k (Fin 3 → k) 1
    have hb : pullback b.polynomialProjIso.hom (LineBundleClass.mk H') = H :=
      b.pullback_mk_symmetricAlgebraTwistingBundle 1 (Proj.polynomialTwistingBundle 1)
        (Proj.polynomialTwistingBundle_obj (k := k) (n := 2) 1)
    rw [← hb, pullback_comp]
    simpa only [E, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] using c.pullback_mk_symmetricAlgebraTwistingBundle 1 L hL
  have hs : classIntersectionNumber k X (pullback g H) (pullback g H) = 1 := by
    simpa only [g, ← pullback_comp, hg] using h
  have hr (p : P) : g.finrank p = 1 := by
    have hdegree := g.classIntersectionNumber_pullback_polynomialTwistingBundle
      (comp_over g S) hX p
    exact_mod_cast hdegree.symm.trans hs
  have : Flat g := flat_of_finite_to_polynomialPlane g hX
  have : IsIso g := (g.isIso_iff_finrank_eq).mpr (funext hr)
  exact IsIso.of_isIso_comp_right f E.hom

end AlgebraicGeometry.Scheme.Hom

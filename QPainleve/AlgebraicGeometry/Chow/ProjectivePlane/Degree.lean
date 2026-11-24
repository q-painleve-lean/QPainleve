/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import QPainleve.AlgebraicGeometry.Chow.ProjectivePlane.Basic
public import QPainleve.AlgebraicGeometry.Chow.ProperIntersection
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Flat
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.TwistingSheaf
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Basic
public import TauCeti.AlgebraicGeometry.Scheme.Normal

import QPainleve.AlgebraicGeometry.Chow.Isomorphism
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Integral
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Smooth
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank
import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

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

variable {X : Scheme.{u}} [Infinite k] [X.Over (Spec (.of k))] [X.IsProjectiveOver k] in
private theorem classIntersectionNumber_pullback_polynomialTwistingBundle_of_flat
    (f : X ⟶ P) [f.IsOver S] [IsFinite f] [Flat f] (p : P) :
    classIntersectionNumber k X (pullback f H) (pullback f H) = f.finrank p := by
  have : IsIntegral P := Proj.isIntegral_polynomialProj
  have : (P).IsProjectiveOver k := isProjectiveOver_polynomialPlane
  have : SmoothOfRelativeDimension 2 (P ↘ S) := Proj.smoothOfRelativeDimension_toSpecCoeff k 2
  have hP := topologicalKrullDim_eq_of_smoothOfRelativeDimension (P ↘ S) (n := 2)
  have : Smooth (P ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (P ↘ S)
  have hrank (y : P) : f.finrank y = f.finrank p :=
    f.isLocallyConstant_finrank.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial
  have h := classIntersectionNumber_pullback_of_finite_flat k
    (f.topologicalKrullDim_le.trans hP.le) hP.le f
    (Proj.isEffectiveCartier_coordinateHyperplaneIdeal (0 : Fin 3))
    (Proj.isEffectiveCartier_coordinateHyperplaneIdeal (1 : Fin 3))
    (Proj.isEffectiveCartier_comap_coordinateHyperplaneIdeal (by decide : (0 : Fin 3) ≠ 1))
    (f.finrank p) hrank
  simpa only [LineBundleClass.inv_mk, Proj.mk_dual_coordinateHyperplaneIdeal,
    classIntersectionNumber_polynomialTwistingBundle, mul_one] using h

variable {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X] [Infinite k]
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]

/-- The square of the pulled-back hyperplane class of a finite map from a normal
projective surface to the projective plane equals the degree of the map. -/
theorem classIntersectionNumber_pullback_polynomialTwistingBundle
    (f : X ⟶ P) [IsFinite f] (hf : f ≫ Proj.toSpecCoeff 𝒜 = X ↘ S)
    (hX : topologicalKrullDim X = 2) (p : P) :
    classIntersectionNumber k X (pullback f H) (pullback f H) = f.finrank p := by
  have : f.IsOver S := ⟨hf⟩
  have : Flat f := f.flat_of_isFinite_to_polynomialPlane hX.ge
  exact f.classIntersectionNumber_pullback_polynomialTwistingBundle_of_flat p

variable {ι : Type u}

local notation "𝒬" => MvPolynomial.homogeneousSubmodule ι k
local notation "Q" => Proj 𝒬
local notation "H₀" => LineBundleClass.mk
  (ObjectProperty.FullSubcategory.mk (Proj.twistingSheaf 𝒬 1) inferInstance : InvertibleSheaf Q)

/-- The square of the pullback of `𝒪(1)` by a finite morphism from a normal projective
surface to the plane is the degree, computed as the rank at any point of the plane.
The coordinate index type can be any type equivalent to `Fin 3`. -/
theorem classIntersectionNumber_pullback_twistingSheaf_projectivePlane (f : X ⟶ Q)
    [f.IsOver S] [IsFinite f] (hX : 2 ≤ topologicalKrullDim X) (ε : ι ≃ Fin 3) (p : Q) :
    classIntersectionNumber k X (pullback f H₀) (pullback f H₀) = f.finrank p := by
  let b := Pi.basisFun k (Fin 3)
  let c := b.reindex ε.symm
  let E := QPainleve.polynomialPlaneIso (k := k) ε
  let g := f ≫ E.hom
  have hE : E.hom.IsOver S := ⟨by
    change (c.polynomialProjIso.hom ≫ b.polynomialProjIso.inv) ≫ Proj.toSpecCoeff 𝒜 =
      Proj.toSpecCoeff 𝒬
    rw [Category.assoc, ← b.polynomialProjIso_hom_over, Iso.inv_hom_id_assoc,
      c.polynomialProjIso_hom_over]⟩
  have hH : pullback E.hom H = H₀ := by
    let H' := Proj.symmetricAlgebraTwistingBundle k (Fin 3 → k) 1
    have hb : pullback b.polynomialProjIso.hom (LineBundleClass.mk H') = H :=
      b.pullback_mk_symmetricAlgebraTwistingBundle 1 (Proj.polynomialTwistingBundle 1)
        (Proj.polynomialTwistingBundle_obj (k := k) (n := 2) 1)
    rw [← hb, pullback_comp]
    change pullback ((c.polynomialProjIso.hom ≫ b.polynomialProjIso.inv) ≫
      b.polynomialProjIso.hom) (LineBundleClass.mk H') = H₀
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact c.pullback_mk_symmetricAlgebraTwistingBundle 1 _ rfl
  have : Flat f := f.flat_of_isFinite_to_projectivePlane hX ε
  have : g.IsOver S := inferInstanceAs ((f ≫ E.hom).IsOver S)
  have : IsFinite g := inferInstanceAs (IsFinite (f ≫ E.hom))
  have : Flat g := inferInstanceAs (Flat (f ≫ E.hom))
  rw [← hH, pullback_comp,
    g.classIntersectionNumber_pullback_polynomialTwistingBundle_of_flat (E.hom p)]
  exact_mod_cast f.finrank_comp_right_of_isIso E.hom p

/-- A finite morphism from a normal projective surface to the projective plane is
an isomorphism exactly when the pullback of the hyperplane class has square one. -/
theorem isIso_iff_hyperplane_pullback_square_eq_one (f : X ⟶ Q)
    [f.IsOver S] [IsFinite f] (hX : 2 ≤ topologicalKrullDim X) (ε : ι ≃ Fin 3) :
    IsIso f ↔ classIntersectionNumber k X (pullback f H₀) (pullback f H₀) = 1 := by
  have : Nonempty ι := Nonempty.map ε.symm inferInstance
  have : IsIntegral Q := Proj.isIntegral_polynomialProj
  have : Finite ι := Finite.of_equiv (Fin 3) ε.symm
  have : IsLocallyNoetherian Q := LocallyOfFiniteType.isLocallyNoetherian (Q ↘ S)
  have : Flat f := f.flat_of_isFinite_to_projectivePlane hX ε
  have hrank := f.classIntersectionNumber_pullback_twistingSheaf_projectivePlane hX ε
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [hrank (genericPoint Q), finrank_eq_one_of_isIso, Pi.one_apply, Nat.cast_one]
  · have h₁ (p : Q) : f.finrank p = 1 := by exact_mod_cast (hrank p).symm.trans h
    exact (f.isIso_iff_finrank_eq).mpr (funext h₁)

end AlgebraicGeometry.Scheme.Hom

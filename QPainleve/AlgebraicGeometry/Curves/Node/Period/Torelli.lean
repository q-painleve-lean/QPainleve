/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import QPainleve.Geometry.Toric.Fan.Picard.Period.Torelli

import QPainleve.AlgebraicGeometry.Chow.NegativeCurve
import QPainleve.Geometry.Toric.Fan.Presentation.Induction

/-!
# Signed Torelli for root-free anticanonical pairs

A Picard isometry matching the boundary classes and signed periods and taking an
ample class to an ample class lifts to a pair isomorphism. The isomorphism
realizes the given dihedral action on the branches, including for boundaries
with one or two components. For nef boundaries of square zero, the ample-class
condition follows from the boundary class comparison.

The proof combines toric presentation existence and the ordered reconstruction
for a torically presented source. This gives the root-free case of
[Gross, Hacking and Keel, Theorem 1.8][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup Multiplicative QPainleve
open TauCeti.AlgebraicGeometry TauCeti.Toric LineBundleClass

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀] [NeZero (2 : k₀)]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "g(" X ")" => (X ↘ S)
local notation "K(" X ")" => LineBundleClass.mk (canonicalBundle k₀ X 2)
local notation "P(" D "," p ")" => Additive.ofMul (primeDivisorClass (boundaryPrimeEmbedding D p))

local macro "withRationalSurface[" k:term "," X:term "," body:term "]" : term =>
  `(let f := $X ↘ Spec (CommRingCat.of $k)
    letI : Smooth f := SmoothOfRelativeDimension.smooth 2 f
    letI : IsIntegral $X := (inferInstance : Scheme.IsRationalOver f).isIntegral_of_smooth
    letI : IsNoetherian $X := isNoetherian_of_finiteType f
    letI : ∀ x : $X, UniqueFactorizationMonoid (($X).presheaf.stalk x) :=
      f.uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    $body)

variable {X Y : Scheme} [X.Over (Spec (.of k₀))] [Y.Over (Spec (.of k₀))] [X.IsProjectiveOver k₀]
  [Y.IsProjectiveOver k₀]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k₀))] [SmoothOfRelativeDimension 2 (Y ↘ Spec
    (.of k₀))]
  [Scheme.IsRationalOver (X ↘ Spec (.of k₀))] [Scheme.IsRationalOver (Y ↘ Spec (.of k₀))]
  (D : X.IdealSheafData) {E : Y.IdealSheafData}
  [PrestableFamily (D.subscheme ↘ Spec (.of k₀))] [PrestableFamily (E.subscheme ↘ Spec (.of k₀))]
  {n : ℕ} [NeZero n] {ι κ : Type}
  {p : ι → (D.subscheme ↘ Spec (.of k₀)).smoothLocus} {q : κ →
    (E.subscheme ↘ Spec (.of k₀)).smoothLocus}
  (A : Scheme.NodalCycleNumbering p n) (C : Scheme.NodalCycleNumbering q n)
  (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
  (act : DihedralGroup n)

include A C act hD hE in
/-- Signed Torelli for anticanonical pairs without internal `(-2)`-curves.
A Picard isometry sending one ample class to an ample class, matching the
specified boundary components and intertwining the signed periods is induced
by a pair isomorphism with the given action on the ordered branches. -/
theorem exists_pair_iso_of_root_free_signed_boundary_period
    (G : withRationalSurface[k₀,X,withRationalSurface[k₀,Y,LinearMap.BilinForm.IsometryEquiv
      (Chow.intersectionBilinForm k₀ Y) (Chow.intersectionBilinForm k₀ X)]])
  (hclass : withRationalSurface[k₀,X,withRationalSurface[k₀,Y,∀ j, G P(E,C.boundaryPrimeEquiv hE
    (cycleVertexPerm act j)) =
    P(D,A.boundaryPrimeEquiv hD j)]])
  (hcanD : LineBundleClass.mk hD.toInvertibleSheaf = K(X))
  (hcanE : LineBundleClass.mk hE.toInvertibleSheaf = K(Y))
  (hrootD : withRationalSurface[k₀,X,∀ r : CodimensionOnePoint X,
    Disjoint (closure {(r : X)}) D.support →
    Chow.classIntersectionNumber k₀ X (primeDivisorClass r) (primeDivisorClass r) ≠ -2])
  (hrootE : withRationalSurface[k₀,Y,∀ r : CodimensionOnePoint Y,
    Disjoint (closure {(r : Y)}) E.support →
    Chow.classIntersectionNumber k₀ Y (primeDivisorClass r) (primeDivisorClass r) ≠ -2])
  (gD : ∀ w : irreducibleComponents (D.subscheme.singularLocus k₀).blowup,
    (D.subscheme.blowupComponent (K := k₀) w).toScheme.genus k₀ = 0)
  (gE : ∀ w : irreducibleComponents (E.subscheme.singularLocus k₀).blowup,
    (E.subscheme.blowupComponent (K := k₀) w).toScheme.genus k₀ = 0)
  (hperiod : withRationalSurface[k₀,X,withRationalSurface[k₀,Y,∀ (x : E.boundaryOrthogonal k₀)
    (y : D.boundaryOrthogonal k₀), G x.val = y.val →
    hE.boundaryPeriod gE C.endpoint_eq (ofAdd x) =
      hD.boundaryPeriod gD A.endpoint_eq (ofAdd y) ^ (cycleOrientationSign act : ℤ)]])
    {H : LineBundleClass Y} (hH : H.IsAmple) (hGH : (G (Additive.ofMul H)).toMul.IsAmple) :
    Nonempty (SignedTorelliPairIso (D := D) (E := E) A C
      (fun L ↦ (G (Additive.ofMul L)).toMul) act) :=
  withRationalSurface[k₀,X,withRationalSurface[k₀,Y,by
  have hpres := D.hasToricPresentation_of_anticanonical_cycle k₀ (Pi.basisFun ℤ (Fin 2))
    (isIntegralLattice_intCast 2) A hD hcanD
  exact D.exists_pair_iso_of_root_free_signed_boundary_period_of_toric_presentation
    k₀ A C hD hE act G hclass hcanD hcanE
    (Chow.prime_self_intersection_ne_neg_two_off_boundary k₀ hD hcanD hrootD)
    (Chow.prime_self_intersection_ne_neg_two_off_boundary k₀ hE hcanE hrootE)
    gD gE hperiod hpres hH hGH]]

include A C act hD hE in
/-- For root-free pairs with nef anticanonical boundary of square zero,
compatibility of the boundary classes and signed periods suffices to realize
the prescribed Picard pullback and branch action. -/
theorem exists_pair_iso_of_root_free_signed_boundary_period_of_nef
    (G : withRationalSurface[k₀,X,withRationalSurface[k₀,Y,LinearMap.BilinForm.IsometryEquiv
      (Chow.intersectionBilinForm k₀ Y) (Chow.intersectionBilinForm k₀ X)]])
  (hclass : withRationalSurface[k₀,X,withRationalSurface[k₀,Y,∀ j, G P(E,C.boundaryPrimeEquiv hE
    (cycleVertexPerm act j)) =
    P(D,A.boundaryPrimeEquiv hD j)]])
  (hcanD : LineBundleClass.mk hD.toInvertibleSheaf = K(X))
  (hcanE : LineBundleClass.mk hE.toInvertibleSheaf = K(Y))
  (hrootD : withRationalSurface[k₀,X,∀ r : CodimensionOnePoint X,
    Disjoint (closure {(r : X)}) D.support →
    Chow.classIntersectionNumber k₀ X (primeDivisorClass r) (primeDivisorClass r) ≠ -2])
  (hrootE : withRationalSurface[k₀,Y,∀ r : CodimensionOnePoint Y,
    Disjoint (closure {(r : Y)}) E.support →
    Chow.classIntersectionNumber k₀ Y (primeDivisorClass r) (primeDivisorClass r) ≠ -2])
  (gD : ∀ w : irreducibleComponents (D.subscheme.singularLocus k₀).blowup,
    (D.subscheme.blowupComponent (K := k₀) w).toScheme.genus k₀ = 0)
  (gE : ∀ w : irreducibleComponents (E.subscheme.singularLocus k₀).blowup,
    (E.subscheme.blowupComponent (K := k₀) w).toScheme.genus k₀ = 0)
  (hperiod : withRationalSurface[k₀,X,withRationalSurface[k₀,Y,∀ (x : E.boundaryOrthogonal k₀)
    (y : D.boundaryOrthogonal k₀), G x.val = y.val →
    hE.boundaryPeriod gE C.endpoint_eq (ofAdd x) =
      hD.boundaryPeriod gD A.endpoint_eq (ofAdd y) ^ (cycleOrientationSign act : ℤ)]])
    (hnefD : (K(X))⁻¹.IsNef k₀ g(X)) (hnefE : (K(Y))⁻¹.IsNef k₀ g(Y))
    (hsq : Chow.classIntersectionNumber k₀ Y (K(Y))⁻¹ (K(Y))⁻¹ = 0) :
    Nonempty (SignedTorelliPairIso (D := D) (E := E) A C
      (fun L ↦ (G (Additive.ofMul L)).toMul) act) :=
  withRationalSurface[k₀,X,withRationalSurface[k₀,Y,by
  have hpres := D.hasToricPresentation_of_anticanonical_cycle k₀ (Pi.basisFun ℤ (Fin 2))
    (isIntegralLattice_intCast 2) A hD hcanD
  exact D.exists_pair_iso_of_root_free_signed_boundary_period_of_toric_presentation_of_nef
    k₀ A C hD hE act G hclass hcanD hcanE
    (Chow.prime_self_intersection_ne_neg_two_off_boundary k₀ hD hcanD hrootD)
    (Chow.prime_self_intersection_ne_neg_two_off_boundary k₀ hE hcanE hrootE)
    gD gE hperiod hpres hnefD hnefE hsq]]

end AlgebraicGeometry.Scheme.IdealSheafData

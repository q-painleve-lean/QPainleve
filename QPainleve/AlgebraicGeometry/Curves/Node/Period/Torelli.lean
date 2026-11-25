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

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "g(" X ")" => (X ↘ S)
local notation "B(" X ")" => Chow.intersectionBilinForm ℂ X
local notation "K(" X ")" => LineBundleClass.mk (canonicalBundle ℂ X 2)
local notation "P(" D "," p ")" => Additive.ofMul (primeDivisorClass (boundaryPrimeEmbedding D p))

attribute [local instance] smoothRationalSurface integralRationalSurface noetherianRationalSurface
  factorialRationalSurface

variable {X Y : Scheme} [X.Over S] [Y.Over S] [X.IsProjectiveOver ℂ] [Y.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 g(X)] [SmoothOfRelativeDimension 2 g(Y)]
  [Scheme.IsRationalOver g(X)] [Scheme.IsRationalOver g(Y)]
  (D : X.IdealSheafData) {E : Y.IdealSheafData}
  [PrestableFamily g(D.subscheme)] [PrestableFamily g(E.subscheme)]
  {n : ℕ} [NeZero n] {ι κ : Type}
  {p : ι → g(D.subscheme).smoothLocus} {q : κ → g(E.subscheme).smoothLocus}
  (A : Scheme.NodalCycleNumbering p n) (C : Scheme.NodalCycleNumbering q n)
  (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
  (act : DihedralGroup n) (G : B(Y).IsometryEquiv B(X))
  (hclass : ∀ j, G P(E,C.boundaryPrimeEquiv hE (cycleVertexPerm act j)) =
    P(D,A.boundaryPrimeEquiv hD j))

variable
  (hcanD : LineBundleClass.mk hD.toInvertibleSheaf = K(X))
  (hcanE : LineBundleClass.mk hE.toInvertibleSheaf = K(Y))
  (hrootD : ∀ r : CodimensionOnePoint X, Disjoint (closure {(r : X)}) D.support →
    Chow.classIntersectionNumber ℂ X (primeDivisorClass r) (primeDivisorClass r) ≠ -2)
  (hrootE : ∀ r : CodimensionOnePoint Y, Disjoint (closure {(r : Y)}) E.support →
    Chow.classIntersectionNumber ℂ Y (primeDivisorClass r) (primeDivisorClass r) ≠ -2)
  (gD : ∀ w : irreducibleComponents (D.subscheme.singularLocus ℂ).blowup,
    (D.subscheme.blowupComponent (K := ℂ) w).toScheme.genus ℂ = 0)
  (gE : ∀ w : irreducibleComponents (E.subscheme.singularLocus ℂ).blowup,
    (E.subscheme.blowupComponent (K := ℂ) w).toScheme.genus ℂ = 0)
  (hperiod : ∀ (x : E.boundaryOrthogonal ℂ) (y : D.boundaryOrthogonal ℂ), G x.val = y.val →
    hE.boundaryPeriod gE C.endpoint_eq (ofAdd x) =
      hD.boundaryPeriod gD A.endpoint_eq (ofAdd y) ^ (cycleOrientationSign act : ℤ))

include A C G act hD hE hcanD hcanE hrootD hrootE hclass gD gE hperiod in
/-- Signed Torelli for anticanonical pairs without internal `(-2)`-curves.
A Picard isometry sending one ample class to an ample class, matching the
specified boundary components and intertwining the signed periods is induced
by a pair isomorphism with the given action on the ordered branches. -/
theorem exists_pair_iso_of_root_free_signed_boundary_period
    {H : LineBundleClass Y} (hH : H.IsAmple) (hGH : (G (Additive.ofMul H)).toMul.IsAmple) :
    ∃ (a : X ≅ Y) (aB : D.subscheme ≅ E.subscheme) (haB : aB.hom.IsOver S),
      a.hom ≫ g(Y) = g(X) ∧ E.comap a.hom = D ∧
      aB.hom ≫ E.subschemeι = D.subschemeι ≫ a.hom ∧
      (∀ L : LineBundleClass Y, pullback a.hom L = (G (Additive.ofMul L)).toMul) ∧
      (letI := haB; aB.boundaryCycleAction (k := ℂ) A C = act) := by
  have hpres := Fan.hasToricPresentation_of_ruled_reduction (b := Pi.basisFun ℤ (Fin 2))
    (isIntegralLattice_intCast 2) A hD hcanD
  exact D.exists_pair_iso_of_root_free_signed_boundary_period_of_toric_presentation
    A C hD hE act G hclass hcanD hcanE
    (Chow.prime_self_intersection_ne_neg_two_off_boundary ℂ hD hcanD hrootD)
    (Chow.prime_self_intersection_ne_neg_two_off_boundary ℂ hE hcanE hrootE)
    gD gE hperiod hpres hH hGH

include A C G act hD hE hcanD hcanE hrootD hrootE hclass gD gE hperiod in
/-- For root-free pairs with nef anticanonical boundary of square zero,
compatibility of the boundary classes and signed periods suffices to realize
the prescribed Picard pullback and branch action. -/
theorem exists_pair_iso_of_root_free_signed_boundary_period_of_nef
    (hnefD : (K(X))⁻¹.IsNef ℂ g(X)) (hnefE : (K(Y))⁻¹.IsNef ℂ g(Y))
    (hsq : Chow.classIntersectionNumber ℂ Y (K(Y))⁻¹ (K(Y))⁻¹ = 0) :
    ∃ (a : X ≅ Y) (aB : D.subscheme ≅ E.subscheme) (haB : aB.hom.IsOver S),
      a.hom ≫ g(Y) = g(X) ∧ E.comap a.hom = D ∧
      aB.hom ≫ E.subschemeι = D.subschemeι ≫ a.hom ∧
      (∀ L : LineBundleClass Y, pullback a.hom L = (G (Additive.ofMul L)).toMul) ∧
      (letI := haB; aB.boundaryCycleAction (k := ℂ) A C = act) := by
  have hpres := Fan.hasToricPresentation_of_ruled_reduction (b := Pi.basisFun ℤ (Fin 2))
    (isIntegralLattice_intCast 2) A hD hcanD
  exact D.exists_pair_iso_of_root_free_signed_boundary_period_of_toric_presentation_of_nef
    A C hD hE act G hclass hcanD hcanE
    (Chow.prime_self_intersection_ne_neg_two_off_boundary ℂ hD hcanD hrootD)
    (Chow.prime_self_intersection_ne_neg_two_off_boundary ℂ hE hcanE hrootE)
    gD gE hperiod hpres hnefD hnefE hsq

end AlgebraicGeometry.Scheme.IdealSheafData

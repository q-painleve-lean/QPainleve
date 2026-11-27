/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Cremona.Identification

import QPainleve.Geometry.Toric.Fan.Presentation.Canonical
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Identification

/-!
# Cremona isometries from ordered toric presentations

For an ordered toric presentation of a primitive nef square-zero anticanonical
cycle without internal `(-2)` curves, Picard pullback projects the opposite
signed cluster modular group onto the Cremona isometries of the original
surface. The identification records the marked family and the specified
toric data. With one or two boundary components, the signed group retains
the branch sign and the unsigned group identifies with the Cremona group.
-/

public section

open AlgebraicGeometry CategoryTheory Module
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀] [Uncountable k₀] [NeZero (2 : k₀)]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "δ[" h "]" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N}
  {X : Scheme} [X.Over (Spec (.of k₀))] [X.IsProjectiveOver k₀]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k₀))] [Scheme.IsRationalOver (X ↘ Spec (.of k₀))]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ Spec (.of k₀))]
  {n r : ℕ} [NeZero n]

/-- The opposite signed cluster modular group of specified ordered toric and
nodal blowup towers projects onto the Cremona isometries of the original surface
without internal `(-2)` curves.
For at least three boundary components the projection is an equivalence. For
one or two components the projection and the sign form a product equivalence,
with the unsigned group mapping isomorphically to the Cremona factor. On loops
the maps evaluate by the realized Picard pullback and inversion sign. -/
theorem exists_cluster_cremona_equivs_of_toric_presentation
    (P : D.ToricPresentation (X ↘ S) b i r)
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (hD : D.IsEffectiveCartier)
    (hprim : IsPrimitive (Additive.ofMul δ[hD])) (hnef : δ[hD].IsNef k₀ (X ↘ S))
    (hsq : Chow.classIntersectionNumber k₀ X δ[hD] δ[hD] = 0) :
    letI : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    letI : IsIntegral X := (inferInstance : Scheme.IsRationalOver (X ↘ S)).isIntegral_of_smooth
    letI : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
    letI := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (∀ p : CodimensionOnePoint X, Disjoint (closure {(p : X)}) D.support →
      Chow.classIntersectionNumber k₀ X (LineBundleClass.primeDivisorClass p)
        (LineBundleClass.primeDivisorClass p) ≠ -2) →
    ∃ R : FiniteMarkedReferenceFiber i r A,
      R.reference.HasToricData P ∧ Nonempty (CremonaGroupIdentification R hD) := by
  let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsIntegral X := (inferInstance : Scheme.IsRationalOver (X ↘ S)).isIntegral_of_smooth
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  intro hroot
  have hK := P.hasToricPresentation.canonicalClass hD (by
    rw [← over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne)
  obtain ⟨R, hR, ⟨Q⟩⟩ := exists_picardGroupEquivs_of_toric_presentation P A hD hprim hnef hsq
  exact ⟨R, hR, ⟨⟨Q, hK, hnef, hsq, hroot⟩⟩⟩

end QPainleve.SignedClusterModularGroup

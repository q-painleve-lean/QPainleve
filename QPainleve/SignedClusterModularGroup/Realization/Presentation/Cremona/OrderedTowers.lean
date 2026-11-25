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
open QPainleve.BlowupTower QPainleve.CharacterTorus
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "δ[" h "]" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "parameters[" c "]" => (fun j ↦ χ[c] (Multiplicative.ofAdd (Pi.single j 1)))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {Φ : Fan i}
  {X W : Scheme} [X.Over S] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ S)] [Scheme.IsRationalOver (X ↘ S)]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)]
  {n r k : ℕ} [NeZero n] {T : BlowupTower X k W}

local instance instIntegralOrderedCremona : IsIntegral X := by
  let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  exact Scheme.IsRationalOver.isIntegral_of_smooth (f := X ↘ S) inferInstance

/-- The opposite signed cluster modular group of specified ordered toric and
nodal blowup towers projects onto the Cremona isometries of the original surface
without internal `(-2)` curves.
For at least three boundary components the projection is an equivalence. For
one or two components the projection and the sign form a product equivalence,
with the unsigned group mapping isomorphically to the Cremona factor. On loops
the maps evaluate by the realized Picard pullback and inversion sign. -/
theorem exists_cluster_cremona_equivs_of_toric_presentation
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (s : Fin r → Φ.Ray) (u : Fin r → ℂˣ)
    (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (e : (Fan.internalBlowupTower (h₀ := hc.nonempty_cones) b s u).1 ≅ W)
    (hbase : e.hom ≫ T.toBase ≫ (X ↘ S) =
      (Fan.internalBlowupTower (h₀ := hc.nonempty_cones) b s u).2.toTower.toBase ≫
        Φ.algebraicRealizationStructureMap)
    (hker : ((D.comap T.toBase).radical).comap e.hom =
      (Fan.internalBlowupTower (h₀ := hc.nonempty_cones) b s u).2.boundaryι.ker)
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (hD : D.IsEffectiveCartier)
    (hprim : IsPrimitive (Additive.ofMul δ[hD])) (hnef : δ[hD].IsNef ℂ (X ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ X δ[hD] δ[hD] = 0) :
    letI : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
    letI := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (∀ p : CodimensionOnePoint X, Disjoint (closure {(p : X)}) D.support →
      Chow.classIntersectionNumber ℂ X (LineBundleClass.primeDivisorClass p)
        (LineBundleClass.primeDivisorClass p) ≠ -2) →
    ∃ P : CremonaGroupIdentification i r A hD,
      ((P.picard.basis = b ∧ parameters[P.picard.center] = u) ∨
        (P.picard.basis = b.reindex (Equiv.swap 0 1) ∧ parameters[P.picard.center] = u⁻¹)) ∧
      ∃ hfan : P.picard.presentation.fan = Φ, hfan ▸ P.picard.presentation.rays = s := by
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  intro hroot
  let presentation : D.ToricPresentation (X ↘ S) b i r :=
    ⟨Φ, hΦ, hc, s, u, k, W, T, hT, e, hbase, hker⟩
  have hK := presentation.hasToricPresentation.canonicalClass hD (by
    rw [← over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne)
  obtain ⟨P, hframe, hrays⟩ :=
    exists_picardGroupEquivs_of_toric_presentation presentation A hD hprim hnef hsq
  exact ⟨⟨P, hK, hnef, hsq, hroot⟩, hframe, hrays⟩

end QPainleve.SignedClusterModularGroup

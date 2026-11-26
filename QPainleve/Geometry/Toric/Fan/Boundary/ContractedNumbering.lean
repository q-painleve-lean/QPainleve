/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
public import QPainleve.Geometry.Toric.Fan.Boundary.BlowupNumbering

import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Survivors
import QPainleve.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import QPainleve.Geometry.Toric.Fan.Boundary.Canonical
import QPainleve.Geometry.Toric.Fan.Boundary.InternalBlowup
import QPainleve.Geometry.Toric.Fan.Logarithmic.InternalBlowup

/-!
# Numberings of contracted toric boundaries

A positive ray numbering and an increasing enumeration of surviving rays
determine compatible oriented numberings on the toric boundary and the boundary
after a nodal contraction. The downstairs numbering starts at the first
surviving ray. The subdivision map keeps track of the order of branches even
when only one or two rays survive.

The descent uses
`IsClosedPointTower.exists_numbering_of_anticanonical_boundary_tower_blowdown_of_survivors`.
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones] {r m n d : ℕ}
  [NeZero m] [NeZero n]
  (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (b : Module.Basis (Fin 2) ℤ N)
  (s : Fin r → Φ.Ray) (c : Fin r → ℂˣ) (v : ZMod m ≃ Φ.Ray)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Z" => Φ.algebraicRealization
local notation "C₀" => Scheme.IdealSheafData.subscheme (Φ.boundaryIdeal h₀)
local notation "U" => internalBlowupTower b s c
local notation "J" => WithBoundary.boundaryι (Sigma.snd U)
local notation "B" => Scheme.Hom.ker J
local notation "z" => BlowupTower.toBase (WithBoundary.toTower (Sigma.snd U)) ≫ (Z ↘ S)

variable {X W : Scheme} [X.Over S] [X.IsProjectiveOver ℂ] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ S)] {D : X.IdealSheafData}
  [PrestableFamily (D.subscheme ↘ S)] {T : BlowupTower X d W}
  (hT : IsClosedPointTower X T) (e : (internalBlowupTower b s c).1 ≅ W)

local instance contractedNumbering_noetherian : IsNoetherian X :=
  isNoetherian_of_finiteType (X ↘ S)

local notation "π" => (Iso.hom e ≫ BlowupTower.toBase T)
local notation "prime[" j "]" =>
  internalBlowupBoundaryPrimeEquiv hΦ b s c (v (ZMod.finEquiv m j))

include hT hc in
/-- For a contraction of an ordered internal blowup, simultaneously number
the toric boundary by the supplied cyclic ray order and the contracted boundary
by the supplied increasing enumeration of survivors. The induced boundary map
is an oriented subdivision in these numberings. Each surviving strict ray prime
maps to the corresponding numbered prime downstairs. -/
theorem exists_oriented_numbering_of_contracted_toric_boundary
    (hv : ∀ j, b.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ)
    (he : π ≫ (X ↘ S) = z)
    (hsupp : (D.comap π).support = (B).support) (hD : D.IsEffectiveCartier)
    (a : Fin n ↪o Fin m)
    (ha : ∀ j : Fin m, π ((prime[j]).val) ∈ D.boundaryPrimes ↔ j ∈ Set.range a) :
    ∃ (_ : PrestableFamily (C₀ ↘ S))
      (C : Scheme.NodalCycleNumbering (Empty.elim : Empty → (C₀ ↘ S).smoothLocus) m)
      (A : Scheme.NodalCycleNumbering (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
      (g : C₀ ⟶ D.subscheme),
      Φ.rayEquivOfNodalCycleNumbering hΦ C = v ∧
      ((D.comap T.toBase).radical).comap e.hom = B ∧
      g ≫ D.subschemeι = J ≫ π ∧ g.IsOver S ∧ g.IsOrientedCycleSubdivision C A ∧
      ∀ j : Fin n, π ((prime[a j]).val) = (A.boundaryPrimeEquiv hD (ZMod.finEquiv n j)).val := by
  let : (U).1.Over S := ⟨z⟩
  let : (π).IsOver S := ⟨he⟩
  let : (Z).IsProjectiveOver ℂ := Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
  let : IsNoetherian (U).1 := (U).2.toTower.isNoetherian
  have hdim : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  let : SmoothOfRelativeDimension 2 (Z ↘ S) := (algebraicRealization_over Φ).symm ▸
    (hdim ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ)
  let hU := isClosedPointTower_internalBlowupTower b s c
  let : SmoothOfRelativeDimension 2 ((U).1 ↘ S) := hU.smoothOfRelativeDimension (Z ↘ S)
  let hBase := Φ.isEffectiveCartier_boundaryIdeal hΦ hc hdim
  let hB := isEffectiveCartier_internalBlowupBoundary b s hΦ c hBase
  have hcan := canonicalClass_internalBlowupTower b s c hΦ hBase hB
    (Φ.canonicalClass_boundaryIdeal hΦ hc b hBase)
  obtain ⟨hpreC, hpreB, C, C', hvC, htOver, ht, hprime⟩ :=
    exists_numbering_internalBlowup_of_cyclicRays hΦ hc b s c v hv hB
  let : PrestableFamily (C₀ ↘ S) := hpreC
  let : PrestableFamily ((B).subscheme ↘ S) := hpreB
  let t : C₀ ≅ (B).subscheme := asIso (J).toImage
  let : t.hom.IsOver S := htOver
  have htSub := t.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one C C'
    (by rw [ht, map_one])
  -- The strict boundary is the reduced total transform, and its image is the target boundary.
  let : Surjective T.toBase := hT.surjective (X ↘ S)
  let hsπ : Surjective (e.hom ≫ T.toBase) := inferInstance
  have hredD : IsReduced D.subscheme :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := D.subscheme ↘ S)).isReduced
  obtain ⟨hrad, hmap⟩ :=
    @Scheme.IdealSheafData.radical_comap_eq_and_map_eq_of_support_eq X (U).1
      D π hsπ B hsupp hpreB.atWorstNodalOfRelativeDimensionOne.isReduced hredD
  have hker : ((D.comap T.toBase).radical).comap e.hom = B := by
    rwa [← radical_comap_of_isOpenImmersion, ← comap_comp]
  have ha' (j : Fin m) : π (C'.boundaryPrimeEquiv hB (ZMod.finEquiv m j)).val ∈
      D.boundaryPrimes ↔ j ∈ Set.range a := by simpa only [hprime] using ha j
  subst D
  obtain ⟨_, _, _, A', g', hg', hgOver, hsub, hsurv⟩ :=
    hT.exists_numbering_of_anticanonical_boundary_tower_blowdown_of_survivors
      hB C' a e rfl hcan ha'
  let : g'.IsOver S := hgOver
  -- Change from the descent theorem's empty mark type to the empty type of the toric model.
  let u := Iso.refl ((B).map π).subscheme
  let : u.hom.IsOver S := ⟨Category.id_comp _⟩
  let A := u.mapNodalCycleNumbering A' (q := (Empty.elim : Empty → _))
  have hu := u.boundaryCycleAction_mapNodalCycleNumbering (q := (Empty.elim : Empty → _)) A'
  have hsub' : g'.IsOrientedCycleSubdivision C' A := by
    have huSub := u.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one A' A
      (by rw [hu, map_one])
    simpa only [u, Iso.refl_hom, Category.comp_id] using hsub.comp huSub
  have hj : t.hom ≫ (B).subschemeι = J := (J).toImage_imageι
  refine ⟨hpreC, C, A, t.hom ≫ g', hvC, hker, ?_, inferInstance, htSub.comp hsub', fun j ↦ ?_⟩
  · rw [Category.assoc, hg', ← Category.assoc, hj]
  · have hpoint := u.apply_componentGenericPoint A' A (ZMod.finEquiv n j)
    rw [hu, map_one, Equiv.Perm.one_apply, Iso.refl_hom, Scheme.Hom.id_base, TopCat.coe_id,
      id_eq] at hpoint
    simpa only [hprime, Scheme.NodalCycleNumbering.boundaryPrimeEquiv_apply_val, hpoint]
      using hsurv j

end TauCeti.Toric.Fan

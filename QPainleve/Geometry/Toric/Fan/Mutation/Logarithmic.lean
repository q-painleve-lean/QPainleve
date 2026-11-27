/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Mutation.Tower

import QPainleve.AlgebraicGeometry.Modules.Differentials.PoleIdeal

/-!
# Pole ideals on isomorphic resolutions of toric mutations

A regular projection on a specified resolving surface can be presented by a
closed point tower on an isomorphic surface. The two regular projections of a
toric elementary transformation then have the same pole factorizations on the
specified surface.
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable (K : Type) [Field K] [PerfectField K]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (ρ : Φ.Ray)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : Kˣ)

local notation "S" => Spec (CommRingCat.of K)
local notation "X[" Δ "]" => Fan.finiteFanScheme K Δ
local notation "s[" Δ "]" => (X[Δ] ↘ S)
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "B[" Δ "," h "]" => Fan.toricBoundaryIdeal K Δ (IsComplete.nonempty_cones h)
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)

variable {Y W : Scheme} {n : ℕ} {T : BlowupTower (Φ.finiteFanScheme K) n W}

/-- The pole factorization criterion for a resolved mutation, transported to an
isomorphic resolving surface. The regular mutated projection respects the
structure map determined by the original projection. -/
theorem Ray.mutation_resolution_poleIdeal_iff_of_iso (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hT : IsClosedPointTower X[Φ] T) (e : Y ≅ W) [Y.Over S]
    (he : e.hom ≫ T.toBase ≫ s[Φ] = Y ↘ S)
    (r : W ⟶ X[Ψ]) (D : Y.IdealSheafData) :
    letI : Nonempty Φ.cones := hc.nonempty_cones
    letI : SmoothOfRelativeDimension 2 s[Φ] :=
      (Φ.finiteFanScheme_over K).symm ▸
        (rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ)
    letI : IsIntegral W := hT.isIntegral s[Φ]
    letI : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two s[Φ]
    T.toBase.toRationalMap.comp (Φ.mutationPartialMap K b (c : K) hv hp hOpp).toRationalMap =
      r.toRationalMap →
    let hdimY : SmoothOfRelativeDimension 2 (Y ↘ S) :=
      haveI := (smoothOfRelativeDimension_isStableUnderBaseChange 2).respectsIso
      he ▸ (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 2)
        e.hom (T.toBase ≫ s[Φ])).mpr (hT.smoothOfRelativeDimension s[Φ])
    letI : Smooth (Y ↘ S) := hdimY.smooth
    letI : (e.hom ≫ T.toBase).IsOver S := ⟨(Category.assoc _ _ _).trans he⟩
    ∃ hover : (e.hom ≫ r).IsOver S, letI := hover
      B[Φ,hc].comap (e.hom ≫ T.toBase) = D * ramificationIdealSheaf K (e.hom ≫ T.toBase) ↔
      B[Ψ, (Φ.isComplete_mutationFan_iff b hv hp hOpp).mpr hc].comap (e.hom ≫ r) =
        D * ramificationIdealSheaf K (e.hom ≫ r) := by
  intro hr hdimY
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : SmoothOfRelativeDimension 2 s[Φ] :=
    (Φ.finiteFanScheme_over K).symm ▸
        (rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ)
  let : IsIntegral W := hT.isIntegral s[Φ]
  let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two s[Φ]
  let : W.Over S := ⟨T.toBase ≫ s[Φ]⟩
  let : e.hom.IsOver S := ⟨he⟩
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : SmoothOfRelativeDimension 2 (W ↘ S) := hT.smoothOfRelativeDimension s[Φ]
  let : Smooth (W ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let := hdimY
  let : Smooth (Y ↘ S) := hdimY.smooth
  let : (e.hom ≫ T.toBase).IsOver S := ⟨(Category.assoc _ _ _).trans he⟩
  let hΨ := (Φ.isRegular_mutationFan_iff b hv hp hOpp).mpr hΦ
  let : Nonempty (Ψ).cones := ((Φ.isComplete_mutationFan_iff b hv hp hOpp).mpr hc).nonempty_cones
  let : SmoothOfRelativeDimension 2 (X[Ψ] ↘ S) :=
    ((Ψ).finiteFanScheme_over K).symm ▸
      (rankTwo ▸ (Ψ).smoothOfRelativeDimension_finiteFanSchemeToSpec K hΨ)
  obtain ⟨hover, hpole⟩ := ρ.mutation_resolution_poleIdeal_iff K b hOpp c hT hΦ hc r
    (D.comap e.inv) hr
  let : r.IsOver S := hover
  let : (e.hom ≫ r).IsOver S := inferInstance
  refine ⟨‹_›, ?_⟩
  have hsource := comap_eq_mul_ramificationIdealSheaf_comp_iff_of_isIso K e.hom T.toBase 2
    (D := B[Φ,hc]) (Q := D)
  have htarget := comap_eq_mul_ramificationIdealSheaf_comp_iff_of_isIso K e.hom r 2
    (D := B[Ψ,(Φ.isComplete_mutationFan_iff b hv hp hOpp).mpr hc]) (Q := D)
  rw [IsIso.inv_eq_of_hom_inv_id e.hom_inv_id] at hsource htarget
  rw [hT.ramificationIdealSheafToBase_def K] at hpole
  exact hsource.trans (hpole.trans htarget.symm)

end TauCeti.Toric.Fan

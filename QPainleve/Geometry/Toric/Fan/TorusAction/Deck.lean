/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.TorusAction.Classification
public import QPainleve.Geometry.Toric.Fan.TorusAction.ContractedEvaluation

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Deck transformations of fixed-center toric evaluation

At finite charge index an automorphism fixing the rational X evaluation is a
descended quotient-character translation. Thus on a contracted nodal pair the
deck transformations are precisely the Picard-trivial automorphisms fixing
each boundary component and each branch. The comparison joins the
function-field translation criterion to the ordered lift and descent used in
[Gross, Hacking and Keel, Proposition 2.6](https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve.BlowupTower TauCeti
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData
open Scheme.RationalMap

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}
  (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)
  (c : Multiplicative (Fin n → ℤ) →* ℂˣ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "centers" => (fun j : Fin n ↦ c (ofAdd (Pi.single j 1)))
local notation "M" => internalBlowupTower b s centers
local notation "π" => toBase (WithBoundary.toTower (Sigma.snd M))
local notation "ι" => WithBoundary.boundaryι (Sigma.snd M)

variable {X Y : Scheme} [X.Over S] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ S)]
  {m : ℕ} {T : QPainleve.BlowupTower X m Y}
  (e : Y ≅ (internalBlowupTower b s (fun j ↦ c (ofAdd (Pi.single j 1)))).1)

local notation "p" => e.inv ≫ T.toBase
local notation "E" => contractedXEvaluation b s c hΦ p

/-- For finite-index charges, the automorphisms fixing the fixed-center X evaluation
are exactly the image of the quotient-character action. Equality of evaluations
itself forces an automorphism to be over the complex base. -/
theorem mem_range_toricPresentationCharacterHom_iff_comp_contractedXEvaluation_eq
    [QuasiCompact (X ↘ S)] [IsSeparated (X ↘ S)] (hT : IsClosedPointTower X T)
    (he : e.hom ≫ π ≫ Φ.algebraicRealizationStructureMap = T.toBase ≫ X ↘ S)
    (hindex : (rayChargeMap s).range.toAddSubgroup.index ≠ 0) (a : Aut X) :
    let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
    let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
    a ∈ (toricPresentationCharacterHom b s centers hΦ (X ↘ S) e hT hc).range ↔
      a.asIso.hom.toRationalMap.comp E = E := by
  intro _ _ _
  constructor
  · rintro ⟨z, rfl⟩
    exact toricPresentationCharacterHom_comp_contractedXEvaluation b s hΦ (X ↘ S) hT e hc z
  · intro ha
    have hp : (p) ≫ (X ↘ S) = π ≫ Φ.algebraicRealizationStructureMap := by
      rw [Category.assoc, ← he, Iso.inv_hom_id_assoc]
    have hbase := isOver_iff.mp (contractedXEvaluation_isOver b s c hΦ (p) (X ↘ S) hp)
    have hcomp : a.asIso.hom ≫ (X ↘ S) = X ↘ S := by
      apply Scheme.Hom.toRationalMap_injective
      simpa only [← comp_compHom, hbase, Scheme.RationalMap.comp_toRationalMap,
        Scheme.Hom.toRationalMap_compHom] using
        congrArg (fun F ↦ F.compHom (Spec.algebraMap ℂ (LaurentRing ℂ (Fin n)))) ha
    let : a.asIso.hom.IsOver S := ⟨hcomp⟩
    obtain ⟨_, ⟨g, hg, hcomm⟩, -⟩ :=
      existsUnique_torusTranslation_isLift_of_comp_contractedXEvaluation_eq
        b s c c hΦ (p) (p) a.asIso hindex hp hp ha
    have hmem := mem_internalBlowupPicardBoundaryAut_of_isLift_torusTranslation
      b s centers hΦ (g := Aut.of g) hg
    exact mem_range_toricPresentationCharacterHom_of_comp_eq
      b s centers hΦ (X ↘ S) e hT hc hmem hcomm

include hc in
/-- The Picard kernel fixing all components and branches of a nodal boundary is
exactly the group fixing its contracted X evaluation at finite charge index. -/
theorem mem_picardNodalBoundaryAut_iff_comp_contractedXEvaluation_eq
    [IsProper (X ↘ S)] {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
    (he : e.hom ≫ π ≫ Φ.algebraicRealizationStructureMap = T.toBase ≫ X ↘ S)
    (hB : (D.comap T.toBase).support = ((ι).ker.comap e.hom).support)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (hindex : (rayChargeMap s).range.toAddSubgroup.index ≠ 0) (a : Aut X) :
    let : IsModification T.toBase :=
      hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
    a ∈ D.picardNodalBoundaryAut hN ↔ a.asIso.hom.toRationalMap.comp E = E := by
  intro _
  let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  rw [← toricPresentationCharacterHom_range_eq_picardNodalBoundaryAut
    b s centers hΦ hc e he hB hD hN hT]
  exact mem_range_toricPresentationCharacterHom_iff_comp_contractedXEvaluation_eq
    b s c hΦ hc e hT.isClosedPointTower he hindex a

end TauCeti.Toric.Fan

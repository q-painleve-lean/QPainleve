/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Descent
public import QPainleve.Geometry.Toric.Fan.TorusAction.ContractedEvaluation

import QPainleve.Geometry.Toric.Fan.Boundary.Contraction

/-!
# Aligning centers on nodal contractions of ordered toric models

Agreement of the center characters on the charge kernel gives a translating lift
between the ordered models. When the same rays survive the two nodal contractions,
the lift identifies the original pairs, their marked Picard coordinates, and their
fixed-center rational X evaluations.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)
  (c d : Multiplicative (Fin n → ℤ) →* ℂˣ)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "center" a:arg => (fun j : Fin n ↦ a (ofAdd (Pi.single j 1)))
local notation "M" a:arg => internalBlowupTower b s (center a)
local notation "π" a:arg => toBase (WithBoundary.toTower (Sigma.snd (M a)))
local notation "strict[" a "]" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd (M a)))
local notation "prime[" a "]" => internalBlowupBoundaryPrimeEquiv hΦ b s (center a)
local notation "mark" a:arg => internalBlowupPicardMarking b s (center a) hΦ
local notation "base" => Φ.algebraicRealizationStructureMap

variable {X X' Y Y' : Scheme} [IsIntegral X] [IsIntegral X']
  {f : X ⟶ S} {g : X' ⟶ S} [SmoothOfRelativeDimension 2 f] [SmoothOfRelativeDimension 2 g]
  [QuasiCompact f] [QuasiCompact g]
  {D : X.IdealSheafData} {D' : X'.IdealSheafData} [IsReduced D.subscheme] [IsReduced D'.subscheme]
  {m m' : ℕ} {T : BlowupTower X m Y} {U : BlowupTower X' m' Y'}

local notation "p[" a "]" => (Iso.inv a ≫ toBase T)
local notation "q[" a "]" => (Iso.inv a ≫ toBase U)

/-- Ordered presentations with the same surviving rays and the same restricted center
character admit a center-aligning isomorphism of their contracted pairs. On the ordered
models the isomorphism lifts a torus translation. It intertwines the rational X
evaluations and identifies the full Picard coordinates obtained by pullback. -/
theorem exists_iso_of_eq_center_character
    (hT : IsNodalBoundaryTower D f (𝟙 X) T) (hU : IsNodalBoundaryTower D' g (𝟙 X') U)
    (e : Y ≅ (M c).1) (e' : Y' ≅ (M d).1)
    (hc : p[e] ≫ f = π c ≫ base) (hd : q[e'] ≫ g = π d ≫ base)
    (hD : (D.comap p[e]).support = strict[c].support)
    (hD' : (D'.comap q[e']).support = strict[d].support)
    (hkeep : ∀ ρ : Φ.Ray, p[e] (prime[c] ρ).val ∈ D.boundaryPrimes ↔
      q[e'] (prime[d] ρ).val ∈ D'.boundaryPrimes)
    (hcenters : ∀ x ∈ (rayChargeMap s).ker,
      (∏ j, (center c) j ^ x j) = ∏ j, (center d) j ^ x j) :
    let : IsModification T.toBase :=
      hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two f
    let : IsModification U.toBase :=
      hU.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two g
    ∃ (χ : Multiplicative (N →+ ℤ) →* ℂˣ) (t : (M c).1 ≅ (M d).1) (a : X ≅ X'),
      IsLift (Φ.torusTranslation χ) (M c).2.toTower (M d).2.toTower t ∧
      p[e] ≫ a.hom = t.hom ≫ q[e'] ∧ a.hom ≫ g = f ∧ D'.comap a.hom = D ∧
      a.hom.toRationalMap.comp (contractedXEvaluation b s d hΦ q[e']) =
        contractedXEvaluation b s c hΦ p[e] ∧
      ∀ L : LineBundleClass X',
        (mark c).symm (Additive.ofMul (LineBundleClass.pullback p[e]
          (LineBundleClass.pullback a.hom L))) =
        (mark d).symm (Additive.ofMul (LineBundleClass.pullback q[e'] L)) := by
  let : IsModification T.toBase :=
    hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two f
  let : IsModification U.toBase :=
    hU.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two g
  obtain ⟨χ, t, ht⟩ :=
    (exists_translation_lift_internalBlowupTower_iff b s (center c) (center d)).mpr hcenters
  have hover : p[e] ≫ f = t.hom ≫ q[e'] ≫ g := by
    rw [hc, hd, hom_comp_internalBlowupTower_structureMap_of_isLift_torusTranslation
      b s (center c) (center d) χ ht]
  obtain ⟨a, ⟨ha, haOver, haD⟩, -⟩ :=
    (existsUnique_iso_iff_eq_contractedBoundaryRays hΦ hΦ b b s s
      (center c) (center d) hT hU e e' (e.hom_inv_id_assoc _) (e'.hom_inv_id_assoc _)
      t hover hD hD' (Equiv.refl Φ.Ray)
      (apply_internalBlowupBoundaryPrimeEquiv_of_isLift_torusTranslation b s hΦ
        (center c) (center d) ht)).mpr hkeep
  exact ⟨χ, t, a, ht, ha, haOver, haD,
    comp_contractedXEvaluation_of_isLift_torusTranslation b s hΦ ht ha,
    pullback_marking_of_translation_descends b s (center c) (center d) hΦ ht ha⟩

end TauCeti.Toric.Fan

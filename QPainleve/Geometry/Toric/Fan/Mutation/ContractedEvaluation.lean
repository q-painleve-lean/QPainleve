/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Chart
public import QPainleve.Geometry.Toric.Fan.Mutation.Evaluation
public import QPainleve.Geometry.Toric.Fan.TorusAction.Comparison

import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational

/-!
# X mutation on contracted toric presentations

For a commuting contraction square resolving an elementary transformation, the
canonical fixed-center evaluation lands generically in the domain of the independent
X mutation. Composing there gives the canonical target evaluation pulled back by
the descended isomorphism. The equation also applies when the fixed-center image
is nondense.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module Multiplicative PointedCone
open QPainleve.BlowupTower QPainleve.Cluster TauCeti.AlgebraicGeometry TauCeti.LaurentRing
open Scheme.RationalMap

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) {n : ℕ}
  (s : Fin n → Φ.Ray) (k : Fin n)
  (χ : Multiplicative (Fin n → ℤ) →* ℂˣ)
  (hOpp : hull ℝ {i (-(s k).primitiveGenerator)} ∈ Φ.cones)
  (hΦ : Φ.IsRegular)

local notation "ρ" => s k
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "t" => Φ.mutationFanCenterRays b s k hOpp
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hOpp) hΦ
local notation "hΦ₀" => Nonempty.intro (Ray.toCone Φ ρ)
local notation "hΨ₀" => Nonempty.intro (Ray.toCone (Ψ) (t k))
local notation "center" a:arg => (fun j : Fin n ↦ a (ofAdd (Pi.single j 1)))
local notation "c" => (center χ) k
local notation "ε" => chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s)
local notation "χ′" => MonoidHom.comp χ (AddMonoidHom.toMultiplicative
  (AddEquiv.toAddMonoidHom (LinearEquiv.toAddEquiv (chargeMutationEquiv ε k))))
local notation "A" => internalBlowupTower (h₀ := hΦ₀) b s (center χ)
local notation "B" => internalBlowupTower (h₀ := hΨ₀) b (t) (center χ′)
local notation "πA" => toBase (WithBoundary.toTower (Sigma.snd A))
local notation "πB" => toBase (WithBoundary.toTower (Sigma.snd B))
local notation "I₀" => Ray.mutationSourceCenterIdeal b ρ c
local notation "I₁" => Ray.mutationTargetCenterIdeal b ρ hOpp c
local notation "G" => Ray.mutationBlowupIso b ρ hOpp c
local notation "incl" => Spec.algebraMap (LaurentRing ℂ (Fin n)) (XMutationChart ℂ k)

/-- The canonical evaluations of two contracted models intertwine X mutation when the
contraction square commutes with an isomorphism resolving the specified pivot.
The generic value of the source evaluation lies in the domain of the mutation. -/
theorem compOfDefined_contractedXEvaluation_mutate
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    {p : (A).1 ⟶ X} {q : (B).1 ⟶ Y} [IsModification p] [IsModification q]
    {e : (A).1 ≅ (B).1} {g : X ≅ Y} (f : (A).1 ⟶ (I₀).blowup)
    (hf : f ≫ (I₀).blowupToBase = πA)
    (he : e.hom ≫ πB = f ≫ (G).hom ≫ (I₁).blowupToBase)
    (hg : p ≫ g.hom = e.hom ≫ q)
    (E : SkewExchangeMatrix (Fin n)) (hE : ∀ j, E.matrix j k = ε j k) :
    let F := ((Generator.mutate k).toStep E).toPath.xRationalMap ℂ
    letI : Nonempty Φ.cones := hΦ₀
    letI : Nonempty (Ψ).cones := hΨ₀
    let a₀ := contractedXEvaluation b s χ hΦ p
    let a₁ := contractedXEvaluation b (t) χ′ (hΨ) q
    ∃ h : a₀.fromFunctionField (IsLocalRing.closedPoint X.functionField) ∈ F.domain,
      a₀.compOfDefined F h = g.hom.toRationalMap.comp a₁ := by
  intro F a₀ a₁
  let : Nonempty Φ.cones := hΦ₀
  let : Nonempty (Ψ).cones := hΨ₀
  have := isIntegral_internalBlowupTower b s (center χ) hΦ
  have := isIntegral_internalBlowupTower b (t) (center χ′) (hΨ)
  have := isModification_internalBlowupTower_toBase b s (center χ) hΦ
  have := isModification_internalBlowupTower_toBase b (t) (center χ′) (hΨ)
  have := Ray.isModification_mutationSourceBlowupToBase b ρ hOpp c
  have : IsDominant (f ≫ (I₀).blowupToBase) := hf ▸ inferInstanceAs (IsDominant πA)
  have : IsDominant f := IsModification.isDominant_of_comp f (I₀).blowupToBase
  obtain ⟨a, a', ha, ha', hm⟩ := Φ.exists_xEvaluation_of_mutation_contraction b s k χ hOpp p g f
  have h₀ : a.compHom incl = a₀ := by
    apply comp_left_injective p.toRationalMap
    dsimp only
    calc
      _ = ((πA).toRationalMap.comp (Φ.mutationChartEvaluation b s k χ)).compHom incl := by
        rw [comp_compHom]
        simpa only [hf] using congrArg (·.compHom incl) ha
      _ = _ := by
        rw [← comp_compHom, mutationChartEvaluation_compHom, comp_contractedXEvaluation]
  have h₁ : a' = a₁ := by
    apply comp_left_injective (p ≫ g.hom).toRationalMap
    dsimp only
    calc
      _ = (e.hom ≫ πB).toRationalMap.comp ((Ψ).xEvaluation b (t) χ′) := by
        simpa only [← he] using ha'
      _ = _ := by
        simpa only [← comp_assoc, comp_toRationalMap, Scheme.Hom.toRationalMap_compHom, ← hg]
          using (congrArg (e.hom.toRationalMap.comp ·)
            (comp_contractedXEvaluation b (t) χ′ (hΨ) q)).symm
  obtain ⟨h, hmix⟩ := Quiver.Path.compOfDefined_xRationalMap_mutate ℂ E k a
  have hcol : (fun j ↦ E.matrix j k) = fun j ↦ ε j k := funext hE
  rw [← h₀]
  exact ⟨h, by rw [hmix, hcol, ← hm, h₁]⟩

end TauCeti.Toric.Fan

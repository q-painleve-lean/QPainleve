/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Contraction
public import QPainleve.Geometry.Toric.Fan.Mutation.ContractedEvaluation
public import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Descent
public import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Ordered
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The marked elementary transformation on contracted toric pairs

An elementary transformation of the ordered toric presentations descends through the
specified nodal towers of nef square-zero pairs. The same descended isomorphism
has the integral mutation formula on the full Picard marking and intertwines
the canonical fixed-center evaluations with independent X mutation.

The elementary transformation is that of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, §3.1 and Theorem 5.6][GHK].

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module Multiplicative PointedCone
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry LineBundleClass
open QPainleve QPainleve.BlowupTower QPainleve.Cluster

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) {n : ℕ}
  (s : Fin (n + 1) → Φ.Ray) (k : Fin (n + 1))
  (χ : Multiplicative (Fin (n + 1) → ℤ) →* ℂˣ)
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
local notation "center" a:arg => (fun j : Fin (n + 1) ↦ a (ofAdd (Pi.single j 1)))
local notation "d" => center χ
local notation "c" => (d) k
local notation "ε" => chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s)
local notation "χ′" => MonoidHom.comp χ (AddMonoidHom.toMultiplicative
  (AddEquiv.toAddMonoidHom (LinearEquiv.toAddEquiv (chargeMutationEquiv ε k))))
local notation "d′" => center χ′
local notation "A" => internalBlowupTower (h₀ := hΦ₀) b s (d)
local notation "B" => internalBlowupTower (h₀ := hΨ₀) b (t) (d′)
local notation "πA" => toBase (WithBoundary.toTower (Sigma.snd A))
local notation "πB" => toBase (WithBoundary.toTower (Sigma.snd B))
local notation "ιA" => WithBoundary.boundaryι (Sigma.snd A)
local notation "ιB" => WithBoundary.boundaryι (Sigma.snd B)
local notation "μA" => internalBlowupPicardMarking (h₀ := hΦ₀) b s (d) hΦ
local notation "μB" => internalBlowupPicardMarking (h₀ := hΨ₀) b (t) (d′) (hΨ)
local notation "I" => mutationPicardEquiv b s k hOpp hΦ
local notation "u" => Ray.mutationBoundaryIso b ρ hOpp c hΦ

variable {X X' Y Y' : Scheme} [IsIntegral X] [IsIntegral X']
  [X.Over (Spec (.of ℂ))] [X'.Over (Spec (.of ℂ))]
  [X.IsProjectiveOver ℂ] [X'.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))]
  [SmoothOfRelativeDimension 2 (X' ↘ Spec (.of ℂ))]
  {D : X.IdealSheafData} {D' : X'.IdealSheafData} {m l : ℕ}
  {P : BlowupTower X m Y} {Q : BlowupTower X' l Y'}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "s₀" => (X ↘ S)
local notation "s₁" => (X' ↘ S)
local notation "classOf(" h ")" =>
  (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

/-- A mutation at a noncolliding pivot in an ordered toric presentation descends
to the original nef square-zero pairs. For the resulting pair isomorphism, the
full Picard pullback is the integral mutation in the ordered markings, and the
fixed-center X evaluations satisfy the independent X mutation equation on its
domain. The upper isomorphism restricts to the pivot boundary isomorphism.
Centers away from the pivot fiber can repeat. -/
theorem exists_iso_ordered_nodal_mutation
    (hsame : ∀ j, j ≠ k → (s j).primitiveGenerator = Ray.primitiveGenerator ρ → (d) j ≠ c)
    (hopp : ∀ j, j ≠ k → (s j).primitiveGenerator = -Ray.primitiveGenerator ρ → (d) j * c ≠ 1)
    (hP : IsNodalBoundaryTower D s₀ (𝟙 X) P)
    (hQ : IsNodalBoundaryTower D' s₁ (𝟙 X') Q)
    (a : Y ≅ (A).1) (a' : Y' ≅ (B).1)
    (ha : a.hom ≫ πA ≫ Φ.algebraicRealizationStructureMap = P.toBase ≫ s₀)
    (ha' : a'.hom ≫ πB ≫ (Ψ).algebraicRealizationStructureMap = Q.toBase ≫ s₁)
    (hb : ((ιA).ker.comap a.hom).support = (D.comap P.toBase).support)
    (hb' : ((ιB).ker.comap a'.hom).support = (D'.comap Q.toBase).support)
    (hD : D.IsEffectiveCartier) (hD' : D'.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s₀))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (D'.subschemeι ≫ s₁))
    (hconn : _root_.IsConnected (D.support : Set X))
    (hnef : IsNef ℂ s₀ classOf(hD)) (hnef' : IsNef ℂ s₁ classOf(hD'))
    (hsq : Chow.classIntersectionNumber ℂ X classOf(hD) classOf(hD) = 0)
    (hsq' : Chow.classIntersectionNumber ℂ X' classOf(hD') classOf(hD') = 0)
    (E : SkewExchangeMatrix (Fin (n + 1))) (hE : ∀ j, E.matrix j k = ε j k) :
    let : IsNoetherian X := isNoetherian_of_finiteType s₀
    let : IsNoetherian X' := isNoetherian_of_finiteType s₁
    let : IsModification P.toBase :=
      hP.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two s₀
    let : IsModification Q.toBase :=
      hQ.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two s₁
    let p := a.inv ≫ P.toBase
    let q := a'.inv ≫ Q.toBase
    letI : IsModification p := inferInstanceAs (IsModification (a.inv ≫ P.toBase))
    letI : IsModification q := inferInstanceAs (IsModification (a'.inv ≫ Q.toBase))
    let F := ((Generator.mutate k).toStep E).toPath.xRationalMap ℂ
    letI : Nonempty Φ.cones := hΦ₀
    letI : Nonempty (Ψ).cones := hΨ₀
    let a₀ := contractedXEvaluation b s χ hΦ p
    let a₁ := contractedXEvaluation b (t) χ′ (hΨ) q
    ∃ (e : (A).1 ≅ (B).1) (g : X ≅ X'),
      (ιA) ≫ e.hom = (u).hom ≫ (ιB) ∧
      p ≫ g.hom = e.hom ≫ q ∧ g.hom ≫ s₁ = s₀ ∧ D'.comap g.hom = D ∧
      (∀ L : LineBundleClass X',
        (μA).symm (Additive.ofMul (pullback p (pullback g.hom L))) =
          I ((μB).symm (Additive.ofMul (pullback q L)))) ∧
      ∃ h : a₀.fromFunctionField (IsLocalRing.closedPoint X.functionField) ∈ F.domain,
        a₀.compOfDefined F h = g.hom.toRationalMap.comp a₁ := by
  intro _ _ _ _ p q F a₀ a₁
  let : IsModification p := inferInstanceAs (IsModification (a.inv ≫ P.toBase))
  let : IsModification q := inferInstanceAs (IsModification (a'.inv ≫ Q.toBase))
  obtain ⟨e, f, hf, he, hover, hmark, -⟩ :=
    exists_iso_ordered_mutation_picard_marking b hΦ s χ k hOpp hsame hopp
  have hbdy : (ιA) ≫ e.hom = (u).hom ≫ (ιB) :=
    boundaryι_comp_of_ordered_mutation b ρ hOpp c s (d) (t) (d′) hΦ hf he
  have hstrict : (ιB).ker.comap e.hom = (ιA).ker := by
    rw [← (ιA).comap_ker_comp_of_isClosedImmersion e.hom, hbdy, Scheme.Hom.ker_comp_of_isIso]
  let e' := a ≪≫ e ≪≫ a'.symm
  have hstructure : P.toBase ≫ s₀ = e'.hom ≫ Q.toBase ≫ s₁ := by
    simp only [e', Iso.trans_hom, Iso.symm_hom, Category.assoc, ← ha', Iso.inv_hom_id_assoc,
      hover, ha]
  have hsupport : (D.comap P.toBase).support = ((D'.comap Q.toBase).comap e'.hom).support := by
    rw [support_comap (D'.comap Q.toBase), ← hb', ← support_comap, ← comap_comp, ← hb]
    simp only [e', Iso.trans_hom, Iso.symm_hom, Iso.inv_hom_id,
      Category.assoc, Category.comp_id, comap_comp, hstrict]
  obtain ⟨g, ⟨hg, hgOver, hpair⟩, -⟩ := hP.existsUnique_iso_of_nef_square_zero_boundary
    ℂ hQ e' hstructure hD hD' hnodal hnodal' hconn hsupport hnef hnef' hsq hsq'
  have hsquare : p ≫ g.hom = e.hom ≫ q := by
    simpa only [p, q, e', Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
      using congrArg (a.inv ≫ ·) hg
  refine ⟨e, g, hbdy, hsquare, hgOver, hpair, ?_, ?_⟩
  · apply pullback_nodal_mutation_picard_marking b s k hOpp hΦ (d) (d′) hsquare.symm
    simpa only [internalBlowupPicardMarking_apply] using hmark
  · exact compOfDefined_contractedXEvaluation_mutate b s k χ hOpp hΦ f hf he hsquare E hE

end TauCeti.Toric.Fan

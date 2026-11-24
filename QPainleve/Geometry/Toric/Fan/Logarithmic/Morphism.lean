/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Logarithmic.Morphism
public import QPainleve.Geometry.Toric.Fan.Boundary.Node
public import QPainleve.Geometry.Toric.Fan.Boundary.Prime
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Basic
public import QPainleve.Geometry.Toric.Fan.Smooth

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus
import QPainleve.AlgebraicGeometry.OrderOfVanishing.IsoLocus
import QPainleve.AlgebraicGeometry.Scheme.FunctionField
import QPainleve.Geometry.Toric.Fan.Separated
import QPainleve.Geometry.Toric.Fan.Subdivision.FunctionField
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Factorization of logarithmic morphisms to toric surfaces

A birational morphism to a complete regular toric surface that pulls a logarithmic top form
back with the prescribed pole divisor factors through a regular toric subdivision followed,
in blowup order, by internal blowups. The factorization identifies the pole ideal itself
with the strict boundary and retains the ordered center schemes on any specified point-blowup
factorization. The rays of the subdivision are characterized by the orders of the pulled-back
characters on the original source boundary. The factorization is the regular-morphism
comparison used in Lutz's appendix to Hacking and Keating,
[*Homological mirror symmetry for log Calabi–Yau surfaces*][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} {X : Scheme}
  (b : Module.Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)

local notation "Y" => Φ.algebraicRealization
local notation "D" => Φ.boundaryIdeal hc.nonempty_cones
local notation "s" => Φ.algebraicRealizationStructureMap

/-- Normalize any specified point-blowup factorization of a morphism whose logarithmic
pole ideal is `P`. The subdivision and the ordered internal blowups realize the original
morphism. Each center of the classified tower retains its scheme and its map to the
original toric surface. -/
theorem exists_toric_internal_factorization_of_poleIdeal
    {Z : Scheme} {n : ℕ} {T : BlowupTower Y n Z}
    (hT : IsClosedPointTower Y T) {f : X ⟶ Y} {P : X.IdealSheafData}
    (e : X ≅ Z) (he : e.hom ≫ T.toBase = f) :
    let _ : Nonempty Φ.cones := hc.nonempty_cones
    let _ : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of ℂ)) :=
      ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    (D).comap T.toBase ≤ hT.ramificationIdealSheafToBase ℂ →
    (((D).comap T.toBase).colon (hT.ramificationIdealSheafToBase ℂ)).comap e.hom = P →
    ∃ (m : ℕ) (c : Fin m → Over Y),
      IsLogarithmicBoundaryTower D s T
        (((D).comap T.toBase).colon (hT.ramificationIdealSheafToBase ℂ)) c ∧
      ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (H : Ψ.IsSubdivision Φ),
        let := H.nonempty_cones_of_nonempty hc.nonempty_cones
        ∃ (ρ : Fin m → Ψ.Ray) (u : Fin m → ℂˣ),
          let A := Ψ.internalBlowupTower b ρ u
          ∃ (g : A.1 ≅ X) (a : ∀ j, (c j).left ⟶ (Ψ.boundaryIdeal inferInstance).subscheme),
            g.hom ≫ f = A.2.toTower.toBase ≫ H.toFanHom.algebraicMap ∧
            P.comap g.hom = A.2.boundaryι.ker ∧
            (∀ j, IsClosedImmersion (a j)) ∧
            ∀ j, (a j).ker = ((ρ j).internalCenter b (u j)).val ∧
              a j ≫ (Ψ.boundaryIdeal inferInstance).subschemeι ≫ H.toFanHom.algebraicMap =
                (c j).hom := by
  intro _ _ hle hP
  have hdim : Module.finrank ℤ N = 2 := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  obtain ⟨m, c, ht, -⟩ := hT.exists_orderedFactorization_of_totalTransform_le_ramification
    (Φ.isEffectiveCartier_boundaryIdeal hΦ hc hdim) hle
    (Φ.atWorstNodalOfRelativeDimensionOne_boundary hΦ hc hdim)
  obtain ⟨Ψ, hΨ, H, ρ, u, g, a, hbase, hboundary, ha, hcenter⟩ :=
    Φ.exists_toric_internal_factorization b hΦ hc ht
  refine ⟨m, c, ht, Ψ, hΨ, H, ρ, u, g ≪≫ e.symm, a, ?_, ?_, ha, hcenter⟩
  · simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← he, Iso.inv_hom_id_assoc]
      using hbase
  · rw [← hP, Iso.trans_hom, ← comap_comp, Category.assoc, Iso.symm_hom, Iso.inv_hom_id,
      Category.comp_id]
    exact hboundary

/-- Under an ordered toric factorization of a specified morphism, every boundary prime
corresponds to a ray of the subdivided fan. Its orders on all pulled-back characters
are the evaluations on that ray's primitive generator, which characterize the correspondence.
The closure of each prime is the image of the embedded ray component. -/
theorem exists_equiv_boundaryPrimes_of_toric_internal_factorization
    [Nonempty Φ.cones] {Ψ : Fan i} [Nonempty Ψ.cones]
    (hΨ : Ψ.IsRegular) (H : Ψ.IsSubdivision Φ)
    {m : ℕ} (ρ : Fin m → Ψ.Ray) (u : Fin m → ℂˣ)
    [IsIntegral X] [IsLocallyNoetherian X] {f : X ⟶ Y} [IsDominant f] {P : X.IdealSheafData}
    (e : (Ψ.internalBlowupTower b ρ u).1 ≅ X)
    (he : e.hom ≫ f = (Ψ.internalBlowupTower b ρ u).2.toTower.toBase ≫ H.toFanHom.algebraicMap)
    (hP : P.comap e.hom = (Ψ.internalBlowupTower b ρ u).2.boundaryι.ker) :
    ∃ R : Ψ.Ray ≃ P.boundaryPrimes,
      (∀ (r : Ψ.Ray) (p : P.boundaryPrimes),
        R r = p ↔ ∀ a : N →+ ℤ,
          X.ord (f.functionFieldMap (Φ.character (ofAdd a))) p.val = a r.primitiveGenerator) ∧
      ∀ r, Set.range (r.boundaryComponentι hΨ ≫ (Ψ.internalBlowupTower b ρ u).2.boundaryι ≫
        e.hom) = closure {((R r).val : X)} := by
  let A := Ψ.internalBlowupTower b ρ u
  let π := A.2.toTower.toBase
  have : IsIntegral A.1 := isIntegral_internalBlowupTower b ρ u hΨ
  have : IsNoetherian A.1 := A.2.toTower.isNoetherian
  have : IsModification π := isModification_internalBlowupTower_toBase b ρ u hΨ
  let R := internalBlowupBoundaryPrimeEquiv hΨ b ρ u
  let E := (Set.equivOfEq (congrArg boundaryPrimes hP.symm)).trans
    (P.boundaryPrimesEquivOfIso e)
  let rays := R.trans E
  have hrays (r : Ψ.Ray) : (rays r).val = e.hom (R r).val := by
    simp only [rays, E, Equiv.trans_apply, boundaryPrimesEquivOfIso_apply_val, Set.equivOfEq_apply]
  have horder (r : Ψ.Ray) (a : N →+ ℤ) :
      X.ord (f.functionFieldMap (Φ.character (ofAdd a))) (rays r).val =
        a r.primitiveGenerator := by
    let x := (R r).val
    have hπ : π x = (Ψ.rayBoundaryPoint hΨ r).val :=
      toBase_internalBlowupBoundaryPrimeEquiv hΨ b ρ u r
    have hIso : π x ∈ π.isoLocus :=
      π.mem_isoLocus_of_coheight_eq_one (hπ.symm ▸ (Ψ.rayBoundaryPoint hΨ r).property)
    rw [hrays, ← TauCeti.AlgebraicGeometry.Scheme.ord_functionFieldMap e.hom]
    have hfield := (Scheme.Hom.functionFieldMap_comp e.hom f).symm.trans
      ((Scheme.Hom.functionFieldMap_congr he).trans (Scheme.Hom.functionFieldMap_comp π _))
    rw [← CommRingCat.comp_apply, hfield, CommRingCat.comp_apply,
      π.ord_functionFieldMap_of_mem_isoLocus hIso, hπ,
      H.toFanHom.functionFieldMap_algebraicMap_character,
      H.toFanHom_latticeMap, AddMonoidHom.comp_id, Ψ.ord_rayBoundaryPoint_character hΨ]
  refine ⟨rays, fun r p ↦ ⟨fun h a ↦ h ▸ horder r a, ?_⟩, ?_⟩
  · obtain ⟨q, rfl⟩ := rays.surjective p
    intro h
    apply congrArg rays
    apply Ray.primitiveGenerator_injective
    apply b.repr.injective
    ext j
    exact (h (b.coord j).toAddMonoidHom).symm.trans (horder q (b.coord j).toAddMonoidHom)
  · intro r
    rw [← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      range_rayComponent_internalBlowupBoundaryPrimeEquiv hΨ b ρ u,
      ← e.hom.isClosedEmbedding.closure_image_eq, Set.image_singleton, hrays]

variable [X.Over (Spec (.of ℂ))] [IsIntegral X] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))]
  {f : X ⟶ Φ.algebraicRealization} [f.IsOver (Spec (.of ℂ))]
  {P : X.IdealSheafData}

include hΦ in
/-- A specified birational morphism with a pole ideal equal to the toric boundary
pullback divided by ramification admits an ordered internal model over a regular
subdivision. The isomorphism recovers the given morphism and the actual pole ideal. -/
theorem exists_toric_internal_factorization_of_boundary_comap_eq
    (hf : Scheme.BirationalOver f (𝟙 Y)) :
    letI := SmoothOfRelativeDimension.smooth 2 (X ↘ Spec (.of ℂ))
    (D).comap f = P * ramificationIdealSheaf ℂ f →
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (H : Ψ.IsSubdivision Φ),
      letI := H.nonempty_cones_of_nonempty hc.nonempty_cones
      ∃ (m : ℕ) (ρ : Fin m → Ψ.Ray) (u : Fin m → ℂˣ),
        let A := Ψ.internalBlowupTower b ρ u
        ∃ e : A.1 ≅ X,
          e.hom ≫ f = A.2.toTower.toBase ≫ H.toFanHom.algebraicMap ∧
          P.comap e.hom = A.2.boundaryι.ker := by
  intro hpole
  let : Nonempty Φ.cones := hc.nonempty_cones
  have hdim : Module.finrank ℤ N = 2 :=
    (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of ℂ)) :=
    hdim ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : Smooth (Y ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 2 _
  let : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ Spec (.of ℂ))
  let : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 2 _
  obtain ⟨_, _, _, e, hT, he⟩ := f.exists_isClosedPointTower_factorization (k := ℂ) hf
  have hRam : (ramificationIdealSheaf ℂ f).IsEffectiveCartier :=
    hT.comap_ramificationIdealSheafToBase ℂ e he ▸
      (hT.isEffectiveCartier_ramificationIdealSheafToBase ℂ).comap e.hom
  obtain ⟨hle, hP⟩ := (hT.comap_eq_mul_ramificationIdealSheaf_iff hRam e he).mp hpole
  obtain ⟨m, c, _, Ψ, hΨ, H, ρ, u, g, _, hbase, hboundary, _, _⟩ :=
    Φ.exists_toric_internal_factorization_of_poleIdeal b hΦ hc hT e he hle hP
  exact ⟨Ψ, hΨ, H, m, ρ, u, g, hbase, hboundary⟩

/-- A specified birational morphism from a smooth integral projective surface to a
complete regular toric surface factors through a regular subdivision and an ordered internal
blowup model if the pulled-back logarithmic top form has divisor `-P`. The model is
isomorphic to the source over the target, and its strict boundary is the pullback of
the actual ideal `P`. The ordered centers may include repeated or infinitely near centers. -/
theorem exists_toric_internal_factorization_of_pullbackTopFormDivisor
    (hf : Scheme.BirationalOver f (𝟙 Y)) (hP : P.IsEffectiveCartier) :
    let _ : Nonempty Φ.cones := hc.nonempty_cones
    let _ : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of ℂ)) :=
      ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let hD := Φ.isEffectiveCartier_boundaryIdeal hΦ hc
      ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2))
    ∀ (ω : hD.toInvertibleSheaf ≅ canonicalBundle ℂ Y 2)
      (hTotal : ((D).comap f).IsEffectiveCartier)
      (hRam : letI := SmoothOfRelativeDimension.smooth 2 (X ↘ Spec (.of ℂ))
        (ramificationIdealSheaf ℂ f).IsEffectiveCartier),
      pullbackTopFormDivisor ℂ f 2 hD ω hTotal hRam = -hP.toCartierDivisor →
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (H : Ψ.IsSubdivision Φ),
      let := H.nonempty_cones_of_nonempty hc.nonempty_cones
      ∃ (m : ℕ) (ρ : Fin m → Ψ.Ray) (u : Fin m → ℂˣ),
        let A := Ψ.internalBlowupTower b ρ u
        ∃ e : A.1 ≅ X,
          e.hom ≫ f = A.2.toTower.toBase ≫ H.toFanHom.algebraicMap ∧
          P.comap e.hom = A.2.boundaryι.ker := by
  intro _ _ hD ω hTotal hRam hdiv
  exact exists_toric_internal_factorization_of_boundary_comap_eq b hΦ hc hf
    ((QPainleve.pullbackTopFormDivisor_eq_neg_iff ℂ f 2 hD ω hTotal hP hRam).mp hdiv)

end TauCeti.Toric.Fan

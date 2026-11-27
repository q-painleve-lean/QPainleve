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
public import QPainleve.Geometry.Toric.Fan.Subdivision

import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus
import QPainleve.AlgebraicGeometry.OrderOfVanishing.IsoLocus
import QPainleve.AlgebraicGeometry.Scheme.FunctionField
import QPainleve.Geometry.Toric.Fan.Boundary.Character
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

universe u

variable (k : Type u) [Field k] {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} {X : Scheme}
  (b : Module.Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)

local notation "Y" => Φ.finiteFanScheme k
local notation "D" => Φ.toricBoundaryIdeal k hc.nonempty_cones
local notation "s" => Φ.finiteFanSchemeToSpec k

variable [IsAlgClosed k] in
/-- Normalize any specified point-blowup factorization of a morphism whose logarithmic
pole ideal is `P`. The subdivision and the ordered internal blowups realize the original
morphism. Each center of the classified tower retains its scheme and its map to the
original toric surface. -/
theorem exists_toric_internal_factorization_of_poleIdeal
    {Z : Scheme} {n : ℕ} {T : BlowupTower Y n Z}
    (hT : IsClosedPointTower Y T) {f : X ⟶ Y} {P : X.IdealSheafData}
    (e : X ≅ Z) (he : e.hom ≫ T.toBase = f) :
    let _ : Nonempty Φ.cones := hc.nonempty_cones
    let _ : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
      (Φ.finiteFanScheme_over k).symm ▸
        (((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)) ▸
          Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ)
    (D).comap T.toBase ≤ hT.ramificationIdealSheafToBase k →
    (((D).comap T.toBase).colon (hT.ramificationIdealSheafToBase k)).comap e.hom = P →
    ∃ (m : ℕ) (c : Fin m → Over Y),
      IsLogarithmicBoundaryTower D s T
        (((D).comap T.toBase).colon (hT.ramificationIdealSheafToBase k)) c ∧
      ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (H : Ψ.IsSubdivision Φ),
        let := H.nonempty_cones_of_nonempty hc.nonempty_cones
        ∃ (ρ : Fin m → Ψ.Ray) (u : Fin m → kˣ),
          let A := Ψ.internalBlowupTower k b ρ u
          ∃ (g : A.1 ≅ X)
          (a : ∀ j, (c j).left ⟶ (Ψ.toricBoundaryIdeal k inferInstance).subscheme),
            g.hom ≫ f = A.2.toTower.toBase ≫ H.toFanHom.finiteFanSchemeHom k ∧
            P.comap g.hom = A.2.boundaryι.ker ∧
            (∀ j, IsClosedImmersion (a j)) ∧
            ∀ j, (a j).ker = ((ρ j).internalCenter k b (u j)).val ∧
              a j ≫ (Ψ.toricBoundaryIdeal k inferInstance).subschemeι ≫
                H.toFanHom.finiteFanSchemeHom k = (c j).hom := by
  intro _ _ hle hP
  have hdim : Module.finrank ℤ N = 2 := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  obtain ⟨m, c, ht, -⟩ := hT.exists_orderedFactorization_of_totalTransform_le_ramification
    (Φ.isEffectiveCartier_boundaryIdeal k hΦ hc hdim) hle
    (Φ.atWorstNodalOfRelativeDimensionOne_boundary k hΦ hc hdim)
  obtain ⟨Ψ, hΨ, H, ρ, u, g, a, hbase, hboundary, ha, hcenter⟩ :=
    Φ.exists_toric_internal_factorization k b hΦ hc ht
  refine ⟨m, c, ht, Ψ, hΨ, H, ρ, u, g ≪≫ e.symm, a, ?_, ?_, ha, hcenter⟩
  · simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← he, Iso.inv_hom_id_assoc]
      using hbase
  · rw [← hP, Iso.trans_hom, ← comap_comp, Category.assoc, Iso.symm_hom, Iso.inv_hom_id,
      Category.comp_id]
    exact hboundary

section Valuation

variable [PerfectField k]

/-- At a transported boundary prime, the order of a character pulled back along the
specified morphism is its evaluation on the corresponding primitive ray generator. -/
theorem ord_internalBlowupBoundaryPrimeEquivOfIso_character
    [Nonempty Φ.cones] {Ψ : Fan i} [Nonempty Ψ.cones]
    (hΨ : Ψ.IsRegular) (H : Ψ.IsSubdivision Φ)
    {m : ℕ} (ρ : Fin m → Ψ.Ray) (u : Fin m → kˣ)
    [IsIntegral X] [IsLocallyNoetherian X] {f : X ⟶ Y} [IsDominant f] {P : X.IdealSheafData}
    (e : (Ψ.internalBlowupTower k b ρ u).1 ≅ X)
    (he : e.hom ≫ f =
      (Ψ.internalBlowupTower k b ρ u).2.toTower.toBase ≫ H.toFanHom.finiteFanSchemeHom k)
    (hs : (P.comap e.hom).support = (Ψ.internalBlowupTower k b ρ u).2.boundaryι.ker.support)
    (r : Ψ.Ray) (a : N →+ ℤ) :
    X.ord (f.functionFieldMap (Φ.functionFieldCharacter k (ofAdd a)))
        (internalBlowupBoundaryPrimeEquivOfIso k hΨ b ρ u e hs r).val =
      a r.primitiveGenerator := by
  let A := Ψ.internalBlowupTower k b ρ u
  let π := A.2.toTower.toBase
  have : IsIntegral A.1 := isIntegral_internalBlowupTower k b ρ u hΨ
  have : IsNoetherian A.1 := A.2.toTower.isNoetherian
  have : IsModification π := isModification_internalBlowupTower_toBase k b ρ u hΨ
  let := Ψ.isNormalScheme_finiteFanScheme (R := k) hΨ
  let x := (internalBlowupBoundaryPrimeEquiv k hΨ b ρ u r).val
  have hπ : π x = (Ψ.rayBoundaryChartPoint (R := k) hΨ r).val :=
    toBase_internalBlowupBoundaryPrimeEquiv k hΨ b ρ u r
  have hIso : π x ∈ π.isoLocus :=
    π.mem_isoLocus_of_coheight_eq_one (hπ.symm ▸ (Ψ.rayBoundaryChartPoint (R := k) hΨ r).property)
  rw [internalBlowupBoundaryPrimeEquivOfIso_apply_val,
    ← TauCeti.AlgebraicGeometry.Scheme.ord_functionFieldMap e.hom]
  have hfield := (Scheme.Hom.functionFieldMap_comp e.hom f).symm.trans
    ((Scheme.Hom.functionFieldMap_congr he).trans (Scheme.Hom.functionFieldMap_comp π _))
  rw [← CommRingCat.comp_apply, hfield, CommRingCat.comp_apply,
    π.ord_functionFieldMap_of_mem_isoLocus hIso, hπ,
    H.toFanHom.functionFieldMap_finiteFanSchemeHom_character k,
    H.toFanHom_latticeMap, AddMonoidHom.comp_id, Ψ.ord_rayBoundaryChartPoint_character k hΨ]

/-- The character orders at a boundary prime determine its ray in the specified
ordered toric factorization. -/
theorem internalBlowupBoundaryPrimeEquivOfIso_eq_iff_forall_ord_character
    [Nonempty Φ.cones] {Ψ : Fan i} [Nonempty Ψ.cones]
    (hΨ : Ψ.IsRegular) (H : Ψ.IsSubdivision Φ)
    {m : ℕ} (ρ : Fin m → Ψ.Ray) (u : Fin m → kˣ)
    [IsIntegral X] [IsLocallyNoetherian X] {f : X ⟶ Y} [IsDominant f] {P : X.IdealSheafData}
    (e : (Ψ.internalBlowupTower k b ρ u).1 ≅ X)
    (he : e.hom ≫ f =
      (Ψ.internalBlowupTower k b ρ u).2.toTower.toBase ≫ H.toFanHom.finiteFanSchemeHom k)
    (hs : (P.comap e.hom).support = (Ψ.internalBlowupTower k b ρ u).2.boundaryι.ker.support)
    (r : Ψ.Ray) (p : P.boundaryPrimes) :
    internalBlowupBoundaryPrimeEquivOfIso k hΨ b ρ u e hs r = p ↔
      ∀ a : N →+ ℤ,
        X.ord (f.functionFieldMap (Φ.functionFieldCharacter k (ofAdd a))) p.val =
          a r.primitiveGenerator := by
  let R := internalBlowupBoundaryPrimeEquivOfIso k hΨ b ρ u e hs
  obtain ⟨q, rfl⟩ := R.surjective p
  simp only [ord_internalBlowupBoundaryPrimeEquivOfIso_character k b hΨ H ρ u e he hs,
    R, Equiv.apply_eq_iff_eq]
  refine ⟨fun h a ↦ congrArg (fun x : Ψ.Ray ↦ a x.primitiveGenerator) h.symm, fun h ↦ ?_⟩
  apply Ray.primitiveGenerator_injective
  apply b.repr.injective
  ext j
  exact (h (b.coord j).toAddMonoidHom).symm

end Valuation

variable [IsAlgClosed k] [X.Over (Spec (.of k))] [IsIntegral X] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {f : X ⟶ Φ.finiteFanScheme k} [f.IsOver (Spec (.of k))]
  {P : X.IdealSheafData}

include hΦ in
/-- A specified birational morphism with a pole ideal equal to the toric boundary
pullback divided by ramification admits an ordered internal model over a regular
subdivision. The isomorphism recovers the given morphism and the actual pole ideal. -/
theorem exists_toric_internal_factorization_of_boundary_comap_eq
    (hf : Scheme.BirationalOver f (𝟙 Y)) :
    letI := SmoothOfRelativeDimension.smooth 2 (X ↘ Spec (.of k))
    (D).comap f = P * ramificationIdealSheaf k f →
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (H : Ψ.IsSubdivision Φ),
      letI := H.nonempty_cones_of_nonempty hc.nonempty_cones
      ∃ (m : ℕ) (ρ : Fin m → Ψ.Ray) (u : Fin m → kˣ),
        let A := Ψ.internalBlowupTower k b ρ u
        ∃ e : A.1 ≅ X,
          e.hom ≫ f = A.2.toTower.toBase ≫ H.toFanHom.finiteFanSchemeHom k ∧
          P.comap e.hom = A.2.boundaryι.ker := by
  intro hpole
  let : Nonempty Φ.cones := hc.nonempty_cones
  have hdim : Module.finrank ℤ N = 2 :=
    (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
    (Φ.finiteFanScheme_over k).symm ▸
      (hdim ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ)
  let : Smooth (Y ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  let : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ Spec (.of k))
  have : QuasiCompact (Y ↘ Spec (.of k)) := by
    rw [Φ.finiteFanScheme_over k]
    infer_instance
  have : IsSeparated (Y ↘ Spec (.of k)) := by
    rw [Φ.finiteFanScheme_over k]
    infer_instance
  let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  obtain ⟨_, _, _, e, hT, he⟩ := f.exists_isClosedPointTower_factorization (k := k) hf
  have hRam : (ramificationIdealSheaf k f).IsEffectiveCartier :=
    hT.comap_ramificationIdealSheafToBase k e he ▸
      (hT.isEffectiveCartier_ramificationIdealSheafToBase k).comap e.hom
  obtain ⟨hle, hP⟩ := (hT.comap_eq_mul_ramificationIdealSheaf_iff hRam e he).mp hpole
  obtain ⟨m, c, _, Ψ, hΨ, H, ρ, u, g, _, hbase, hboundary, _, _⟩ :=
    Φ.exists_toric_internal_factorization_of_poleIdeal k b hΦ hc hT e he hle hP
  exact ⟨Ψ, hΨ, H, m, ρ, u, g, hbase, hboundary⟩

/-- A specified birational morphism from a smooth integral projective surface to a
complete regular toric surface factors through a regular subdivision and an ordered internal
blowup model if the pulled-back logarithmic top form has divisor `-P`. The model is
isomorphic to the source over the target, and its strict boundary is the pullback of
the actual ideal `P`. The ordered centers may include repeated or infinitely near centers. -/
theorem exists_toric_internal_factorization_of_pullbackTopFormDivisor
    (hf : Scheme.BirationalOver f (𝟙 Y)) (hP : P.IsEffectiveCartier) :
    let _ : Nonempty Φ.cones := hc.nonempty_cones
    let _ : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
      (Φ.finiteFanScheme_over k).symm ▸
        (((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)) ▸
          Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ)
    let hD := Φ.isEffectiveCartier_boundaryIdeal k hΦ hc
      ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2))
    ∀ (ω : hD.toInvertibleSheaf ≅ canonicalBundle k Y 2)
      (hTotal : ((D).comap f).IsEffectiveCartier)
      (hRam : letI := SmoothOfRelativeDimension.smooth 2 (X ↘ Spec (.of k))
        (ramificationIdealSheaf k f).IsEffectiveCartier),
      pullbackTopFormDivisor k f 2 hD ω hTotal hRam = -hP.toCartierDivisor →
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (H : Ψ.IsSubdivision Φ),
      let := H.nonempty_cones_of_nonempty hc.nonempty_cones
      ∃ (m : ℕ) (ρ : Fin m → Ψ.Ray) (u : Fin m → kˣ),
        let A := Ψ.internalBlowupTower k b ρ u
        ∃ e : A.1 ≅ X,
          e.hom ≫ f = A.2.toTower.toBase ≫ H.toFanHom.finiteFanSchemeHom k ∧
          P.comap e.hom = A.2.boundaryι.ker := by
  intro _ _ hD ω hTotal hRam hdiv
  exact exists_toric_internal_factorization_of_boundary_comap_eq k b hΦ hc hf
    ((QPainleve.pullbackTopFormDivisor_eq_neg_iff k f 2 hD ω hTotal hP hRam).mp hdiv)

end TauCeti.Toric.Fan

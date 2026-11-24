/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Transport
public import QPainleve.Geometry.Toric.Fan.Equiv
public import QPainleve.Geometry.Toric.Fan.Picard.Endpoint
public import QPainleve.Geometry.Toric.Fan.Subdivision.MatchingModels

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.Geometry.Toric.Fan.CommonRefinement
import QPainleve.Geometry.Toric.Fan.Picard.Reindex
import QPainleve.Geometry.Toric.Fan.Subdivision

/-!
# Comparison of toric endpoints across lattice equivalences

An integral equivalence that matches the labeled charges and preserves the determinant
pairing allows the endpoint models to be compared in a common lattice. The ordered
binomial centers are transported along the fan equivalence and reindexed before taking a
common nodal refinement. Square-zero boundary descent then identifies the original pairs.
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open QPainleve.Cluster Multiplicative TopologicalSpace TauCeti.LaurentRing
open Scheme.IdealSheafData LineBundleClass

namespace TauCeti.Toric.Fan

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones] {n : ℕ}

local notation "centers(" c ")" => (fun j : Fin n ↦ c (ofAdd (Pi.single j 1)))

section SquareZero

variable {X X' Y Y' : Scheme} [IsIntegral X] [IsIntegral X']
  [X.Over (Spec (.of ℂ))] [X'.Over (Spec (.of ℂ))]
  [X.IsProjectiveOver ℂ] [X'.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))]
  [SmoothOfRelativeDimension 2 (X' ↘ Spec (.of ℂ))]
  {D : X.IdealSheafData} {E : X'.IdealSheafData} {p q : ℕ}
  {P : BlowupTower X p Y} {Q : BlowupTower X' q Y'}

local notation "s" => (X ↘ Spec (CommRingCat.of ℂ))
local notation "t" => (X' ↘ Spec (CommRingCat.of ℂ))
local notation "renameX(" σ ")" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (rename (R := ℂ) (Equiv.toFun σ))))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

/-- Identify two nef square-zero nodal pairs when an oriented integral equivalence matches
the charges of their regular toric models and the two center families agree after
relabeling. The isomorphism intertwines the fixed-center X evaluations by that
relabeling. If the relabeling preserves the order of coincident centers, the
Picard pullback is characterized in the coordinates of the specified common subdivision. -/
theorem exists_iso_of_matching_toric_models_of_latticeEquiv
    (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (ρ : Fin n → Φ.Ray) (τ : Fin n → Ψ.Ray) (c d : Multiplicative (Fin n → ℤ) →* ℂˣ)
    (σ : Equiv.Perm (Fin n)) (hc : centers(d) ∘ σ = centers(c))
    (e : N ≃ₗ[ℤ] N') (hρτ : ∀ j, e (ρ j).primitiveGenerator = (τ (σ j)).primitiveGenerator)
    (hdet : ∀ x y, b'.detDualEquiv (e x) (e y) = b.detDualEquiv x y)
    {Δ : Fan i} (hΔΦ : Δ.IsSubdivision Φ)
    (hΔΩ : Δ.IsSubdivision (Ψ.mapEquiv Φ.lattice e.symm)) (hΔ : Δ.IsRegular)
    (hP : IsNodalBoundaryTower D s (𝟙 X) P) (hQ : IsNodalBoundaryTower E t (𝟙 X') Q)
    (a : Y ≅ (internalBlowupTower b ρ centers(c)).1)
    (a' : Y' ≅ (internalBlowupTower b' τ centers(d)).1)
    (ha : a.hom ≫ (internalBlowupTower b ρ centers(c)).2.toTower.toBase ≫
      Φ.algebraicRealizationStructureMap = P.toBase ≫ s)
    (ha' : a'.hom ≫ (internalBlowupTower b' τ centers(d)).2.toTower.toBase ≫
      Ψ.algebraicRealizationStructureMap = Q.toBase ≫ t)
    (hb : (((internalBlowupTower b ρ centers(c)).2.boundaryι.ker).comap a.hom).support =
      (D.comap P.toBase).support)
    (hb' : (((internalBlowupTower b' τ centers(d)).2.boundaryι.ker).comap a'.hom).support =
      (E.comap Q.toBase).support)
    (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
    (hnodalD : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s))
    (hnodalE : AtWorstNodalOfRelativeDimensionOne (E.subschemeι ≫ t))
    (hconn : _root_.IsConnected (D.support : Set X))
    (hnefD : LineBundleClass.IsNef ℂ s classOf(hD))
    (hnefE : LineBundleClass.IsNef ℂ t classOf(hE))
    (hsqD : Chow.classIntersectionNumber ℂ X classOf(hD) classOf(hD) = 0)
    (hsqE : Chow.classIntersectionNumber ℂ X' classOf(hE) classOf(hE) = 0) :
    letI := hP.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two s
    letI := hQ.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two t
    let Ω := Ψ.mapEquiv Φ.lattice e.symm
    let g : FanEquiv Ψ Ω := Ψ.mapEquivIso Φ.lattice e.symm
    ∃ f : X ≅ X', f.hom ≫ t = s ∧ E.comap f.hom = D ∧
      f.hom.toRationalMap.comp (contractedXEvaluation b' τ d hΨ (a'.inv ≫ Q.toBase)) =
        (contractedXEvaluation b ρ c hΦ (a.inv ≫ P.toBase)).compHom (renameX(σ.symm)) ∧
      ((∀ a b, a < b → σ b < σ a →
        (τ (σ a), centers(d) (σ a)) ≠ (τ (σ b), centers(d) (σ b))) →
        ∀ (L : LineBundleClass X) (L' : LineBundleClass X'),
          let x := (internalBlowupPicardMarking b ρ centers(c) hΦ).symm
            (Additive.ofMul (pullback (a.inv ≫ P.toBase) L))
          let y := (internalBlowupPicardMarking b' τ centers(d) hΨ).symm
            (Additive.ofMul (pullback (a'.inv ≫ Q.toBase) L'))
          pullback f.hom L' = L ↔
            (Additive.ofMul (pullback hΔΦ.toFanHom.algebraicMap x.1.toMul), x.2) =
              (Additive.ofMul (pullback
                (hΔΩ.toFanHom.algebraicMap ≫ g.symm.toFanHom.algebraicMap) y.1.toMul),
                y.2 ∘ σ)) := by
  have := hP.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two s
  have := hQ.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two t
  let Ω := Ψ.mapEquiv Φ.lattice e.symm
  let g : FanEquiv Ψ Ω := Ψ.mapEquivIso Φ.lattice e.symm
  let hΩ₀ : Nonempty Ω.cones := hΨ₀.map g.coneEquiv
  let τ' := g.rayEquiv ∘ τ ∘ σ
  have hmatch (j : Fin n) : (ρ j).primitiveGenerator = (τ' j).primitiveGenerator := by
    simp only [τ', Function.comp_apply, FanEquiv.primitiveGenerator_rayEquiv, g,
      mapEquivIso_latticeEquiv, LinearEquiv.coe_addEquiv_apply, ← hρτ, LinearEquiv.symm_apply_apply]
  have hdet' (x y : N') : b.detDualEquiv (g.latticeEquiv x) (g.latticeEquiv y) =
      b'.detDualEquiv x y := by
    simpa only [g, mapEquivIso_latticeEquiv, LinearEquiv.coe_addEquiv_apply,
      LinearEquiv.apply_symm_apply] using (hdet (e.symm x) (e.symm y)).symm
  have h := g.exists_iso_reindex_transport_internalBlowupTower b' b hdet' τ centers(d) hΨ σ
  dsimp only at h
  rw [hc] at h
  obtain ⟨f, hf, hfB⟩ := h
  let B := internalBlowupTower (h₀ := hΩ₀) b τ' centers(c)
  have ha'' : (a' ≪≫ f).hom ≫ B.2.toTower.toBase ≫ Ω.algebraicRealizationStructureMap =
      Q.toBase ≫ t := by
    rw [Iso.trans_hom, Category.assoc]
    rw [reassoc_of% hf, FanHom.algebraicMap_comp_algebraicRealizationStructureMap, ha']
  have hb'' : (B.2.boundaryι.ker.comap (a' ≪≫ f).hom).support = (E.comap Q.toBase).support := by
    rw [Iso.trans_hom, comap_comp, hfB, hb']
  have hΩ := g.isRegular_iff.mpr hΨ
  let : Nonempty Δ.cones := hΔΦ.nonempty_cones_of_nonempty hΦ₀
  obtain ⟨iso, hover, hpair, heval, hpic⟩ := exists_iso_of_matching_toric_models b hΔΦ hΔΩ hΔ hΦ hΩ
    ρ τ' c hmatch hP hQ a (a' ≪≫ f) ha ha'' hb hb'' hD hE hnodalD hnodalE hconn hnefD hnefE
    hsqD hsqE
  have htransport := g.contractedXEvaluation_eq_of_reindex_transport b' b hΨ hΩ τ d c σ hc hdet'
    (a'.inv ≫ Q.toBase) f hf
  refine ⟨iso, hover, hpair, ?_, ?_⟩
  · simp only [htransport, Scheme.RationalMap.comp_compHom, Iso.trans_inv, Category.assoc]
      at heval ⊢
    rw [heval]
  · intro horder L L'
    have hcoords := g.internalBlowupPicardMarking_symm_pullback_inv_of_reindex b' τ b hΨ hΩ
      centers(d) centers(c) σ hc hdet' horder f hf (pullback (a'.inv ≫ Q.toBase) L')
    have h := hpic L L'
    dsimp only at h
    rw [Iso.trans_inv, Category.assoc, ← pullback_comp f.inv, hcoords] at h
    simpa only [Prod.fst, Prod.snd, toMul_ofMul, pullback_comp] using h

local instance : IsNoetherian X := isNoetherian_of_finiteType s

local instance : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
  (s).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two

/-- For a primitive anticanonical cycle with its Picard marking, equality of the
exchange matrices identifies the two original pairs once the center parameters agree
in the given label order, with the associated relabeling of independent X coordinates. -/
theorem exists_iso_of_equal_endpoint_exchange_matrix
    [Scheme.IsRationalOver s] [Φ.algebraicRealization.IsProjectiveOver ℂ]
    (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hcΦ : Φ.IsComplete) (hcΨ : Ψ.IsComplete)
    (ρ : Fin n → Φ.Ray) (τ : Fin n → Ψ.Ray) (c d : Multiplicative (Fin n → ℤ) →* ℂˣ)
    (σ : Equiv.Perm (Fin n)) (hc : centers(d) ∘ σ = centers(c))
    (hP : IsNodalBoundaryTower D s (𝟙 X) P) (hQ : IsNodalBoundaryTower E t (𝟙 X') Q)
    (a : Y ≅ (internalBlowupTower b ρ centers(c)).1)
    (a' : Y' ≅ (internalBlowupTower b' τ centers(d)).1)
    (ha : a.hom ≫ (internalBlowupTower b ρ centers(c)).2.toTower.toBase ≫
      Φ.algebraicRealizationStructureMap = P.toBase ≫ s)
    (ha' : a'.hom ≫ (internalBlowupTower b' τ centers(d)).2.toTower.toBase ≫
      Ψ.algebraicRealizationStructureMap = Q.toBase ≫ t)
    (hb : (((internalBlowupTower b ρ centers(c)).2.boundaryι.ker).comap a.hom).support =
      (D.comap P.toBase).support)
    (hb' : (((internalBlowupTower b' τ centers(d)).2.boundaryι.ker).comap a'.hom).support =
      (E.comap Q.toBase).support)
    (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
    (hnodalD : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s))
    (hnodalE : AtWorstNodalOfRelativeDimensionOne (E.subschemeι ≫ t))
    (hconn : _root_.IsConnected (D.support : Set X))
    (hnefD : LineBundleClass.IsNef ℂ s classOf(hD))
    (hnefE : LineBundleClass.IsNef ℂ t classOf(hE))
    (hsqD : Chow.classIntersectionNumber ℂ X classOf(hD) classOf(hD) = 0)
    (hsqE : Chow.classIntersectionNumber ℂ X' classOf(hE) classOf(hE) = 0)
    {k : ℕ} [NeZero k] (C : ZMod k → Additive (LineBundleClass X))
    (hGram : ∀ j l : ZMod k, Chow.intersectionBilinForm ℂ X (C j) (C l) =
      (-2 : ℤ) * (if j = l then 1 else 0) +
        (if l = j + 1 then 1 else 0) + (if l = j - 1 then 1 else 0))
    (hspan : Scheme.Opens.primeDivisorSpanCompl D.support.compl =
      Submodule.span ℤ (Set.range C))
    (hcan : ∑ j, C j = -Additive.ofMul (LineBundleClass.mk (canonicalBundle ℂ X 2)))
    (hδ : TauCeti.IsPrimitive (∑ j, C j))
    (hmat : chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap ρ) =
      chargeExchangeMatrix b'.detDualEquiv.toLinearMap (rayChargeMap (τ ∘ σ))) :
    letI := hP.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two s
    letI := hQ.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two t
    ∃ f : X ≅ X', f.hom ≫ t = s ∧ E.comap f.hom = D ∧
      f.hom.toRationalMap.comp (contractedXEvaluation b' τ d hΨ (a'.inv ≫ Q.toBase)) =
        (contractedXEvaluation b ρ c hΦ (a.inv ≫ P.toBase)).compHom (renameX(σ.symm)) := by
  have := hP.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two s
  have := hQ.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two t
  let A := internalBlowupTower b ρ centers(c)
  have haInv : a.inv ≫ P.toBase ≫ s =
      A.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap := by
    rw [← ha, Iso.inv_hom_id_assoc]
  have hbInv : ((D.comap P.toBase).comap a.inv).support = A.2.boundaryι.ker.support := by
    have h := congrArg (fun Z : Closeds Y ↦ Z.preimage a.inv.continuous) hb.symm
    simpa only [← support_comap, ← comap_comp, Iso.inv_hom_id, comap_id] using h
  obtain ⟨e, ⟨hρτ, hdet⟩, -⟩ := existsUnique_rayChargeEquiv_of_anticanonical_cycle ρ (τ ∘ σ)
    b b' centers(c) hΦ hcΦ hP a haInv hbInv C hGram hspan hcan hδ hmat
  let Ω := Ψ.mapEquiv Φ.lattice e.symm
  let g : FanEquiv Ψ Ω := Ψ.mapEquivIso Φ.lattice e.symm
  have hΩc : Ω.IsComplete := g.isComplete_iff.mpr hcΨ
  have hs : Φ.support = Ω.support := by
    ext x
    exact iff_of_true (Φ.mem_support.mpr ((Φ.isComplete_iff).mp hcΦ x))
      (Ω.mem_support.mpr ((Ω.isComplete_iff).mp hΩc x))
  have hrank := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  obtain ⟨Δ, hΔΦ, hΔΩ, hΔ⟩ :=
    Φ.exists_regular_common_subdivision Ω hΦ (g.isRegular_iff.mpr hΨ) hrank hs
  obtain ⟨f, hover, hpair, heval, _⟩ :=
    exists_iso_of_matching_toric_models_of_latticeEquiv b b' hΦ hΨ
      ρ τ c d σ hc e hρτ hdet hΔΦ hΔΩ hΔ hP hQ a a' ha ha' hb hb' hD hE
      hnodalD hnodalE hconn hnefD hnefE hsqD hsqE
  exact ⟨f, hover, hpair, heval⟩

end SquareZero

end TauCeti.Toric.Fan

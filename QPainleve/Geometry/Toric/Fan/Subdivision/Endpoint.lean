/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Transport
public import QPainleve.Geometry.Toric.Fan.Picard.Endpoint
public import QPainleve.Geometry.Toric.Fan.Subdivision.NodalRefinement

import QPainleve.Geometry.Toric.Fan.Equiv

/-!
# Comparison of toric endpoints across lattice equivalences

An integral equivalence that matches the labeled charges and preserves the determinant
pairing allows the endpoint models to be compared in a common lattice. The ordered
binomial centers are transported along the fan equivalence and reindexed before taking a
common nodal refinement. Square-zero boundary descent then identifies the original pairs.
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open QPainleve.Cluster TopologicalSpace
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones] {n : ℕ}

private theorem exists_iso_reindex_transport_internalBlowupTower
    (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
    {Ω : Fan i} (g : FanEquiv Ψ Ω) [hΩ₀ : Nonempty Ω.cones]
    (hdet : ∀ x y, b.detDualEquiv (g.latticeEquiv x) (g.latticeEquiv y) = b'.detDualEquiv x y)
    (hΨ : Ψ.IsRegular)
    (τ : Fin n → Ψ.Ray) (c : Fin n → ℂˣ) (σ : Equiv.Perm (Fin n)) :
    let A := internalBlowupTower b' τ c
    let B := internalBlowupTower (h₀ := hΩ₀) b (g.rayEquiv ∘ τ ∘ σ) (c ∘ σ)
    ∃ f : A.1 ≅ B.1,
      f.hom ≫ B.2.toTower.toBase ≫ Ω.algebraicRealizationStructureMap =
        A.2.toTower.toBase ≫ Ψ.algebraicRealizationStructureMap ∧
      B.2.boundaryι.ker.comap f.hom = A.2.boundaryι.ker := by
  dsimp only
  let A := internalBlowupTower b' τ c
  let B := internalBlowupTower (h₀ := hΩ₀) b (g.rayEquiv ∘ τ ∘ σ) (c ∘ σ)
  obtain ⟨f, hf, hfB⟩ := exists_iso_internalBlowupTower_reindex b' τ c σ
  obtain ⟨f', ⟨hf', hf'B⟩, -⟩ :=
    g.existsUnique_isLift_internalBlowupTower b' b hdet (τ ∘ σ) (c ∘ σ) hΨ
  refine ⟨f ≪≫ f', ?_, ?_⟩
  · simp only [Iso.trans_hom, Category.assoc, reassoc_of% hf'.hom_toBase, asIso_hom,
      FanHom.algebraicMap_comp_algebraicRealizationStructureMap, reassoc_of% hf]
  · have hk : (A.2.boundaryι ≫ (f ≪≫ f').hom).ker = B.2.boundaryι.ker := by
      rw [Iso.trans_hom, ← Category.assoc, hfB, hf'B, Scheme.Hom.ker_comp_of_isIso]
    rw [← hk, Scheme.Hom.comap_ker_comp_of_isClosedImmersion]

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
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

/-- Identify two nef square-zero nodal pairs when an oriented integral equivalence matches
the charges of their complete toric models and the two center families agree after
relabeling. The order comparison allows repeated centers. -/
theorem exists_iso_of_matching_toric_models_of_latticeEquiv
    (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hcΦ : Φ.IsComplete) (hcΨ : Ψ.IsComplete)
    (ρ : Fin n → Φ.Ray) (τ : Fin n → Ψ.Ray) (c d : Fin n → ℂˣ)
    (σ : Equiv.Perm (Fin n)) (hc : d ∘ σ = c)
    (e : N ≃ₗ[ℤ] N') (hρτ : ∀ j, e (ρ j).primitiveGenerator = (τ (σ j)).primitiveGenerator)
    (hdet : ∀ x y, b'.detDualEquiv (e x) (e y) = b.detDualEquiv x y)
    (hP : IsNodalBoundaryTower D s (𝟙 X) P) (hQ : IsNodalBoundaryTower E t (𝟙 X') Q)
    (a : Y ≅ (internalBlowupTower b ρ c).1) (a' : Y' ≅ (internalBlowupTower b' τ d).1)
    (ha : a.hom ≫ (internalBlowupTower b ρ c).2.toTower.toBase ≫
      Φ.algebraicRealizationStructureMap = P.toBase ≫ s)
    (ha' : a'.hom ≫ (internalBlowupTower b' τ d).2.toTower.toBase ≫
      Ψ.algebraicRealizationStructureMap = Q.toBase ≫ t)
    (hb : (((internalBlowupTower b ρ c).2.boundaryι.ker).comap a.hom).support =
      (D.comap P.toBase).support)
    (hb' : (((internalBlowupTower b' τ d).2.boundaryι.ker).comap a'.hom).support =
      (E.comap Q.toBase).support)
    (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
    (hnodalD : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s))
    (hnodalE : AtWorstNodalOfRelativeDimensionOne (E.subschemeι ≫ t))
    (hconn : _root_.IsConnected (D.support : Set X))
    (hnefD : LineBundleClass.IsNef ℂ s classOf(hD))
    (hnefE : LineBundleClass.IsNef ℂ t classOf(hE))
    (hsqD : Chow.classIntersectionNumber ℂ X classOf(hD) classOf(hD) = 0)
    (hsqE : Chow.classIntersectionNumber ℂ X' classOf(hE) classOf(hE) = 0) :
    ∃ f : X ≅ X', f.hom ≫ t = s ∧ E.comap f.hom = D := by
  let Ω := Ψ.mapEquiv Φ.lattice e.symm
  let g : FanEquiv Ψ Ω := Ψ.mapEquivIso Φ.lattice e.symm
  have hΩc : Ω.IsComplete := g.isComplete_iff.mpr hcΨ
  let hΩ₀ : Nonempty Ω.cones := hΩc.nonempty_cones
  let τ' := g.rayEquiv ∘ τ ∘ σ
  have hmatch (j : Fin n) : (ρ j).primitiveGenerator = (τ' j).primitiveGenerator := by
    simp only [τ', Function.comp_apply, FanEquiv.primitiveGenerator_rayEquiv, g,
      mapEquivIso_latticeEquiv, LinearEquiv.coe_addEquiv_apply, ← hρτ, LinearEquiv.symm_apply_apply]
  have hs : Φ.support = Ω.support := by
    ext x
    exact iff_of_true (Φ.mem_support.mpr ((Φ.isComplete_iff).mp hcΦ x))
      (Ω.mem_support.mpr ((Ω.isComplete_iff).mp hΩc x))
  have hdet' (x y : N') : b.detDualEquiv (g.latticeEquiv x) (g.latticeEquiv y) =
      b'.detDualEquiv x y := by
    simpa only [g, mapEquivIso_latticeEquiv, LinearEquiv.coe_addEquiv_apply,
      LinearEquiv.apply_symm_apply] using (hdet (e.symm x) (e.symm y)).symm
  have h := exists_iso_reindex_transport_internalBlowupTower b b' g hdet' hΨ τ d σ
  dsimp only at h
  rw [hc] at h
  obtain ⟨f, hf, hfB⟩ := h
  let B := internalBlowupTower (h₀ := hΩ₀) b τ' c
  have ha'' : (a' ≪≫ f).hom ≫ B.2.toTower.toBase ≫ Ω.algebraicRealizationStructureMap =
      Q.toBase ≫ t := by
    rw [Iso.trans_hom, Category.assoc]
    exact (congrArg (a'.hom ≫ ·) hf).trans ha'
  have hb'' : (B.2.boundaryι.ker.comap (a' ≪≫ f).hom).support = (E.comap Q.toBase).support := by
    rw [Iso.trans_hom, comap_comp, hfB, hb']
  exact exists_iso_of_matching_toric_models b hΦ (g.isRegular_iff.mpr hΨ) hs ρ τ' c
    hmatch hP hQ a (a' ≪≫ f) ha ha'' hb hb'' hD hE hnodalD hnodalE hconn hnefD hnefE hsqD hsqE

local instance : IsNoetherian X := isNoetherian_of_finiteType s

local instance : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
  (s).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two

/-- For a primitive anticanonical cycle with its Picard marking, equality of the
exchange matrices identifies the two original pairs once the center parameters agree
in the given label order. -/
theorem exists_iso_of_equal_endpoint_exchange_matrix
    [Scheme.IsRationalOver s] [Φ.algebraicRealization.IsProjectiveOver ℂ]
    (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hcΦ : Φ.IsComplete) (hcΨ : Ψ.IsComplete)
    (ρ : Fin n → Φ.Ray) (τ : Fin n → Ψ.Ray) (c d : Fin n → ℂˣ)
    (σ : Equiv.Perm (Fin n)) (hc : d ∘ σ = c)
    (hP : IsNodalBoundaryTower D s (𝟙 X) P) (hQ : IsNodalBoundaryTower E t (𝟙 X') Q)
    (a : Y ≅ (internalBlowupTower b ρ c).1) (a' : Y' ≅ (internalBlowupTower b' τ d).1)
    (ha : a.hom ≫ (internalBlowupTower b ρ c).2.toTower.toBase ≫
      Φ.algebraicRealizationStructureMap = P.toBase ≫ s)
    (ha' : a'.hom ≫ (internalBlowupTower b' τ d).2.toTower.toBase ≫
      Ψ.algebraicRealizationStructureMap = Q.toBase ≫ t)
    (hb : (((internalBlowupTower b ρ c).2.boundaryι.ker).comap a.hom).support =
      (D.comap P.toBase).support)
    (hb' : (((internalBlowupTower b' τ d).2.boundaryι.ker).comap a'.hom).support =
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
    ∃ f : X ≅ X', f.hom ≫ t = s ∧ E.comap f.hom = D := by
  let A := internalBlowupTower b ρ c
  have haInv : a.inv ≫ P.toBase ≫ s =
      A.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap := by
    rw [← ha, Iso.inv_hom_id_assoc]
  have hbInv : ((D.comap P.toBase).comap a.inv).support = A.2.boundaryι.ker.support := by
    have h := congrArg (fun Z : Closeds Y ↦ Z.preimage a.inv.continuous) hb.symm
    simpa only [← support_comap, ← comap_comp, Iso.inv_hom_id, comap_id] using h
  obtain ⟨e, ⟨hρτ, hdet⟩, -⟩ := existsUnique_rayChargeEquiv_of_anticanonical_cycle ρ (τ ∘ σ)
    b b' c hΦ hcΦ hP a haInv hbInv C hGram hspan hcan hδ hmat
  exact exists_iso_of_matching_toric_models_of_latticeEquiv b b' hΦ hΨ hcΦ hcΨ
    ρ τ c d σ hc e hρτ hdet hP hQ a a' ha ha' hb hb' hD hE hnodalD hnodalE hconn hnefD hnefE
    hsqD hsqE

end SquareZero

end TauCeti.Toric.Fan

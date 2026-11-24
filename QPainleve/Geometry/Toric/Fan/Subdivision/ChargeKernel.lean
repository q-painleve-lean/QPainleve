/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Subdivision.Endpoint

import QPainleve.AlgebraicGeometry.Chow.Isomorphism

/-!
# Charge transport across toric endpoints

On the boundary orthogonal, pullback along the isomorphism of matching toric
endpoints reindexes the charge relations. The comparison uses the same isomorphism
that intertwines fixed-center X evaluation and identifies the full Picard markings.
The charge coordinates come from the total exceptional coefficients in the Picard
formula of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, Theorem 5.5](https://arxiv.org/html/1309.2573v2#S5.Thmtheorem5).
The comparison allows ordered towers with infinitely near centers.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData TauCeti.LaurentRing

namespace TauCeti.Toric.Fan

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  [Nonempty Φ.cones] [Nonempty Ψ.cones]
  [Φ.algebraicRealization.IsProjectiveOver ℂ] [Ψ.algebraicRealization.IsProjectiveOver ℂ]
  {n : ℕ} {X X' Y Y' : Scheme} [IsIntegral X] [IsIntegral X']
  [X.Over (Spec (.of ℂ))] [X'.Over (Spec (.of ℂ))]
  [X.IsProjectiveOver ℂ] [X'.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))]
  [SmoothOfRelativeDimension 2 (X' ↘ Spec (.of ℂ))]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm ℂ X)]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm ℂ X')]
  {D : X.IdealSheafData} {E : X'.IdealSheafData} {p q : ℕ}
  {P : QPainleve.BlowupTower X p Y} {Q : QPainleve.BlowupTower X' q Y'}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "centers(" c ")" => (fun j : Fin n ↦ c (ofAdd (Pi.single j 1)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "renameX(" σ ")" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (rename (R := ℂ) (Equiv.toFun σ))))

/-- On the Picard boundary orthogonals, the isomorphism of matching toric endpoints
pulls the class of a charge relation back to the class of the reindexed relation.
The same isomorphism identifies the boundary ideals, intertwines the evaluations,
and compares the full Picard markings on the common subdivision.
Coincident centers retain their relative order. -/
theorem exists_iso_of_matching_toric_models_chargeKernel
    (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (ρ : Fin n → Φ.Ray) (τ : Fin n → Ψ.Ray) (c d : Multiplicative (Fin n → ℤ) →* ℂˣ)
    (σ : Equiv.Perm (Fin n)) (hc : centers(d) ∘ σ = centers(c))
    (e : N ≃ₗ[ℤ] N') (hρτ : ∀ j, e (ρ j).primitiveGenerator = (τ (σ j)).primitiveGenerator)
    (hdet : ∀ x y, b'.detDualEquiv (e x) (e y) = b.detDualEquiv x y)
    {Δ : Fan i} (hΔΦ : Δ.IsSubdivision Φ)
    (hΔΩ : Δ.IsSubdivision (Ψ.mapEquiv Φ.lattice e.symm)) (hΔ : Δ.IsRegular)
    (hP : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) P) (hQ : IsNodalBoundaryTower E (X' ↘ S) (𝟙 X') Q)
    (a : Y ≅ (internalBlowupTower b ρ centers(c)).1)
    (a' : Y' ≅ (internalBlowupTower b' τ centers(d)).1)
    (ha : a.inv ≫ P.toBase ≫ (X ↘ S) =
      (internalBlowupTower b ρ centers(c)).2.toTower.toBase ≫ (Φ.algebraicRealization ↘ S))
    (ha' : a'.inv ≫ Q.toBase ≫ (X' ↘ S) =
      (internalBlowupTower b' τ centers(d)).2.toTower.toBase ≫ (Ψ.algebraicRealization ↘ S))
    (hb : ((D.comap P.toBase).comap a.inv).support =
      (internalBlowupTower b ρ centers(c)).2.boundaryι.ker.support)
    (hb' : ((E.comap Q.toBase).comap a'.inv).support =
      (internalBlowupTower b' τ centers(d)).2.boundaryι.ker.support)
    (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
    (hnodalD : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ (X ↘ S)))
    (hnodalE : AtWorstNodalOfRelativeDimensionOne (E.subschemeι ≫ (X' ↘ S)))
    (hconn : _root_.IsConnected (D.support : Set X))
    (hnefD : LineBundleClass.IsNef ℂ (X ↘ S) classOf(hD))
    (hnefE : LineBundleClass.IsNef ℂ (X' ↘ S) classOf(hE))
    (hsqD : Chow.classIntersectionNumber ℂ X classOf(hD) classOf(hD) = 0)
    (hsqE : Chow.classIntersectionNumber ℂ X' classOf(hE) classOf(hE) = 0)
    (horder : ∀ l m, l < m → σ m < σ l →
      (τ (σ l), centers(d) (σ l)) ≠ (τ (σ m), centers(d) (σ m))) :
    letI := hP.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
    letI := hQ.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X' ↘ S)
    let g := Ψ.mapEquivIso Φ.lattice e.symm
    let hcModel := internalBlowupTower_eq_alongBoundary b ρ centers(c)
    let hdModel := internalBlowupTower_eq_alongBoundary b' τ centers(d)
    let pc := transport_boundaryPresentation hcModel.symm a ha hb
    let pd := transport_boundaryPresentation hdModel.symm a' ha' hb'
    let κ := markedBoundaryChargeEquiv hΦ b ρ hP
      (a ≪≫ eqToIso (congrArg Sigma.fst hcModel)) pc.1 pc.2
    let κ' := markedBoundaryChargeEquiv hΨ b' τ hQ
      (a' ≪≫ eqToIso (congrArg Sigma.fst hdModel)) pd.1 pd.2
    ∃ f : X ≅ X', f.hom ≫ (X' ↘ S) = (X ↘ S) ∧ E.comap f.hom = D ∧
      f.hom.toRationalMap.comp (contractedXEvaluation b' τ d hΨ (a'.inv ≫ Q.toBase)) =
        (contractedXEvaluation b ρ c hΦ (a.inv ≫ P.toBase)).compHom (renameX(σ.symm)) ∧
      (∀ (L : LineBundleClass X) (L' : LineBundleClass X'),
        let x := (internalBlowupPicardMarking b ρ centers(c) hΦ).symm
          (Additive.ofMul (pullback (a.inv ≫ P.toBase) L))
        let y := (internalBlowupPicardMarking b' τ centers(d) hΨ).symm
          (Additive.ofMul (pullback (a'.inv ≫ Q.toBase) L'))
        pullback f.hom L' = L ↔
          (Additive.ofMul (pullback hΔΦ.toFanHom.algebraicMap x.1.toMul), x.2) =
            (Additive.ofMul (pullback
              (hΔΩ.toFanHom.algebraicMap ≫ g.symm.toFanHom.algebraicMap) y.1.toMul),
              y.2 ∘ σ)) ∧
      ∀ x : (rayChargeMap τ).ker,
        pullback f.hom (κ'.symm x).val.toMul =
          (κ.symm (rayChargeKernelReindex σ e.toLinearMap e.injective hρτ x)).val.toMul := by
  intro g hcModel hdModel pc pd κ κ'
  let := hP.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
  let := hQ.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X' ↘ S)
  have hbase := congrArg (fun g ↦ a.hom ≫ g) ha
  have hbase' := congrArg (fun g ↦ a'.hom ≫ g) ha'
  simp only [← Category.assoc, a.hom_inv_id, a'.hom_inv_id, Category.id_comp,
    algebraicRealization_over] at hbase hbase'
  have hs := congrArg (fun Z : TopologicalSpace.Closeds (internalBlowupTower b ρ centers(c)).1 ↦
    Z.preimage a.hom.continuous) hb
  have hs' := congrArg (fun Z : TopologicalSpace.Closeds (internalBlowupTower b' τ centers(d)).1 ↦
    Z.preimage a'.hom.continuous) hb'
  simp only [← support_comap, ← comap_comp, Iso.hom_inv_id_assoc] at hs hs'
  obtain ⟨f, hf, hfD, -, hfX, hpic⟩ := exists_iso_of_matching_toric_models_of_latticeEquiv
    b b' hΦ hΨ ρ τ c d σ hc e hρτ hdet hΔΦ hΔΩ hΔ hP hQ a a'
    (by simpa only [Category.assoc] using hbase.symm)
    (by simpa only [Category.assoc] using hbase'.symm)
    hs.symm hs'.symm hD hE hnodalD hnodalE hconn hnefD hnefE hsqD hsqE
  refine ⟨f, hf, hfD, hfX, hpic horder, fun x ↦ ?_⟩
  let : f.hom.IsOver S := ⟨hf⟩
  let L' := κ'.symm x
  have hsupport := congrArg (fun I : X.IdealSheafData ↦ I.support) hfD
  have hmem : Additive.ofMul (pullback f.hom L'.val.toMul) ∈ D.boundaryOrthogonal ℂ :=
    (D.pullback_mem_boundaryOrthogonal_iff E f.hom hsupport L'.val.toMul).mpr
      (by simpa only [ofMul_toMul] using L'.property)
  let L : D.boundaryOrthogonal ℂ := ⟨_, hmem⟩
  have hcoords := congrArg Prod.snd ((hpic horder L.val.toMul L'.val.toMul).mp (by
    simp only [L, toMul_ofMul]))
  have hsource := internalBlowupPicardMarking_symm_pullback_snd_eq_neg_charge
    hΦ b ρ hP (a := a) ha hb L
  have htarget := internalBlowupPicardMarking_symm_pullback_snd_eq_neg_charge
    hΨ b' τ hQ (a := a') ha' hb' L'
  dsimp only at hcoords
  rw [hsource, htarget] at hcoords
  have hκ' : κ' L' = x := κ'.apply_symm_apply x
  simp only [κ'] at hκ'
  have hκ : κ L = rayChargeKernelReindex σ e.toLinearMap e.injective hρτ x := by
    apply Subtype.ext
    funext j
    have hj := congrFun hcoords j
    simpa only [κ, Pi.neg_apply, Function.comp_apply, hκ', neg_inj,
      rayChargeKernelReindex_apply] using hj
  have heq := congrArg (fun y ↦ (κ.symm y).val.toMul) hκ
  simpa only [LinearEquiv.symm_apply_apply, L, toMul_ofMul] using heq

end TauCeti.Toric.Fan

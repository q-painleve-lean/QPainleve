/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.ProjectiveLineCharts.Overlap
public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch.Transition

import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Basic
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Scaling
import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch.Gluing

/-!
# Split projective bundle charts on a Hirzebruch ruling

The standard charts of the projectivization of `𝒪(a) ⊞ 𝒪(b)` have the
Hirzebruch transition of parameter `b - a`. The comparison identifies the
unit `X₁ / X₀` in the ring of sections on the overlap with the Laurent
parameter on the base torus. It provides the chart compatibility for the
ruled case of [Gross, Hacking and Keel, Proposition 1.3][GHK].

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory LaurentPolynomial Limits Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.projectiveLine

namespace TauCeti.Toric.Fan

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => projectiveLine ℂ
local notation "p" => (P ↘ S)
local notation "L" => LaurentPolynomial ℂ
local notation "Q" => Spec (CommRingCat.of L)
local notation "A[" k "]" => Fan.algebraicRealization (projectiveLineAffineFan k)
local notation "j[" k "]" => projectiveLineAffineFanι k
local notation "s[" k "]" => algebraicRealizationStructureMap (projectiveLineAffineFan k)
local notation "H[" k "]" => pullback p s[k]
local notation "T₀" => projectiveLineTorusFan.algebraicRealization
local notation "t" => (T₀ ↘ S)
local notation "Hₜ" => pullback p t
local notation "iT" => projectiveLineTorusι
local notation "eT" => projectiveLineTorusIsoSpecLaurent
local notation "aT[" k "]" => FanHom.algebraicMap (projectiveLineTorusToAffineFan k)
local notation "d[" k "]" => projectiveLineTorusProductToAffine k
local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule ℂ (Fin 2 → ℂ)
local notation "B[" k "]" => Proj.basicOpen 𝒜 (coord ℂ k)

private abbrev siteRing (U : (P).AffineZariskiSite) : CommRingCat := Γ(P, U.toOpens)

local notation "Γ[" U "]" => CommRingCat.carrier (siteRing U)
local notation "q[" U "]" => (projectiveLine Γ[U] ↘ Spec (CommRingCat.of Γ[U]))

private abbrev siteFromSpec (U : (P).AffineZariskiSite) : Spec (.of Γ[U]) ⟶ P :=
  U.property.fromSpec

local notation "ι[" U "]" => siteFromSpec U

private abbrev siteAlgebra (U : (P).AffineZariskiSite) : Algebra ℂ Γ[U] :=
  (Spec.preimage (ι[U] ≫ p)).hom.toAlgebra

local notation "pΓ[" U "]" => @baseChangeProjection ℂ _ Γ[U] _ (siteAlgebra U)

private def torusSite : (P).AffineZariskiSite :=
  let : IsAffine T₀ := IsAffine.of_isIso (Iso.hom eT)
  ⟨projectiveLineTorusι.opensRange, isAffineOpen_opensRange iT⟩

local notation "V" => torusSite

private theorem torusSite_toOpens : (V).toOpens = B[0] ⊓ B[1] := by
  apply TopologicalSpace.Opens.ext
  have he (i : Fin 2) : Set.range (polynomialChartι ℂ i) = (B[i] : Set P) :=
    congrArg SetLike.coe (opensRange_polynomialChartι ℂ i)
  -- The site was chosen from the open immersion of the torus.
  change (projectiveLineTorusι.opensRange : Set P) = (B[0] : Set P) ∩ (B[1] : Set P)
  rw [Scheme.Hom.coe_opensRange, range_projectiveLineTorusι, he, he]

private theorem torusSite_le (k : Fin 2) : (V).toOpens ≤ B[k] := by
  rw [torusSite_toOpens]
  fin_cases k
  · exact inf_le_left
  · exact inf_le_right

private theorem range_torus_eq_range_fromSpec :
    Set.range iT = Set.range ι[V] :=
  (IsAffineOpen.range_fromSpec (V).property).symm

private def laurentSiteMap : Q ⟶ Spec (.of Γ[V]) :=
  (Iso.inv eT) ≫ (IsOpenImmersion.isoOfRangeEq iT ι[V] range_torus_eq_range_fromSpec).hom

@[reassoc]
private theorem laurentSiteMap_comp_fromSpec :
    laurentSiteMap ≫ ι[V] = (Iso.inv eT) ≫ iT := by
  unfold laurentSiteMap
  rw [Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]

private abbrev laurentSiteRingHom : Γ[V] →+* L := (Spec.preimage laurentSiteMap).hom

private theorem laurentSiteRingHom_affineCoordinateUnit :
    laurentSiteRingHom (affineCoordinateUnit ℂ (torusSite_le 0) (torusSite_le 1)) = T 1 := by
  let f := polynomialChartι ℂ 0
  let h := (preimage_polynomialChartι_basicOpen_self ℂ 0).ge
  have hB : IsAffineOpen (B[0]) :=
    (opensRange_polynomialChartι ℂ 0) ▸ isAffineOpen_opensRange f
  let ψ := f.appLE (B[0]) ⊤ h ≫ (Scheme.ΓSpecIso (.of (Polynomial ℂ))).hom
  have hψ : Spec.map ψ ≫ hB.fromSpec = f := by
    rw [Spec.map_comp, Category.assoc,
      hB.SpecMap_appLE_fromSpec f (isAffineOpen_top _) h, IsAffineOpen.fromSpec_top]
    simp [Scheme.isoSpec_Spec_inv]
  let res := (P).presheaf.map (homOfLE (torusSite_le 0)).op
  have hc : res ≫ Spec.preimage laurentSiteMap =
      ψ ≫ CommRingCat.ofHom (algebraMap (Polynomial ℂ) L) := by
    apply Spec.map_injective
    apply (cancel_mono hB.fromSpec).mp
    simp only [Spec.map_comp, Spec.map_preimage, Category.assoc]
    rw [hB.map_fromSpec (V).property, laurentSiteMap_comp_fromSpec, hψ,
      ← projectiveLineTorusIsoSpecLaurent_hom_comp_chart, Iso.inv_hom_id_assoc]
  have hX : ψ (affineCoordinate ℂ 0) = Polynomial.X := by
    rw [affineCoordinate_def]
    exact (appLE_polynomialChartι_awayToSection ℂ 0 _).trans (AlgEquiv.apply_symm_apply _ _)
  rw [coe_affineCoordinateUnit, ← CommRingCat.comp_apply, hc, CommRingCat.comp_apply, hX]
  exact Polynomial.toLaurent_X

private theorem map_affineCoordinateUnit_zpow (n : ℤ) :
    (affineCoordinateUnit ℂ (torusSite_le 0) (torusSite_le 1) ^ n).map
      laurentSiteRingHom.toMonoidHom = (LaurentPolynomial.isUnit_T n).unit := by
  have ht : (affineCoordinateUnit ℂ (torusSite_le 0) (torusSite_le 1)).map
      laurentSiteRingHom.toMonoidHom = LaurentPolynomial.genericUnit ℂ := by
    apply Units.ext
    rw [Units.coe_map, LaurentPolynomial.genericUnit_val]
    exact laurentSiteRingHom_affineCoordinateUnit
  rw [map_zpow, ht]
  apply Units.ext
  exact LaurentPolynomial.genericUnit_zpow_val ℂ n

private theorem laurentSiteMap_comp_structure :
    laurentSiteMap ≫ ι[V] ≫ p = Spec.map (CommRingCat.ofHom (algebraMap ℂ L)) := by
  rw [laurentSiteMap_comp_fromSpec_assoc, comp_over,
    ← projectiveLineTorusIsoSpecLaurent_hom_comp_toBase, Iso.inv_hom_id_assoc]

private abbrev laurentAlgebra : Algebra Γ[V] L := laurentSiteRingHom.toAlgebra

private theorem laurentScalarTower :
    let := siteAlgebra V
    let := laurentAlgebra
    IsScalarTower ℂ Γ[V] L := by
  let := siteAlgebra V
  let := laurentAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  have h : CommRingCat.ofHom (algebraMap ℂ L) =
      Spec.preimage (ι[V] ≫ p) ≫ Spec.preimage laurentSiteMap := by
    rw [← Spec.preimage_map (CommRingCat.ofHom (algebraMap ℂ L)),
      ← laurentSiteMap_comp_structure, Spec.preimage_comp]
  exact congrArg (fun f : CommRingCat.of ℂ ⟶ CommRingCat.of L ↦ f.hom) h

local notation "J" => IsPullback.isoPullback isPullback_projectiveLineTorusProduct
local notation "E" => Iso.symm J ≪≫ projectiveLineTorusProductIsoLaurent
local notation "qL" => (projectiveLine L ↘ Q)
local notation "pL" => baseChangeProjection ℂ L

private theorem laurentProduct_hom_fst : (E).hom ≫ pL = pullback.fst p t := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    projectiveLineTorusProductIsoLaurent_hom_baseChangeProjection]
  exact isPullback_projectiveLineTorusProduct.isoPullback_inv_fst

@[reassoc]
private theorem laurentProduct_hom_snd : (E).hom ≫ qL = pullback.snd p t ≫ (Iso.hom eT) := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    projectiveLineTorusProductIsoLaurent_hom_toBase,
    IsPullback.isoPullback_inv_snd_assoc]

private def overlapToSite : Hₜ ⟶ projectiveLine Γ[V] :=
  (E).hom ≫ @baseChangeProjection Γ[V] _ L _ laurentAlgebra

private theorem overlapToSite_fst : overlapToSite ≫ pΓ[V] = pullback.fst p t := by
  let := siteAlgebra V
  let := laurentAlgebra
  let := laurentScalarTower
  rw [overlapToSite, Category.assoc, baseChangeProjection_comp, laurentProduct_hom_fst]

@[reassoc]
private theorem overlapToSite_snd :
    overlapToSite ≫ q[V] = pullback.snd p t ≫ (Iso.hom eT) ≫ laurentSiteMap := by
  let := laurentAlgebra
  rw [overlapToSite, Category.assoc, (isPullback_baseChangeProjection Γ[V] L).w,
    laurentProduct_hom_snd_assoc, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom,
    Spec.map_preimage]

@[reassoc]
private theorem overlapToSite_comp_scaling (n : ℤ) :
    (hirzebruchRulingOverlapTransition (-n)).hom ≫ overlapToSite =
      overlapToSite ≫ (scalingBy Γ[V]
        (affineCoordinateUnit ℂ (torusSite_le 0) (torusSite_le 1) ^ n)).hom := by
  let := laurentAlgebra
  have h : (affineCoordinateUnit ℂ (torusSite_le 0) (torusSite_le 1) ^ n).map
      (algebraMap Γ[V] L).toMonoidHom = (LaurentPolynomial.isUnit_T n).unit :=
    map_affineCoordinateUnit_zpow n
  simp only [overlapToSite, hirzebruchRulingOverlapTransition_hom_comp_laurentProduct_assoc,
    Category.assoc, baseChangeProjection_comp_scalingBy, ← RingHom.toMonoidHom_eq_coe, neg_neg, h]

section Restriction

variable (U : (P).AffineZariskiSite)

private abbrev restrictionMap (hVU : (V).toOpens ≤ U.toOpens) :
    Γ(P, U.toOpens) ⟶ Γ(P, (V).toOpens) :=
  (P).presheaf.map (homOfLE hVU : (V).toOpens ⟶ U.toOpens).op

private theorem restrictionMap_comp_algebraMap (hVU : (V).toOpens ≤ U.toOpens) :
    let := siteAlgebra U
    let := siteAlgebra V
    let := (restrictionMap U hVU).hom.toAlgebra
    IsScalarTower ℂ Γ[U] Γ[V] := by
  let := siteAlgebra U
  let := siteAlgebra V
  let := (restrictionMap U hVU).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  have h : Spec.preimage (ι[V] ≫ p) = Spec.preimage (ι[U] ≫ p) ≫ restrictionMap U hVU := by
    apply Spec.map_injective
    simp only [Spec.map_comp, Spec.map_preimage]
    exact (U.property.map_fromSpec_assoc (V).property _ p).symm
  exact congrArg (fun f : CommRingCat.of ℂ ⟶ siteRing V ↦ f.hom) h

private abbrev overlapRestriction (hVU : (V).toOpens ≤ U.toOpens) :
    projectiveLine Γ[V] ⟶ projectiveLine Γ[U] :=
  @baseChangeProjection Γ[U] _ Γ[V] _ (restrictionMap U hVU).hom.toAlgebra

private theorem torusProductToAffine_comp_splitChart (hVU : (V).toOpens ≤ U.toOpens) (k : Fin 2)
    (a : A[k] ⟶ Spec (.of Γ[U])) (ha : a ≫ ι[U] = j[k])
    (v : H[k] ⟶ projectiveLine Γ[U])
    (hv₁ : v ≫ pΓ[U] = pullback.fst p s[k])
    (hv₂ : v ≫ q[U] = pullback.snd p s[k] ≫ a) :
    d[k] ≫ v = overlapToSite ≫ overlapRestriction U hVU := by
  let := siteAlgebra U
  let := siteAlgebra V
  let := (restrictionMap U hVU).hom.toAlgebra
  let := restrictionMap_comp_algebraMap U hVU
  apply (isPullback_baseChangeProjection ℂ Γ[U]).hom_ext
  · rw [Category.assoc, hv₁, projectiveLineTorusProductToAffine_fst,
      Category.assoc, overlapRestriction, baseChangeProjection_comp, overlapToSite_fst]
  · rw [Category.assoc, hv₂, projectiveLineTorusProductToAffine_snd_assoc, Category.assoc,
      overlapRestriction, (isPullback_baseChangeProjection Γ[U] Γ[V]).w, overlapToSite_snd_assoc,
      RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
    apply congrArg (pullback.snd p t ≫ ·)
    apply (cancel_mono ι[U]).mp
    simp only [Category.assoc, ha, projectiveLineTorusToAffineFan_algebraicMap_comp_ι,
      restrictionMap, U.property.map_fromSpec (V).property]
    rw [laurentSiteMap_comp_fromSpec, Iso.hom_inv_id_assoc]

end Restriction

/-- In the Cartesian product charts over the two toric affine opens of the base,
the projectivization of `𝒪(a) ⊞ 𝒪(b)` has the Hirzebruch transition of parameter
`b - a`. The comparisons `v` preserve the projective-line and base projections,
and the split twisting chart uses the standard frame on each affine open. -/
theorem split_twisting_product_chart_overlap (a b : ℤ)
    (U : Fin 2 → (P).AffineZariskiSite) (hU : ∀ k, (U k).toOpens = B[k])
    (f : ∀ k, A[k] ⟶ Spec (.of Γ(P, (U k).toOpens)))
    (hf : ∀ k, f k ≫ (U k).property.fromSpec = j[k])
    (v : ∀ k, H[k] ⟶ projectiveLine Γ(P, (U k).toOpens))
    (hv₁ : ∀ k,
      let := (Spec.preimage ((U k).property.fromSpec ≫ p)).hom.toAlgebra
      v k ≫ baseChangeProjection ℂ Γ(P, (U k).toOpens) = pullback.fst p s[k])
    (hv₂ : ∀ k,
      v k ≫ (projectiveLine Γ(P, (U k).toOpens) ↘ Spec (.of Γ(P, (U k).toOpens))) =
        pullback.snd p s[k] ≫ f k) :
    let u k := v k ≫ relativeProjSplitTwistingChart ℂ a b k (U k) (hU k).le
    d[0] ≫ u 0 = (hirzebruchRulingOverlapTransition (b - a)).hom ≫ d[1] ≫ u 1 := by
  let jVU (k : Fin 2) : V ⟶ U k := homOfLE (by
    let x : Γ(P, (U k).toOpens) := (hU k).symm ▸ affineCoordinate ℂ k
    refine ⟨x, ?_⟩
    have hx (W : (P).Opens) (h : W = B[k]) :
        (P).basicOpen (h.symm ▸ affineCoordinate ℂ k : Γ(P, W)) = (V).toOpens := by
      subst W
      rw [basicOpen_affineCoordinate, Proj.basicOpen_mul, torusSite_toOpens]
    exact hx _ (hU k))
  have hj (k : Fin 2) := torusProductToAffine_comp_splitChart (U k)
    (Scheme.AffineZariskiSite.toOpens_mono (jVU k).le) k
    (f k) (hf k) (v k) (hv₁ k) (hv₂ k)
  dsimp only
  simp only [← Category.assoc, hj]
  simp only [Category.assoc]
  have h := relativeProjSplitTwistingChart_overlap ℂ a b (jVU 0) (jVU 1)
    (hU 0).le (hU 1).le
  have ho (k : Fin 2) := Scheme.AffineZariskiSite.toOpens_mono (jVU k).le
  have hsplit :
      overlapRestriction (U 0) (ho 0) ≫ relativeProjSplitTwistingChart ℂ a b 0 (U 0) (hU 0).le =
        (scalingBy Γ[V] (affineCoordinateUnit ℂ (torusSite_le 0) (torusSite_le 1) ^ (a - b))).hom ≫
          overlapRestriction (U 1) (ho 1) ≫
            relativeProjSplitTwistingChart ℂ a b 1 (U 1) (hU 1).le := h
  rw [hsplit, ← overlapToSite_comp_scaling_assoc, neg_sub]

end TauCeti.Toric.Fan

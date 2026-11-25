/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import QPainleve.Geometry.Toric.Fan.Boundary.Prime
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Blowdown
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Canonical
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.ExceptionalCurve
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryPrimes
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.Geometrically.Connected
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import QPainleve.Geometry.Toric.Fan.Boundary.Canonical
import QPainleve.Geometry.Toric.Fan.Boundary.InternalBlowup
import QPainleve.Geometry.Toric.Fan.Boundary.Prestable
import QPainleve.Geometry.Toric.Fan.Logarithmic.InternalBlowup
import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Boundary
import QPainleve.Geometry.Toric.Fan.Rationality
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Nodal contraction towers after moving internal centers

Transport a specified nodal contraction of an ordered toric presentation to another
choice of its internal centers. The marked Picard comparison on partially contracted
models recognizes the next exceptional prime. At each step the two contractions
remove the same ray, so the final models retain precisely the same boundary rays.

The Picard comparison uses `exists_picardIsometry_of_same_survivingRays`. The
contraction step uses the numerical exceptional-curve criterion and Castelnuovo
contraction through `Scheme.IdealSheafData.IsEffectiveCartier.exists_nodal_boundary_blowdown`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower TopologicalSpace
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData LineBundleClass

namespace TauCeti.Toric.Fan

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "K[" X "]" => LineBundleClass.mk (canonicalBundle ℂ X 2)
local notation "I[" p "]" =>
  vanishingIdeal (Closeds.mk (closure (Singleton.singleton p)) isClosed_closure)
local notation "singleTower[" p "]" => BlowupTower.nil.snoc (I[p])

private structure NodalAnticanonicalSurface where
  surface : Scheme
  over : surface.Over S
  integral : IsIntegral surface
  projective : surface.IsProjectiveOver ℂ
  smooth : SmoothOfRelativeDimension 2 (CategoryTheory.over surface S over)
  rational : Scheme.IsRationalOver (CategoryTheory.over surface S over)
  boundary : surface.IdealSheafData
  cartier : boundary.IsEffectiveCartier
  nodal : AtWorstNodalOfRelativeDimensionOne
    (boundary.subschemeι ≫ CategoryTheory.over surface S over)
  canonical : LineBundleClass.mk cartier.toInvertibleSheaf =
    LineBundleClass.mk (@canonicalBundle ℂ _ surface over 2 smooth)

attribute [local instance] NodalAnticanonicalSurface.over NodalAnticanonicalSurface.integral
  NodalAnticanonicalSurface.projective NodalAnticanonicalSurface.smooth
  NodalAnticanonicalSurface.rational

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  (b : Basis (Fin 2) ℤ N) {r : ℕ} (s : Fin r → Φ.Ray) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)

local notation "Z" => Φ.algebraicRealization
local notation "Model[" c "]" => internalBlowupTower b s c
local notation "Y[" c "]" => (Model[c]).1
local notation "B[" c "]" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd (Model[c])))
local notation "base[" c "]" =>
  toBase (WithBoundary.toTower (Sigma.snd (Model[c]))) ≫ Φ.algebraicRealizationStructureMap
local notation "prime[" c "," ρ "]" => internalBlowupBoundaryPrimeEquiv hΦ b s c ρ
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)

private structure CenterContraction (c : Fin r → ℂˣ) (m : ℕ)
    (A : NodalAnticanonicalSurface) where
  top : Scheme
  tower : BlowupTower A.surface m top
  nodal : IsNodalBoundaryTower A.boundary (A.surface ↘ S) (𝟙 A.surface) tower
  iso : Y[c] ≅ top
  over : iso.hom ≫ tower.toBase ≫ (A.surface ↘ S) = base[c]
  support : (A.boundary.comap (iso.hom ≫ tower.toBase)).support = (B[c]).support

variable {b s} in
private abbrev CenterContraction.projection {c : Fin r → ℂˣ} {m : ℕ}
    {A : NodalAnticanonicalSurface} (P : CenterContraction b s c m A) :
    Y[c] ⟶ A.surface := P.iso.hom ≫ P.tower.toBase

include hc in
private def centerSurface (c : Fin r → ℂˣ) : NodalAnticanonicalSurface := by
  let : SmoothOfRelativeDimension 2 Φ.algebraicRealizationStructureMap :=
      (rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ)
  let : (Z).IsProjectiveOver ℂ := Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
  let : SmoothOfRelativeDimension 2 (Z ↘ S) :=
    (algebraicRealization_over Φ).symm ▸ inferInstance
  let : Y[c].Over S := ⟨(WithBoundary.toTower (Sigma.snd (Model[c]))).toBase ≫ Z ↘ S⟩
  let hT := isClosedPointTower_internalBlowupTower b s c
  let : SmoothOfRelativeDimension 2 (Y[c] ↘ S) := hT.smoothOfRelativeDimension (Z ↘ S)
  let : Scheme.IsRationalOver (Z ↘ S) := Φ.isRationalOver_of_isComplete hΦ hc b
  let hBase := Φ.isEffectiveCartier_boundaryIdeal hΦ hc rankTwo
  let hB := isEffectiveCartier_internalBlowupBoundary b s hΦ c hBase
  exact
    { surface := Y[c]
      over := inferInstance
      integral := isIntegral_internalBlowupTower b s c hΦ
      projective := (WithBoundary.toTower (Sigma.snd (Model[c]))).isProjectiveOver ℂ
      smooth := inferInstance
      rational := hT.isRationalOver (Z ↘ S)
      boundary := B[c]
      cartier := hB
      nodal := atWorstNodalOfRelativeDimensionOne_internalBlowupBoundary b s hΦ hc c
      canonical := canonicalClass_internalBlowupTower b s c hΦ hBase hB
        (Φ.canonicalClass_boundaryIdeal hΦ hc b hBase) }

private theorem exists_prepend {c : Fin r → ℂˣ} {m n : ℕ}
    {A C : NodalAnticanonicalSurface} (P : CenterContraction b s c m A)
    {W : Scheme} {U : BlowupTower C.surface n W}
    (hU : IsNodalBoundaryTower C.boundary (C.surface ↘ S) (𝟙 C.surface) U)
    (a : A.surface ≅ W) {f : A.surface ⟶ C.surface} (ha : a.hom ≫ U.toBase = f)
    (hover : f ≫ (C.surface ↘ S) = A.surface ↘ S)
    (hs : (C.boundary.comap f).support = A.boundary.support) :
    ∃ P' : CenterContraction b s c (n + m) C, P'.projection = P.projection ≫ f := by
  obtain ⟨W', T, e, hT, hbase, hbound⟩ := hU.exists_append_of_iso P.nodal a.symm
    (by rw [Iso.symm_hom, ← hover, ← ha, Category.assoc, Iso.inv_hom_id_assoc])
    (by rw [Iso.symm_hom, support_comap, ← hs, ← support_comap, ← comap_comp, ← ha,
      Iso.inv_hom_id_assoc])
  have hproj : (P.iso ≪≫ e.symm).hom ≫ T.toBase = P.projection ≫ f := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hbase, Iso.inv_hom_id_assoc,
      Iso.symm_inv, ha, CenterContraction.projection]
  refine ⟨⟨W', T, hT, P.iso ≪≫ e.symm, ?_, ?_⟩, hproj⟩
  · rw [← Category.assoc, hproj, Category.assoc, hover]
    exact P.over
  · rw [hproj, comap_comp, support_comap, hs, ← support_comap]
    exact P.support


private theorem map_canonical_of_boundaryPrimes {A B : NodalAnticanonicalSurface}
    (e : (Chow.intersectionBilinForm ℂ A.surface).IsometryEquiv
      (Chow.intersectionBilinForm ℂ B.surface))
    (q : A.boundary.boundaryPrimes ≃ B.boundary.boundaryPrimes)
    (hq :
      let : IsNoetherian A.surface := isNoetherian_of_finiteType (A.surface ↘ S)
      let : IsNoetherian B.surface := isNoetherian_of_finiteType (B.surface ↘ S)
      let := (A.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      let := (B.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      ∀ x, e (Additive.ofMul (primeDivisorClass ⟨x.val, (mem_boundaryPrimes.mp x.property).2⟩)) =
        Additive.ofMul (primeDivisorClass ⟨(q x).val, (mem_boundaryPrimes.mp (q x).property).2⟩)) :
    e (Additive.ofMul K[A.surface]) = Additive.ofMul K[B.surface] := by
  let : IsNoetherian A.surface := isNoetherian_of_finiteType (A.surface ↘ S)
  let : IsNoetherian B.surface := isNoetherian_of_finiteType (B.surface ↘ S)
  let : IsReduced A.boundary.subscheme := A.nodal.isReduced
  let : IsReduced B.boundary.subscheme := B.nodal.isReduced
  let := (A.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := (B.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hpoint {W : Scheme} {C : W.IdealSheafData} (z : C.boundaryPrimes) :
      C.boundaryPrimeEmbedding z = ⟨z.val, (mem_boundaryPrimes.mp z.property).2⟩ :=
    Subtype.ext (coe_boundaryPrimeEmbedding C z)
  have hK := A.cartier.map_ofMul_inv_toInvertibleSheaf_of_boundaryPrimes B.cartier
    e.toLinearEquiv.toLinearMap.toAddMonoidHom q (fun x ↦ by
      rw [hpoint (C := A.boundary) x, hpoint (C := B.boundary) (q x)]
      simpa only [LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
        LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv] using
        hq x)
  rw [A.canonical, B.canonical] at hK
  exact neg_injective (by simpa only [ofMul_inv, map_neg, LinearMap.toAddMonoidHom_coe,
      LinearEquiv.coe_coe, LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv] using hK)

include hc in
private theorem isExceptional_of_survivingRay {c d : Fin r → ℂˣ} {m n : ℕ}
    {A B : NodalAnticanonicalSurface}
    (P : CenterContraction b s c m A) (U : CenterContraction b s d n B)
    (hmatch : ∀ ρ, P.projection (prime[c,ρ]).val ∈ A.boundary.boundaryPrimes ↔
      U.projection (prime[d,ρ]).val ∈ B.boundary.boundaryPrimes)
    (ρ : Φ.Ray) (hρ : P.projection (prime[c,ρ]).val ∈ A.boundary.boundaryPrimes)
    (hE : (I[P.projection (prime[c,ρ]).val]).IsExceptionalCurveOfFirstKind) :
    (I[U.projection (prime[d,ρ]).val]).IsExceptionalCurveOfFirstKind := by
  let : (Z).IsProjectiveOver ℂ := Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
  let : IsNoetherian A.surface := isNoetherian_of_finiteType (A.surface ↘ S)
  let : IsNoetherian B.surface := isNoetherian_of_finiteType (B.surface ↘ S)
  let := (A.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := (B.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let : IsNormalScheme A.surface := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  let : IsNormalScheme B.surface := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  let := isModification_orderedContraction hΦ b s c P.nodal P.iso
  let := isModification_orderedContraction hΦ b s d U.nodal U.iso
  let j := contractedBoundaryRayEmbedding hΦ b s c P.projection P.support
  let k := contractedBoundaryRayEmbedding hΦ b s d U.projection U.support
  have hR : Set.range j = Set.range k := Set.ext fun ρ ↦
    (mem_range_contractedBoundaryRayEmbedding_iff hΦ b s c P.projection P.support ρ).trans
      ((hmatch ρ).trans
        (mem_range_contractedBoundaryRayEmbedding_iff hΦ b s d U.projection U.support ρ).symm)
  obtain ⟨e, he⟩ := exists_picardIsometry_of_same_survivingRays hΦ b s c P.nodal P.iso P.over
    P.support d U.nodal U.iso U.over U.support hR
  let q := (Equiv.ofInjective j j.injective).trans
    ((Set.equivOfEq hR).trans (Equiv.ofInjective k k.injective).symm)
  have hq (x : A.boundary.boundaryPrimes) : j x = k (q x) :=
    (congrArg Subtype.val ((Equiv.ofInjective k k.injective).apply_symm_apply
      ((Set.equivOfEq hR) (Equiv.ofInjective j j.injective x)))).symm
  have hk := map_canonical_of_boundaryPrimes e q (fun x ↦ he x (q x) (hq x))
  let x : A.boundary.boundaryPrimes := ⟨_, hρ⟩
  let y : B.boundary.boundaryPrimes := ⟨_, (hmatch ρ).mp hρ⟩
  have hx := (contractedBoundaryRayEmbedding_eq_iff hΦ b s c P.projection P.support x ρ).mpr rfl
  have hy := (contractedBoundaryRayEmbedding_eq_iff hΦ b s d U.projection U.support y ρ).mpr rfl
  let x' : CodimensionOnePoint A.surface := ⟨x.val, (mem_boundaryPrimes.mp x.property).2⟩
  let y' : CodimensionOnePoint B.surface := ⟨y.val, (mem_boundaryPrimes.mp y.property).2⟩
  have hxy : e (Additive.ofMul (primeDivisorClass x')) = Additive.ofMul (primeDivisorClass y') :=
    he x y (hx.trans hy.symm)
  have hmap (a z : Additive (LineBundleClass A.surface)) :
      Chow.classIntersectionNumber ℂ B.surface (e a).toMul (e z).toMul =
        Chow.classIntersectionNumber ℂ A.surface a.toMul z.toMul :=
    (Chow.intersectionBilinForm_apply ℂ B.surface (e a) (e z)).symm.trans
      ((e.map_app z a).trans (Chow.intersectionBilinForm_apply ℂ A.surface a z))
  exact (Chow.isExceptionalCurveOfFirstKind_iff_primeDivisorClass ℂ y').mpr (by
    have hin := (Chow.isExceptionalCurveOfFirstKind_iff_primeDivisorClass ℂ x').mp hE
    let a := Additive.ofMul (primeDivisorClass x')
    simpa only [a, hxy, hk, toMul_ofMul] using
      And.intro ((hmap a a).trans hin.1) ((hmap a (Additive.ofMul K[A.surface])).trans hin.2))

private theorem projectsTo_boundaryPrime_iff
    {A C : NodalAnticanonicalSurface} {f : A.surface ⟶ C.surface} {p : C.surface}
    (hp : IsClosed ({p} : Set C.surface))
    (hiso : ∀ z : C.surface, z ≠ p → z ∈ f.isoLocus)
    (hB : (C.boundary.comap f).support = A.boundary.support) (x : A.surface) :
    f x ∈ C.boundary.boundaryPrimes ↔ x ∈ A.boundary.boundaryPrimes ∧ f x ≠ p := by
  by_cases hx : f x = p
  · have h := coheight_eq_of_isClosed_of_smoothOfRelativeDimension (n := 2) (C.surface ↘ S) hp
    simp only [hx, mem_boundaryPrimes, h, (by decide : ((2 : ℕ) : ℕ∞) ≠ 1),
      and_false, ne_eq, not_true_eq_false]
  · rw [and_iff_left hx, mem_boundaryPrimes, mem_boundaryPrimes,
      ← f.coheight_eq_of_apply_mem_isoLocus (hiso _ hx), ← hB, support_comap]
    rfl

private theorem exists_prepend_exceptional_blowdown {c : Fin r → ℂˣ} {m : ℕ}
    {A : NodalAnticanonicalSurface} (P : CenterContraction b s c m A)
    (ρ : Φ.Ray) (hρ : P.projection (prime[c,ρ]).val ∈ A.boundary.boundaryPrimes)
    (hE : (I[P.projection (prime[c,ρ]).val]).IsExceptionalCurveOfFirstKind) :
    ∃ (C : NodalAnticanonicalSurface) (P' : CenterContraction b s c (1 + m) C),
      ∀ τ, P'.projection (prime[c,τ]).val ∈ C.boundary.boundaryPrimes ↔
        P.projection (prime[c,τ]).val ∈ A.boundary.boundaryPrimes ∧ τ ≠ ρ := by
  let x := P.projection (prime[c,ρ]).val
  have hEsub : (I[x]).support ≤ A.boundary.support := by
    rw [← SetLike.coe_subset_coe, coe_support_vanishingIdeal, Closeds.coe_mk]
    exact A.boundary.support.isClosed.closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr (mem_boundaryPrimes.mp hρ).1)
  obtain ⟨Y, t, f, p, hY, hP, hS, hover, hmod, hp, hcenter, hExc, e, he, hC, hK, hn,
    hT, hred, -⟩ := A.cartier.exists_nodal_boundary_blowdown A.nodal A.canonical hE hEsub
  let : Y.Over S := ⟨t⟩
  let : IsModification f := hmod
  let : f.IsOver S := hover
  obtain ⟨v, hv⟩ := IsModification.birationalOver f
  have hft : f ≫ t = A.surface ↘ S := comp_over f S
  have hBir : Scheme.BirationalOver (A.surface ↘ S) t := ⟨v, by
    simpa only [Scheme.PartialIso.IsOver, Category.assoc, Category.comp_id, hft] using
      congrArg (· ≫ t) hv⟩
  let C : NodalAnticanonicalSurface := ⟨Y, ⟨t⟩, hY, hP, hS,
    hBir.symm.isRationalOver _ _, A.boundary.map f, hC, hn, hK⟩
  have hs : (C.boundary.comap f).support = A.boundary.support :=
    (support_radical _).symm.trans (congrArg (fun D : A.surface.IdealSheafData ↦ D.support) hred)
  obtain ⟨P', hproj⟩ := exists_prepend b s P hT e he (comp_over f S) hs
  have hiso (z : Y) (hz : z ≠ p) : z ∈ f.isoLocus := by
    rw [← SetLike.mem_coe, ← Scheme.Hom.compl_centre, hcenter, Set.mem_compl_iff]
    exact hz
  refine ⟨C, P', fun τ ↦ ?_⟩
  rw [hproj, Scheme.Hom.comp_apply, projectsTo_boundaryPrime_iff hp hiso hs]
  refine and_congr_right fun hτ ↦ not_congr ?_
  have hmem : f (P.projection (prime[c,τ]).val) = p ↔
      P.projection (prime[c,τ]).val ∈ (I[x]).support := by
    rw [← hExc, ← SetLike.mem_coe, support_comap, Closeds.coe_preimage, coe_support_vanishingIdeal,
      Closeds.coe_mk, hp.closure_eq, Set.mem_preimage, Set.mem_singleton_iff]
  rw [hmem, ← SetLike.mem_coe, coe_support_vanishingIdeal, Closeds.coe_mk]
  refine ⟨fun ht ↦ ?_, fun h ↦ h ▸ subset_closure (Set.mem_singleton _)⟩
  have hsame := CodimensionOnePoint.eq_of_specializes
    (x := A.boundary.boundaryPrimeEmbedding ⟨_, hτ⟩)
    (y := A.boundary.boundaryPrimeEmbedding ⟨_, hρ⟩)
    (specializes_iff_mem_closure.mpr
      (by simpa only [coe_boundaryPrimeEmbedding] using ht))
  have hpoint : P.projection (prime[c,ρ]).val = P.projection (prime[c,τ]).val :=
    by simpa only [coe_boundaryPrimeEmbedding] using
      congrArg (fun z : CodimensionOnePoint A.surface ↦ z.val) hsame
  let : IsNoetherian A.surface := isNoetherian_of_finiteType (A.surface ↘ S)
  let := (A.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let : IsNormalScheme A.surface := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  let := isModification_orderedContraction hΦ b s c P.nodal P.iso
  let z : A.boundary.boundaryPrimes := ⟨_, hρ⟩
  have hτ' := (contractedBoundaryRayEmbedding_eq_iff hΦ b s c P.projection P.support z τ).mpr
    hpoint.symm
  exact hτ'.symm.trans
    ((contractedBoundaryRayEmbedding_eq_iff hΦ b s c P.projection P.support z ρ).mpr rfl)

private abbrev prefixSurface (A : NodalAnticanonicalSurface) {m : ℕ} {Y : Scheme}
    {T : BlowupTower A.surface m Y}
    (hT : IsNodalBoundaryTower A.boundary (A.surface ↘ S) (𝟙 A.surface) T) :
    NodalAnticanonicalSurface := by
  let : IsNoetherian A.surface := isNoetherian_of_finiteType (A.surface ↘ S)
  let h := hT.radical_comap_toBase A.cartier A.nodal
  exact
    { surface := Y
      over := ⟨T.toBase ≫ A.surface ↘ S⟩
      integral := hT.isClosedPointTower.isIntegral (A.surface ↘ S)
      projective := T.isProjectiveOver ℂ
      smooth := hT.isClosedPointTower.smoothOfRelativeDimension (A.surface ↘ S)
      rational := hT.isClosedPointTower.isRationalOver (A.surface ↘ S)
      boundary := (A.boundary.comap T.toBase).radical
      cartier := h.1
      nodal := h.2
      canonical := (hT.canonicalClass_radical_comap_toBase_iff A.cartier A.nodal).mpr A.canonical }

private abbrev extendPrefix {A : NodalAnticanonicalSurface} {l : ℕ} {Y : Scheme}
    {T : BlowupTower A.surface l Y}
    (hT : IsNodalBoundaryTower A.boundary (A.surface ↘ S) (𝟙 A.surface) T)
    {p : Y} (hp : IsClosed ({p} : Set Y))
    (hn : (A.boundary.comap (T.toBase ≫ 𝟙 A.surface)).IsNodeOfReducedBoundary
      ((T.toBase ≫ 𝟙 A.surface) ≫ (A.surface ↘ S)) p) :=
  hT.snoc p hp (I := (Y.fromSpecResidueField p).ker) rfl hn

private theorem exists_prepend_last_step {c : Fin r → ℂˣ} {l m : ℕ}
    {A : NodalAnticanonicalSurface} {Y : Scheme} {T : BlowupTower A.surface l Y}
    (hT : IsNodalBoundaryTower A.boundary (A.surface ↘ S) (𝟙 A.surface) T)
    {p : Y} (hp : IsClosed ({p} : Set Y))
    (hn : (A.boundary.comap (T.toBase ≫ 𝟙 A.surface)).IsNodeOfReducedBoundary
      ((T.toBase ≫ 𝟙 A.surface) ≫ (A.surface ↘ S)) p)
    (P : CenterContraction b s c m (prefixSurface A (extendPrefix hT hp hn))) :
    ∃ P' : CenterContraction b s c (1 + m) (prefixSurface A hT),
      P'.projection = P.projection ≫ (Y.fromSpecResidueField p).ker.blowupToBase := by
  let C₀ := prefixSurface A hT
  let C₁ := prefixSurface A (extendPrefix hT hp hn)
  let : C₀.surface.Over S := C₀.over
  let : C₁.surface.Over S := C₁.over
  let J := (Y.fromSpecResidueField p).ker
  let f := J.blowupToBase
  have hs₁ : C₁.surface ↘ S = (T.snoc J).toBase ≫ A.surface ↘ S := rfl
  have hcomp : f ≫ (C₀.surface ↘ S) = C₁.surface ↘ S := by
    rw [hs₁, toBase_snoc, Category.assoc]
    rfl
  have hs : (C₀.boundary.comap f).support = C₁.boundary.support := by
    simp only [C₀, C₁, prefixSurface, toBase_snoc, f, support_comap,
      support_radical, comap_comp]
  have hpnode : C₀.boundary.IsNodeOfReducedBoundary (C₀.surface ↘ S) p := by
    have hs₀ : C₀.surface ↘ S = T.toBase ≫ A.surface ↘ S := rfl
    rw [hs₀]
    simpa only [C₀, prefixSurface, isNodeOfReducedBoundary_radical, Category.comp_id] using hn
  have hU : IsNodalBoundaryTower C₀.boundary (C₀.surface ↘ S) (𝟙 C₀.surface)
      (BlowupTower.nil.snoc J) := by
    refine .snoc .nil p hp rfl ?_
    rwa [toBase_nil, Category.id_comp, comap_id, Category.id_comp]
  have hstep : (Iso.refl C₁.surface).hom ≫ (BlowupTower.nil.snoc J).toBase = f := by
    simp [f, toBase_snoc, toBase_nil]
  simpa only [Nat.zero_add] using exists_prepend b s P hU (Iso.refl C₁.surface) hstep hcomp hs

private theorem exists_prepend_source_blowdown {c : Fin r → ℂˣ} {l m : ℕ}
    {A : NodalAnticanonicalSurface} {Y : Scheme} {T : BlowupTower A.surface l Y}
    (hT : IsNodalBoundaryTower A.boundary (A.surface ↘ S) (𝟙 A.surface) T)
    {p : Y} (hp : IsClosed ({p} : Set Y))
    (hn : (A.boundary.comap (T.toBase ≫ 𝟙 A.surface)).IsNodeOfReducedBoundary
      ((T.toBase ≫ 𝟙 A.surface) ≫ (A.surface ↘ S)) p)
    (P : CenterContraction b s c m (prefixSurface A (extendPrefix hT hp hn))) :
    ∃ (ρ : Φ.Ray) (P' : CenterContraction b s c (1 + m) (prefixSurface A hT)),
      P'.projection = P.projection ≫ (Y.fromSpecResidueField p).ker.blowupToBase ∧
      P.projection (prime[c,ρ]).val ∈
          (prefixSurface A (extendPrefix hT hp hn)).boundary.boundaryPrimes ∧
      (I[P.projection (prime[c,ρ]).val]).IsExceptionalCurveOfFirstKind ∧
      ∀ τ, P'.projection (prime[c,τ]).val ∈ (prefixSurface A hT).boundary.boundaryPrimes ↔
        P.projection (prime[c,τ]).val ∈
          (prefixSurface A (extendPrefix hT hp hn)).boundary.boundaryPrimes ∧ τ ≠ ρ := by
  let C₀ := prefixSurface A hT
  let C₁ := prefixSurface A (extendPrefix hT hp hn)
  let : C₀.surface.Over S := C₀.over
  let : C₁.surface.Over S := C₁.over
  let J := (Y.fromSpecResidueField p).ker
  let f := J.blowupToBase
  let : SmoothOfRelativeDimension 2 (C₀.surface ↘ S) := C₀.smooth
  let : SmoothOfRelativeDimension 2 (C₁.surface ↘ S) := C₁.smooth
  let : IsIntegral C₁.surface := C₁.integral
  let : C₁.surface.IsProjectiveOver ℂ := C₁.projective
  have hs : (C₀.boundary.comap f).support = C₁.boundary.support := by
    simp only [C₀, C₁, prefixSurface, toBase_snoc, f, support_comap,
      support_radical, comap_comp]
  have hpnode : C₀.boundary.IsNodeOfReducedBoundary (C₀.surface ↘ S) p := by
    have hs₀ : C₀.surface ↘ S = T.toBase ≫ A.surface ↘ S := rfl
    rw [hs₀]
    simpa only [C₀, prefixSurface, isNodeOfReducedBoundary_radical, Category.comp_id] using hn
  obtain ⟨P', hproj⟩ := exists_prepend_last_step b s hT hp hn P
  -- Locate the exceptional prime of the specified last blowup in the fixed fan.
  let : IsNoetherian C₀.surface := isNoetherian_of_finiteType (C₀.surface ↘ S)
  let : IsNoetherian C₁.surface := isNoetherian_of_finiteType (C₁.surface ↘ S)
  let : Smooth (C₀.surface ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let := isRegularLocalRing_stalk_of_smooth (C₀.surface ↘ S) p
  let := (C₁.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let : IsNormalScheme C₁.surface := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  let := isModification_orderedContraction hΦ b s c P.nodal P.iso
  have hd := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (C₀.surface ↘ S) 2).mp
    inferInstance).2 p hp
  have hexc := isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hd
  let : IsIntegral (J.comap f).subscheme := hexc.isIntegral_subscheme
  have hJ : (J.support : Set Y) = {p} :=
    Y.support_ker_fromSpecResidueField_of_isClosed hp
  have hmem (z : C₁.surface) : z ∈ (J.comap f).support ↔ f z = p := by
    rw [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage, hJ,
      Set.mem_singleton_iff]
  let η := (J.comap f).subschemeι (genericPoint (J.comap f).subscheme)
  have hη : η ∈ (J.comap f).support := by
    rw [← SetLike.mem_coe, ← (J.comap f).range_subschemeι]
    exact Set.mem_range_self _
  have hηD : η ∈ C₁.boundary.boundaryPrimes := by
    refine mem_boundaryPrimes.mpr ⟨?_, hexc.isEffectiveCartier.coheight_subschemeι_genericPoint⟩
    rw [← hs, ← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage,
      (hmem η).mp hη]
    exact mem_support_of_isNodeOfReducedBoundary hpnode
  let x : C₁.boundary.boundaryPrimes := ⟨η, hηD⟩
  let ρ := contractedBoundaryRayEmbedding hΦ b s c P.projection P.support x
  have hx : P.projection (prime[c,ρ]).val = η :=
    contraction_internalBlowupBoundaryPrimeEquiv hΦ b s c P.projection P.support x
  -- Away from that closed center, codimension-one points survive the projection.
  have hiso (z : Y) (hz : z ≠ p) : z ∈ f.isoLocus :=
    (f.le_isoLocus_iff.mpr J.isIso_blowupToBase_restrict_compl_support)
      (by simpa only [← SetLike.mem_coe, Closeds.coe_compl, hJ, Set.mem_compl_iff,
        Set.mem_singleton_iff] using hz)
  refine ⟨ρ, P', hproj, hx.symm ▸ hηD, ?_, fun τ ↦ ?_⟩
  · rw [hx, (J.comap f).vanishingIdeal_closure_subschemeι_genericPoint]
    exact hexc
  · rw [hproj, Scheme.Hom.comp_apply, projectsTo_boundaryPrime_iff (A := C₁) (C := C₀) hp hiso hs]
    refine and_congr_right fun hτ ↦ not_congr ?_
    rw [← hmem, hexc.isEffectiveCartier.mem_support_iff_eq_subschemeι_genericPoint
      (mem_boundaryPrimes.mp hτ).2]
    exact (contractedBoundaryRayEmbedding_eq_iff hΦ b s c P.projection P.support x τ).symm.trans
      eq_comm

include hc in
private theorem exists_matching_contractionAux {c d : Fin r → ℂˣ}
    (A : NodalAnticanonicalSurface) {l : ℕ} {Y : Scheme} {T : BlowupTower A.surface l Y}
    (hT : IsNodalBoundaryTower A.boundary (A.surface ↘ S) (𝟙 A.surface) T) :
    ∀ {m : ℕ} {B : NodalAnticanonicalSurface}
      (P : CenterContraction b s c m (prefixSurface A hT))
      (U : CenterContraction b s d m B),
      (∀ ρ, P.projection (prime[c,ρ]).val ∈ (prefixSurface A hT).boundary.boundaryPrimes ↔
        U.projection (prime[d,ρ]).val ∈ B.boundary.boundaryPrimes) →
      ∃ (C : NodalAnticanonicalSurface) (U' : CenterContraction b s d (l + m) C),
        ∀ ρ, (P.projection ≫ T.toBase) (prime[c,ρ]).val ∈ A.boundary.boundaryPrimes ↔
          U'.projection (prime[d,ρ]).val ∈ C.boundary.boundaryPrimes := by
  induction hT with
  | nil =>
    intro m B P U hmatch
    have hred : A.boundary.radical = A.boundary :=
      A.boundary.isReduced_subscheme_iff_radical_eq.mp A.nodal.isReduced
    rw [Nat.zero_add]
    refine ⟨B, U, fun ρ ↦ ?_⟩
    simpa only [prefixSurface, toBase_nil, Category.comp_id, comap_id, hred] using hmatch ρ
  | @snoc l Y T J hT p hp hJ hn ih =>
    subst J
    intro m B P U hmatch
    obtain ⟨ρ, P', hproj, hρ, hexc, hP'⟩ :=
      exists_prepend_source_blowdown b s hΦ hT hp hn P
    have hE := isExceptional_of_survivingRay b s hΦ hc P U hmatch ρ hρ hexc
    obtain ⟨C, U', hU'⟩ :=
      exists_prepend_exceptional_blowdown b s hΦ U ρ ((hmatch ρ).mp hρ) hE
    have hmatch' (τ : Φ.Ray) := (hP' τ).trans
      ((and_congr_left fun _ ↦ hmatch τ).trans (hU' τ).symm)
    rw [Nat.add_assoc]
    obtain ⟨E, W, hW⟩ := ih P' U' hmatch'
    exact ⟨E, W, fun τ ↦ by
      have hh := hW τ
      rw [hproj, Category.assoc] at hh
      simpa only [toBase_snoc] using hh⟩


private theorem exists_nilContraction (c : Fin r → ℂˣ) (A : NodalAnticanonicalSurface)
    (e : Y[c] ≅ A.surface) (he : e.hom ≫ (A.surface ↘ S) = base[c])
    (hs : (A.boundary.comap e.hom).support = (B[c]).support) :
    ∃ P : CenterContraction b s c 0 A, P.projection = e.hom ∧
      ∀ ρ, P.projection (prime[c,ρ]).val ∈ A.boundary.boundaryPrimes := by
  let T : BlowupTower A.surface 0 A.surface := .nil
  have hproj : e.hom ≫ T.toBase = e.hom := by simp only [T, toBase_nil, Category.comp_id]
  let P : CenterContraction b s c 0 A := ⟨_, T, .nil, e,
    by rw [← Category.assoc, hproj, he], by rw [hproj, hs]⟩
  have hP : P.projection = e.hom := hproj
  refine ⟨P, hP, fun ρ ↦ ?_⟩
  rw [hP, mem_boundaryPrimes, coheight_eq_of_isOpenImmersion e.hom]
  have hp := mem_boundaryPrimes.mp (prime[c,ρ]).property
  rw [← hs, support_comap] at hp
  exact hp

include hΦ hc in
private theorem prestableFamily_contractedBoundary {d : Fin r → ℂˣ} {m : ℕ}
    {C : NodalAnticanonicalSurface} (W : CenterContraction b s d m C) :
    PrestableFamily (C.boundary.subscheme ↘ S) := by
  let j := WithBoundary.boundaryι (Sigma.snd (Model[d]))
  let E := Φ.boundaryIdeal ‹Nonempty Φ.cones›
  have : GeometricallyConnected (E.subschemeι ≫ Φ.algebraicRealizationStructureMap) :=
    Φ.geometricallyConnected_boundary hΦ hc rankTwo
  have : ConnectedSpace E.subscheme :=
    GeometricallyConnected.connectedSpace_of_subsingleton (E.subschemeι ≫
      Φ.algebraicRealizationStructureMap)
  have hconn : _root_.IsConnected ((B[d]).support : Set Y[d]) := by
    rw [Scheme.Hom.support_ker]
    exact (isConnected_range j.continuous).closure
  let : IsModification W.projection := isModification_orderedContraction hΦ b s d W.nodal W.iso
  have himage : W.projection '' ((B[d]).support : Set Y[d]) = C.boundary.support := by
    rw [← W.support, support_comap, Closeds.coe_preimage]
    exact Set.image_preimage_eq _ W.projection.surjective
  have hbase : _root_.IsConnected (C.boundary.support : Set C.surface) := by
    rw [← himage]
    exact hconn.image _ W.projection.continuous.continuousOn
  let : ConnectedSpace C.boundary.subscheme :=
    C.boundary.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.connectedSpace_iff.mpr
      (isConnected_iff_connectedSpace.mp (C.boundary.range_subschemeι.symm ▸ hbase))
  rw [C.boundary.over_eq_subschemeι_comp]
  exact {
    toIsProper := inferInstance
    toGeometricallyConnected := (GeometricallyConnected.iff_connectedSpace_of_isSepClosed _).mpr
      inferInstance
    atWorstNodalOfRelativeDimensionOne := C.nodal }

include hc in
/-- A specified nodal contraction of an ordered toric model can be repeated after
any change of its internal centers. The new surface is smooth, projective and
rational with a prestable anticanonical boundary. Its projection has a nodal tower of
the same length as the reference tower, its reduced total boundary is the strict
toric boundary, and exactly the same rays project to boundary primes. The internal
centers may repeat in either model. -/
theorem exists_nodal_contraction_of_same_surviving_rays
    (c d : Fin r → ℂˣ) {X Y : Scheme} [X.Over S] [X.IsProjectiveOver ℂ]
    [SmoothOfRelativeDimension 2 (X ↘ S)] [Scheme.IsRationalOver (X ↘ S)]
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hK : LineBundleClass.mk hD.toInvertibleSheaf = K[X])
    {m : ℕ} {T : BlowupTower X m Y} (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (e : Y[c] ≅ Y) (he : e.hom ≫ T.toBase ≫ (X ↘ S) = base[c])
    (hB : (D.comap (e.hom ≫ T.toBase)).support = (B[c]).support) :
    ∃ (X' Y' : Scheme) (t : X' ⟶ S) (D' : X'.IdealSheafData)
      (U : BlowupTower X' m Y') (f : Y[d] ≅ Y'),
      let : X'.Over S := ⟨t⟩
      ∃ (_ : IsIntegral X') (_ : X'.IsProjectiveOver ℂ) (_ : SmoothOfRelativeDimension 2 (X' ↘ S))
        (hD' : D'.IsEffectiveCartier),
        Scheme.IsRationalOver (X' ↘ S) ∧
        PrestableFamily (D'.subscheme ↘ S) ∧
        LineBundleClass.mk hD'.toInvertibleSheaf = K[X'] ∧
        IsNodalBoundaryTower D' (X' ↘ S) (𝟙 X') U ∧
        f.hom ≫ U.toBase ≫ (X' ↘ S) = base[d] ∧
        (D'.comap (f.hom ≫ U.toBase)).radical = B[d] ∧
        (∀ ρ, (e.hom ≫ T.toBase) (prime[c,ρ]).val ∈ D.boundaryPrimes ↔
          (f.hom ≫ U.toBase) (prime[d,ρ]).val ∈ D'.boundaryPrimes) := by
  let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsIntegral X := (inferInstance : Scheme.IsRationalOver (X ↘ S)).isIntegral_of_smooth
  let A : NodalAnticanonicalSurface :=
    ⟨X, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, D, hD, hN, hK⟩
  let A' := prefixSurface A hT
  let B := centerSurface b s hΦ hc d
  let : A'.surface.Over S := A'.over
  have he' : e.hom ≫ (A'.surface ↘ S) = base[c] := he
  have hB' : (A'.boundary.comap e.hom).support = (B[c]).support := by
    simpa only [A', prefixSurface, A, support_comap, support_radical, comap_comp] using hB
  obtain ⟨P, hP, hAll⟩ := exists_nilContraction b s hΦ c A' e he' hB'
  have hBstruct : B.surface ↘ S =
      (WithBoundary.toTower (Sigma.snd (Model[d]))).toBase ≫ Z ↘ S := rfl
  have hd : (Iso.refl B.surface).hom ≫ (B.surface ↘ S) = base[d] := by
    rw [Iso.refl_hom, Category.id_comp, hBstruct, algebraicRealization_over]
  have hBd : (B.boundary.comap (Iso.refl (Y[d])).hom).support = (B[d]).support := by
    simp only [B, centerSurface, Iso.refl_hom, comap_id]
  obtain ⟨U, -, hAll'⟩ := exists_nilContraction b s hΦ d B (Iso.refl _) hd hBd
  obtain ⟨C, W, hW⟩ := exists_matching_contractionAux b s hΦ hc A hT P U
    (fun ρ ↦ iff_of_true (hAll ρ) (hAll' ρ))
  have hred : (B[d]).radical = B[d] :=
    (B[d]).isReduced_subscheme_iff_radical_eq.mp
      (atWorstNodalOfRelativeDimensionOne_internalBlowupBoundary b s hΦ hc d).isReduced
  have htotal := congrArg vanishingIdeal W.support
  rw [vanishingIdeal_support, vanishingIdeal_support, hred] at htotal
  exact ⟨C.surface, W.top, C.surface ↘ S, C.boundary, W.tower, W.iso, C.integral, C.projective,
    C.smooth, C.cartier, C.rational, prestableFamily_contractedBoundary b s hΦ hc W,
    C.canonical, W.nodal, W.over, htotal,
    fun ρ ↦ by simpa only [hP] using hW ρ⟩
end TauCeti.Toric.Fan

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Complexity
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Contraction

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.Intersection
import QPainleve.AlgebraicGeometry.Blowup.Isomorphism
import QPainleve.AlgebraicGeometry.Blowup.Point.Picard
import QPainleve.AlgebraicGeometry.Blowup.Point.Projective
import QPainleve.AlgebraicGeometry.Blowup.Projective.Global
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.Chow.Isomorphism
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision
import QPainleve.Geometry.Toric.Fan.Smooth
import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic

/-!
# Toric models of boundary contractions

If a point blowup with center on the boundary has a toric reduced total boundary,
its exceptional curve is a toric ray divisor of square `-1`. Reversing the star
subdivision and descending along the actual exceptional class identifies the
specified blowdown with a toric morphism. Iteration descends a whole nodal tower.

In a specified toric presentation, boundary complexity counts the internal centers.
At complexity zero the auxiliary surface is toric, so the original pair is toric.
See R. Friedman, *On the geometry of anticanonical pairs*, Lemmas 1.2 and 2.2 for
the charge and its behavior under corner and interior blowups.
-/

public noncomputable section

open Module TopologicalSpace
open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry Scheme.IdealSheafData
open LineBundleClass QPainleve QPainleve.BlowupTower

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "s[" Δ "]" => algebraicRealizationStructureMap Δ
local notation "X[" Δ "]" => algebraicRealization Δ
local notation "f[" Δ "]" => (X[Δ] ↘ S)
local notation "I[" σ "]" => Scheme.Hom.ker (distinguishedPointHom _ σ)

/-- A smooth toric surface is projective if a common subdivision realizes its
distinguished point blowup and a distinguished point blowup of a projective toric surface. -/
theorem IsSubdivision.isProjectiveOver_of_common_pointBlowup {F Ψ : Fan i}
    [X[Φ].IsProjectiveOver ℂ] [Nonempty Ψ.cones]
    [SmoothOfRelativeDimension 2 f[Ψ]]
    (t : F.IsSubdivision Ψ) (s : F.IsSubdivision Φ) (σ : Φ.cones) (τ : Ψ.cones)
    (v : X[F] ≅ (I[σ]).blowup) (w : X[F] ≅ (I[τ]).blowup)
    (hv : v.hom ≫ (I[σ]).blowupToBase = s.toFanHom.algebraicMap)
    (hw : w.hom ≫ (I[τ]).blowupToBase = t.toFanHom.algebraicMap) :
    X[Ψ].IsProjectiveOver ℂ := by
  let : (I[σ]).blowup.Over S := ⟨(I[σ]).blowupToBase ≫ f[Φ]⟩
  let : (I[τ]).blowup.Over S := ⟨(I[τ]).blowupToBase ≫ f[Ψ]⟩
  let : v.hom.IsOver S := ⟨by
    -- The structure map on the blowup was chosen as the composite with its projection.
    change v.hom ≫ (I[σ]).blowupToBase ≫ f[Φ] = f[F]
    rw [← Category.assoc, hv, comp_over]⟩
  let : w.hom.IsOver S := ⟨by
    -- Use the structure map on the target blowup in the same form.
    change w.hom ≫ (I[τ]).blowupToBase ≫ f[Ψ] = f[F]
    rw [← Category.assoc, hw, comp_over]⟩
  let : (I[σ]).blowup.IsProjectiveOver ℂ := (I[σ]).isProjectiveOver_blowup_of_isNoetherianRing ℂ
  let : X[F].IsProjectiveOver ℂ := Scheme.IsProjectiveOver.of_isClosedImmersion ℂ v.hom
  have hprojective : (I[τ]).blowup.IsProjectiveOver ℂ :=
    Scheme.IsProjectiveOver.of_isClosedImmersion ℂ w.inv
  let p := Ψ.distinguishedPointHom τ (IsLocalRing.closedPoint ℂ)
  have hp := Ψ.isClosed_singleton_distinguishedPoint τ
  have hker := (Ψ.distinguishedPointHom τ).ker_eq_ker_fromSpecResidueField
  let : Smooth f[Ψ] := SmoothOfRelativeDimension.smooth 2 _
  have hnoeth : IsNoetherian X[Ψ] := isNoetherian_of_finiteType f[Ψ]
  apply Scheme.IsProjectiveOver.of_pointBlowup (k := ℂ) p hp
  exact (congrArg (fun J : X[Ψ].IdealSheafData ↦
    let : J.blowup.Over S := ⟨J.blowupToBase ≫ f[Ψ]⟩
    J.blowup.IsProjectiveOver ℂ) hker).mp hprojective

private theorem exists_rayBoundaryIdeal_of_exceptional_comap
    {Y : Scheme} {J : Y.IdealSheafData}
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (e : Φ.algebraicRealization ≅ Y)
    (hJ : J.IsExceptionalCurveOfFirstKind)
    (hle : ((J.comap e.hom).support : Set Φ.algebraicRealization) ⊆
      (Φ.boundaryIdeal hc.nonempty_cones).support) :
    ∃ r : Φ.Ray, J.comap e.hom = Φ.rayBoundaryIdeal hΦ r := by
  let := hJ.isIntegral_subscheme
  let K := J.comap e.hom
  have : IsIntegral K.subscheme :=
    IsIntegral.of_isIso
      (asIso ((J.comapIso e.hom).hom ≫ Limits.pullback.snd e.hom J.subschemeι)).inv
  have hK := hJ.isEffectiveCartier.comap e.hom
  let q : CodimensionOnePoint Φ.algebraicRealization :=
    ⟨K.subschemeι (genericPoint K.subscheme), hK.coheight_subschemeι_genericPoint⟩
  have hq : q ∈ Set.range (Φ.rayBoundaryPoint hΦ) := by
    rw [Φ.range_rayBoundaryPoint hΦ hc.nonempty_cones, Set.mem_ofPred, ← Set.mem_compl_iff,
      ← Φ.support_boundaryIdeal hc.nonempty_cones]
    exact hle (by rw [← range_subschemeι]; exact Set.mem_range_self _)
  obtain ⟨r, hr⟩ := hq
  refine ⟨r, ?_⟩
  rw [rayBoundaryIdeal_def, hr, vanishingIdeal_closure_subschemeι_genericPoint]

section Point

variable {X : Scheme} [X.Over S] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ S)] {p : X}

local notation "f" => (X ↘ S)
local notation "I" => Scheme.Hom.ker (X.fromSpecResidueField p)
local notation "π" => blowupToBase I
local notation "E" => Scheme.IdealSheafData.comap I π

private theorem exists_exceptional_ray_of_pointBlowup
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (hp : IsClosed ({p} : Set X))
    (e : Φ.algebraicRealization ≅ (I).blowup) (he : e.hom ≫ π ≫ f = s[Φ])
    (hle : (((E).comap e.hom).support : Set Φ.algebraicRealization) ⊆
      (Φ.boundaryIdeal hc.nonempty_cones).support) :
    ∃ r : Φ.Ray, (E).comap e.hom = Φ.rayBoundaryIdeal hΦ r ∧
      Φ.rayBoundarySelfIntersection hΦ r = -1 := by
  let : (I).blowup.Over S := ⟨π ≫ f⟩
  let : e.hom.IsOver S := ⟨he⟩
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f 2).mp inferInstance).2 p hp
  have := isRegularLocalRing_stalk_of_smooth f p
  have hE := isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hdim
  obtain ⟨r, hr⟩ := exists_rayBoundaryIdeal_of_exceptional_comap hΦ hc e hE hle
  have : Nonempty Φ.cones := hc.nonempty_cones
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have hclass := hE.isEffectiveCartier.pullback_mk_toInvertibleSheaf (g := e.hom)
    (hr.symm ▸ Φ.isEffectiveCartier_rayBoundaryIdeal hΦ r)
  rw [mk_toInvertibleSheaf_congr _ (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ r) hr] at hclass
  have hproj : (I).blowup.IsProjectiveOver ℂ := (I).isProjectiveOver_blowup_of_isNoetherianRing ℂ
  refine ⟨r, hr, ?_⟩
  let K := (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ r).toInvertibleSheaf
  have hprime : (LineBundleClass.mk K)⁻¹ = primeDivisorClass (Φ.rayBoundaryPoint hΦ r) := by
    dsimp only [K]
    rw [primeDivisorClass_def, mk_toInvertibleSheaf_congr _ _ (Φ.rayBoundaryIdeal_def hΦ r)]
  rw [rayBoundarySelfIntersection_def, ← hprime, ← hclass, ← pullback_inv,
    Chow.classIntersectionNumber_pullback_of_isIso ℂ e.hom]
  simpa only [blowupExceptionalClass_def, pullback_one, one_mul, zpow_one,
    Chow.classIntersectionNumber_one_left, zero_sub, mul_one] using
    Chow.classIntersectionNumber_pointBlowup p ℂ hp 1 1 1 1 hproj

omit [X.IsProjectiveOver ℂ] in
private theorem exists_baseIso_comp_eq_of_toric_centres
    {Ψ : Fan i} (b : Basis (Fin 2) ℤ N) (hΨ : Ψ.IsRegular) (σ : Ψ.cones)
    (hp : IsClosed ({p} : Set X))
    {u : (I).blowup ≅ (Ψ.algebraicRealization.fromSpecResidueField
      (Ψ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))).ker.blowup}
    (he : pullback u.hom (Ψ.algebraicRealization.fromSpecResidueField
      (Ψ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))).ker.blowupExceptionalClass =
      (I).blowupExceptionalClass) :
    let q := Ψ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ)
    let J := (Ψ.algebraicRealization.fromSpecResidueField q).ker
    ∃ g : X ≅ Ψ.algebraicRealization, π ≫ g.hom = u.hom ≫ J.blowupToBase := by
  intro q J
  let t := Ψ.distinguishedPointHom σ
  have := Ψ.isClosedImmersion_distinguishedPointHom σ
  have hq : IsClosed ({q} : Set Ψ.algebraicRealization) := by
    let z : S := IsLocalRing.closedPoint ℂ
    have hs : IsClosed ((fun x : S ↦ t x) '' {z}) :=
      t.isClosedMap _ isClosed_singleton
    rw [Set.image_singleton] at hs
    exact hs
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  have : SmoothOfRelativeDimension 2 s[Ψ] :=
    hN ▸ Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : Smooth s[Ψ] := SmoothOfRelativeDimension.smooth 2 s[Ψ]
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := isRegularLocalRing_stalk_of_smooth f p
  have := isRegularLocalRing_stalk_of_smooth s[Ψ] q
  have hdp := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f 2).mp inferInstance).2 p hp
  have hdq := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq s[Ψ] 2).mp inferInstance).2 q hq
  obtain ⟨g, ⟨hg, hu⟩, -⟩ := existsUnique_baseIso_of_pullback_blowupExceptionalClass_eq
    hp hq hdp hdq u he
  refine ⟨g, ?_⟩
  rw [hu, blowupIso_hom_blowupToBase]

private theorem exists_baseIso_of_exceptional_ray
    (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hp : IsClosed ({p} : Set X)) (e : Φ.algebraicRealization ≅ (I).blowup)
    (hover : e.hom ≫ π ≫ f = s[Φ])
    (r : Φ.Ray) (hr : (E).comap e.hom = Φ.rayBoundaryIdeal hΦ r)
    (hsq : Φ.rayBoundarySelfIntersection hΦ r = -1) :
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (_ : Ψ.IsComplete) (h : Φ.IsSubdivision Ψ)
      (g : X ≅ Ψ.algebraicRealization),
      e.hom ≫ π ≫ g.hom = h.toFanHom.algebraicMap ∧ g.hom ≫ s[Ψ] = f := by
  let : (I).blowup.Over S := ⟨π ≫ f⟩
  let : e.hom.IsOver S := ⟨hover⟩
  have : (I).blowup.IsProjectiveOver ℂ := (I).isProjectiveOver_blowup_of_isNoetherianRing ℂ
  have : Φ.algebraicRealization.IsProjectiveOver ℂ :=
    Scheme.IsProjectiveOver.of_isClosedImmersion ℂ e.hom
  obtain ⟨Ψ, hΨ, hc', σ, -, h, t, ht, htE, -⟩ :=
    exists_iso_blowup_of_ray_self_intersection_neg_one b hΦ hc r hsq
  let q := Ψ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ)
  let J := (Ψ.algebraicRealization.fromSpecResidueField q).ker
  have hJ : (Ψ.distinguishedPointHom σ).ker = J :=
    (Ψ.distinguishedPointHom σ).ker_eq_ker_fromSpecResidueField
  have ht' : ∃ t' : Φ.algebraicRealization ≅ J.blowup,
      t'.hom ≫ J.blowupToBase = h.toFanHom.algebraicMap ∧
        (J.comap J.blowupToBase).comap t'.hom = Φ.rayBoundaryIdeal hΦ r := by
    generalize (Ψ.distinguishedPointHom σ).ker = L at t ht htE hJ
    subst L
    exact ⟨t, ht, htE⟩
  obtain ⟨t', ht', ht'E⟩ := ht'
  let u := e.symm ≪≫ t'
  have hu : (J.comap J.blowupToBase).comap u.hom = E := by
    simp only [u, Iso.trans_hom, Iso.symm_hom, comap_comp, ht'E]
    rw [← hr, ← comap_comp, Iso.inv_hom_id, comap_id]
  have hclass := J.isEffectiveCartier_comap_blowupToBase.pullback_mk_toInvertibleSheaf
    (g := u.hom) (hu.symm ▸ (I).isEffectiveCartier_comap_blowupToBase)
  rw [mk_toInvertibleSheaf_congr _ (I).isEffectiveCartier_comap_blowupToBase hu] at hclass
  have hclass' : pullback u.hom J.blowupExceptionalClass = (I).blowupExceptionalClass := by
    simpa only [blowupExceptionalClass_def, pullback_inv] using congrArg Inv.inv hclass
  obtain ⟨g, hcomm⟩ := exists_baseIso_comp_eq_of_toric_centres (u := u) b hΨ σ hp hclass'
  have hcomm' : π ≫ g.hom = u.hom ≫ J.blowupToBase := hcomm
  have hproj : e.hom ≫ π ≫ g.hom = h.toFanHom.algebraicMap := by
    simpa only [hcomm', u, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc] using ht'
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f 2).mp inferInstance).2 p hp
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have := isRegularLocalRing_stalk_of_smooth f p
  have hI := X.ker_fromSpecResidueField_eq_vanishingIdeal p
  have : Epi π := (congrArg (fun K : X.IdealSheafData ↦ Epi K.blowupToBase) hI).mpr
    (epi_blowupToBase_point hp hdim)
  refine ⟨Ψ, hΨ, hc', h, g, hproj, ?_⟩
  apply (cancel_epi π).mp
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc π, ← Category.assoc e.hom, hproj,
    FanHom.algebraicMap_comp_algebraicRealizationStructureMap]
  exact hover.symm

/-- A specified point blowup of a smooth projective surface with a toric reduced total
boundary descends to a subdivision of a toric model of the base pair when the
center lies on the boundary. The isomorphism commutes with the specified projection. -/
theorem exists_toric_base_of_pointBlowup (b : Basis (Fin 2) ℤ N)
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (D : X.IdealSheafData)
    (hp : IsClosed ({p} : Set X)) (hpD : p ∈ D.support)
    (e : Φ.algebraicRealization ≅ (I).blowup) (hover : e.hom ≫ π ≫ f = s[Φ])
    (hD : (((D.comap π).comap e.hom).support : Set Φ.algebraicRealization) =
      (Φ.boundaryIdeal hc.nonempty_cones).support) :
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (hc' : Ψ.IsComplete) (h : Φ.IsSubdivision Ψ)
      (g : Ψ.algebraicRealization ≅ X),
      e.hom ≫ π = h.toFanHom.algebraicMap ≫ g.hom ∧ g.hom ≫ f = s[Ψ] ∧
      (D.comap g.hom).support = (Ψ.boundaryIdeal hc'.nonempty_cones).support := by
  have hle : ((I).support : Set X) ⊆ D.support :=
    (Scheme.support_ker_fromSpecResidueField_of_isClosed hp).symm ▸ Set.singleton_subset_iff.mpr hpD
  have hE : (((E).comap e.hom).support : Set Φ.algebraicRealization) ⊆
      (Φ.boundaryIdeal hc.nonempty_cones).support := by
    rw [← hD, support_comap, support_comap, support_comap, support_comap]
    exact Set.preimage_mono (Set.preimage_mono hle)
  obtain ⟨r, hr, hs⟩ := exists_exceptional_ray_of_pointBlowup hΦ hc hp e hover hE
  obtain ⟨Ψ, hΨ, hc', h, g, hcomm, hg⟩ := exists_baseIso_of_exceptional_ray b hΦ hc hp e
    hover r hr hs
  have hg' : g.inv ≫ f = s[Ψ] := by rw [← hg, Iso.inv_hom_id_assoc]
  have hπ : e.hom ≫ π = h.toFanHom.algebraicMap ≫ g.inv := by
    simp only [← hcomm, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hsurj : Surjective h.toFanHom.algebraicMap := by
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f 2).mp inferInstance).2 p hp
    have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
    have := isRegularLocalRing_stalk_of_smooth f p
    have hI := X.ker_fromSpecResidueField_eq_vanishingIdeal p
    have : Surjective π :=
      (congrArg (fun K : X.IdealSheafData ↦ Surjective K.blowupToBase) hI).mpr
        (surjective_blowupToBase_point hp hdim)
    rw [← hcomm]
    infer_instance
  refine ⟨Ψ, hΨ, hc', h, g.symm, hπ, hg', ?_⟩
  apply SetLike.coe_injective
  apply h.toFanHom.algebraicMap.surjective.preimage_injective
  have hB := congrArg (fun J : Φ.algebraicRealization.IdealSheafData ↦
      (J.support : Set Φ.algebraicRealization))
    (h.radical_comap_boundaryIdeal hc.nonempty_cones hc'.nonempty_cones)
  rw [support_radical, support_comap, Closeds.coe_preimage] at hB
  rw [hB, ← hD, ← comap_comp, hπ, comap_comp, support_comap, Closeds.coe_preimage]
  simp only [Iso.symm_hom, support_comap, Closeds.coe_preimage]

end Point

/-- If the reduced total transform on a specified nodal blowup tower is toric, then its
original pair is toric. The specified tower projection is the subdivision morphism. -/
theorem exists_toric_base_of_nodal_tower (b : Basis (Fin 2) ℤ N)
    {X Y : Scheme} [X.Over S] [X.IsProjectiveOver ℂ]
    [SmoothOfRelativeDimension 2 (X ↘ S)] {D : X.IdealSheafData}
    {n : ℕ} {T : BlowupTower X n Y} (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (e : Φ.algebraicRealization ≅ Y)
    (he : e.hom ≫ T.toBase ≫ X ↘ S = s[Φ])
    (hD : (((D.comap T.toBase).comap e.hom).support : Set Φ.algebraicRealization) =
      (Φ.boundaryIdeal hc.nonempty_cones).support) :
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (hc' : Ψ.IsComplete) (h : Φ.IsSubdivision Ψ)
      (g : Ψ.algebraicRealization ≅ X),
      e.hom ≫ T.toBase = h.toFanHom.algebraicMap ≫ g.hom ∧ g.hom ≫ X ↘ S = s[Ψ] ∧
      (D.comap g.hom).support = (Ψ.boundaryIdeal hc'.nonempty_cones).support := by
  induction hT generalizing Φ with
  | nil =>
    refine ⟨Φ, hΦ, hc, IsSubdivision.refl Φ, e, by simp, by simpa using he, ?_⟩
    exact SetLike.coe_injective (by simpa only [toBase_nil, comap_id] using hD)
  | @snoc n W T J hT p hp hJ hnode ih =>
    subst J
    let : W.Over S := ⟨T.toBase ≫ X ↘ S⟩
    have hW : W ↘ S = T.toBase ≫ X ↘ S := rfl
    let : W.IsProjectiveOver ℂ := T.isProjectiveOver ℂ
    have : SmoothOfRelativeDimension 2 (W ↘ S) :=
      hT.isClosedPointTower.smoothOfRelativeDimension (X ↘ S)
    have hpD : p ∈ (D.comap T.toBase).support := by
      simpa only [Category.comp_id] using mem_support_of_isNodeOfReducedBoundary hnode
    obtain ⟨Ψ, hΨ, hc', h, e', hcomm, he', hD'⟩ :=
      exists_toric_base_of_pointBlowup b hΦ hc (D.comap T.toBase) hp hpD e
        (by simpa only [hW, toBase_snoc, Category.assoc] using he)
        (by simpa only [toBase_snoc, comap_comp] using hD)
    obtain ⟨Ω, hΩ, hd, F, g, hg, hg', hD''⟩ := ih hΨ hc' e' he'
      (congrArg (fun J : Closeds Ψ.algebraicRealization ↦ (J : Set Ψ.algebraicRealization)) hD')
    refine ⟨Ω, hΩ, hd, h.trans F, g, ?_, hg', hD''⟩
    rw [toBase_snoc, ← Category.assoc, hcomm, Category.assoc, hg,
      IsSubdivision.toFanHom_trans h F, FanHom.algebraicMap_comp, Category.assoc]

/-- A pair of boundary complexity zero with a specified toric presentation is itself toric.
The isomorphism is over `ℂ` and identifies the reduced boundary ideals. -/
theorem exists_toric_of_boundaryComplexity_zero [Nonempty Φ.cones]
    {X Y : Scheme} [X.Over S] [X.IsProjectiveOver ℂ] [IsNoetherian X] [IsIntegral X]
    [SmoothOfRelativeDimension 2 (X ↘ S)] [Module.Finite ℤ (Additive (LineBundleClass X))]
    {D : X.IdealSheafData} (hCartier : D.IsEffectiveCartier) (hzero : D.boundaryComplexity = 0)
    {m n : ℕ} {T : BlowupTower X m Y} (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ) (e : Y ≅ (internalBlowupTower b s c).1)
    (he : e.inv ≫ T.toBase ≫ X ↘ S =
      (internalBlowupTower b s c).2.toTower.toBase ≫ s[Φ])
    (hD : ((D.comap T.toBase).comap e.inv).support =
      (Scheme.Hom.ker (internalBlowupTower b s c).2.boundaryι).support) :
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (hc' : Ψ.IsComplete) (g : Ψ.algebraicRealization ≅ X),
      g.hom ≫ X ↘ S = s[Ψ] ∧ (D.comap g.hom).radical = Ψ.boundaryIdeal hc'.nonempty_cones := by
  have hlen := boundaryComplexity_eq_length_of_toricPresentation hΦ b s c hc hCartier hT e hD
  have hn : n = 0 := by omega
  subst n
  revert hD he e
  rw [internalBlowupTower_zero]
  intro e he hD
  have hover : e.inv ≫ T.toBase ≫ X ↘ S = s[Φ] := by simpa using he
  have hs : (((D.comap T.toBase).comap e.inv).support : Set Φ.algebraicRealization) =
      (Φ.boundaryIdeal hc.nonempty_cones).support := by
    have hD' := congrArg (fun J : Closeds Φ.algebraicRealization ↦
      (J : Set Φ.algebraicRealization)) hD
    simpa only [WithBoundary.boundaryι_nil, ker_subschemeι] using hD'
  obtain ⟨Ψ, hΨ, hc', _, g, -, hg, hsupport⟩ :=
    exists_toric_base_of_nodal_tower b hT hΦ hc e.symm hover hs
  refine ⟨Ψ, hΨ, hc', g, hg, ?_⟩
  rw [← vanishingIdeal_support, hsupport, Ψ.boundaryIdeal_def]
  congr 1

end TauCeti.Toric.Fan

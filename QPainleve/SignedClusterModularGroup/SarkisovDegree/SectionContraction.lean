/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Homaloidal
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.ProjectivePlane
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.Link

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Class
import QPainleve.AlgebraicGeometry.Blowup.Intersection
import QPainleve.AlgebraicGeometry.Blowup.Projective.Global
import QPainleve.AlgebraicGeometry.Chow.Isomorphism
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Sarkisov degree under contraction of the negative section

The toric contraction from the first Hirzebruch surface to the plane preserves
the specified resolving morphism. The new first blowup is the blowup of the
coordinate vertex, of order `a - b` for a system of class `aA + bB`. All
subsequent exceptional coordinates are retained, including at infinitely near
centers. The plane degree is `a`, so the Sarkisov bidegree decreases when
`2a < 3b`. This is the negative-section case of Proposition 8.11 in
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry LineBundleClass Chow TauCeti.SymmetricAlgebra
open TauCeti.Toric
open Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "Ppol" => Proj (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "degree" => Module.Basis.picardTwistEquiv (Pi.basisFun ℂ (Fin 3))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, ((1 : ℕ) : ℤ) • b 0 - b 1])

local notation "X" => Φ.algebraicRealization
local notation "C" => Fan.hirzebruchPicardBasis b 1 hΦ r hr
local notation "fX" => (X ↘ S)
local notation "fP" => (P ↘ S)

section

variable [Nonempty Φ.cones] [Φ.algebraicRealization.IsProjectiveOver ℂ]

omit [Nonempty Φ.cones] [Φ.algebraicRealization.IsProjectiveOver ℂ] in
include b hc hr in
private theorem hirzebruchOne_plane_blowup :
    ∃ (d : Basis (Fin 2) ℤ N) (s : Φ.IsSubdivision (Fan.projectiveSpace d Φ.lattice))
      (p : P) (_ : IsClosed ({p} : Set P))
      (e : X ≅ (Scheme.fromSpecResidueField P p).ker.blowup),
      e.hom ≫ (Scheme.fromSpecResidueField P p).ker.blowupToBase =
        s.toFanHom.algebraicMap ≫ (Fan.projectivePlaneIso d Φ.lattice).hom ≫
          (Pi.basisFun ℂ (Fin 3)).polynomialProjIso.hom ∧
      e.hom ≫ (Scheme.fromSpecResidueField P p).ker.blowupToBase ≫ fP = fX ∧
      ((Scheme.fromSpecResidueField P p).ker.comap
        (e.hom ≫ (Scheme.fromSpecResidueField P p).ker.blowupToBase)) =
        Φ.rayBoundaryIdeal hΦ (r 0) := by
  have hrays : Set.range (Fan.Ray.primitiveGenerator (Phi := Φ)) =
      {b 0, b 1, -b 0, b 0 - b 1} := by
    rw [← r.surjective.range_comp, Function.comp_def, hr]
    ext x
    simp
    tauto
  obtain ⟨d, s, ρ, e, -, -, hρ, -, -, he, hE, -⟩ :=
    Fan.exists_iso_blowup_projectivePlane_of_hirzebruchOne b hΦ hc hrays
  let q := (Fan.projectiveSpace d Φ.lattice).distinguishedPointHom
    (Fan.projectiveSpaceMaximalCone d Φ.lattice none)
  let v := q ≫ (Fan.projectivePlaneIso d Φ.lattice).hom
  let a : Ppol ≅ P := (Pi.basisFun ℂ (Fin 3)).polynomialProjIso
  let p := (v ≫ a.hom) (IsLocalRing.closedPoint ℂ)
  let J := (Scheme.fromSpecResidueField P p).ker
  have : IsClosedImmersion q := Fan.isClosedImmersion_distinguishedPointHom _ _
  have : IsClosedImmersion (v ≫ a.hom) := by dsimp [v]; infer_instance
  have hp : IsClosed ({p} : Set P) := by
    exact (Set.range_eq_singleton (f := fun x : S ↦ (v ≫ a.hom) x)
      (fun y ↦ congrArg (fun x : S ↦ (v ≫ a.hom) x) (Subsingleton.elim y _))) ▸
        (v ≫ a.hom).isClosedEmbedding.isClosed_range
  have hJ : J.comap a.hom = v.ker := by
    dsimp only [J, p]
    rw [← (v ≫ a.hom).ker_eq_ker_fromSpecResidueField, v.comap_ker_comp_of_isClosedImmersion]
  let e' := e ≪≫ J.blowupIso a hJ
  have he' : e'.hom ≫ J.blowupToBase =
      s.toFanHom.algebraicMap ≫ (Fan.projectivePlaneIso d Φ.lattice).hom ≫ a.hom := by
    rw [Iso.trans_hom, Category.assoc, blowupIso_hom_blowupToBase, ← Category.assoc, he,
      Category.assoc]
  have hρ' : ρ = r 0 := by
    apply Fan.Ray.primitiveGenerator_injective
    exact hρ.trans (congrFun hr 0).symm
  refine ⟨d, s, p, hp, e', he', ?_, ?_⟩
  · rw [← Category.assoc, he']
    simp only [Category.assoc, a, over_eq_projToSpec,
      Module.Basis.polynomialProjIso_hom_over, Fan.projectivePlaneIso_hom_toSpecCoeff,
      FanHom.algebraicMap_comp_algebraicRealizationStructureMap, Fan.algebraicRealization_over]
  · rw [he', ← Category.assoc, ← he]
    rw [comap_comp, comap_comp, ← hρ']
    have hJ' : (Scheme.fromSpecResidueField P p).ker.comap a.hom = v.ker := hJ
    rw [hJ']
    simpa only [comap_comp] using hE


section Marking

variable {p : P}
local notation "J" => Scheme.Hom.ker (Scheme.fromSpecResidueField P p)
local notation "W" => blowup J
local notation "π" => blowupToBase J
local notation "U₀" => BlowupTower.snoc BlowupTower.nil J

omit [Φ.algebraicRealization.IsProjectiveOver ℂ] in
private theorem hirzebruchOne_section_class (e : X ≅ W)
    (hE : (J).comap (e.hom ≫ π) = Φ.rayBoundaryIdeal hΦ (r 0)) :
    pullback e.hom (J).blowupExceptionalClass = (C 1).toMul := by
  classical
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  let hD := Φ.isEffectiveCartier_rayBoundaryIdeal hΦ (r 0)
  rw [blowupExceptionalClass_def, pullback_inv,
    (J).isEffectiveCartier_comap_blowupToBase.pullback_mk_toInvertibleSheaf (by
      rwa [← comap_comp, hE])]
  rw [mk_toInvertibleSheaf_congr _ hD (by rw [← comap_comp, hE]),
    Fan.hirzebruchPicardBasis_apply_one, Fan.rayDivisorToPicard_single, one_smul]
  rw [toMul_ofMul, primeDivisorClass_def,
    mk_toInvertibleSheaf_congr _ _ (Φ.rayBoundaryIdeal_def hΦ (r 0))]

include hc in
private theorem hirzebruchOne_section_coefficient [SmoothOfRelativeDimension 2 fX]
    (hp : IsClosed ({p} : Set P))
    (e : X ≅ W) (he : e.hom ≫ π ≫ fP = fX)
    (hE : (J).comap (e.hom ≫ π) = Φ.rayBoundaryIdeal hΦ (r 0))
    (L : Additive (LineBundleClass P)) (c : Fin 1 → ℤ) :
    let M := Additive.ofMul (pullback e.hom ((U₀).picardHom (L, c)).toMul)
    c 0 = (C).repr M 1 - (C).repr M 0 := by
  dsimp only
  let : (W).Over S := ⟨π ≫ fP⟩
  let : e.hom.IsOver S := ⟨he⟩
  have hW : (W).IsProjectiveOver ℂ := (J).isProjectiveOver_blowup_of_isNoetherianRing ℂ
  have h := (Fan.hirzebruchPicardBasis_intersection_repr b 1 hΦ r hr hc
    (Additive.ofMul (pullback e.hom ((U₀).picardHom (L, c)).toMul))).2
  simp only [intersectionBilinForm_apply, toMul_ofMul, one_mul] at h
  rw [← hirzebruchOne_section_class b hΦ r hr e hE,
    classIntersectionNumber_pullback_of_isIso ℂ e.hom] at h
  have hpull := classIntersectionNumber_pointBlowup p ℂ hp L.toMul 1 (c 0) 1 hW
  rw [classIntersectionNumber_one_right] at hpull
  simp only [picardHom_snoc_apply_toMul, picardHom_nil, Fin.last_zero] at h ⊢
  simp only [pullback_one, one_mul, zpow_one, mul_one, zero_sub,
    ← blowupExceptionalClass_def] at hpull
  omega

private theorem prepend_picard_coordinates {Y Z : Scheme} {n : ℕ}
    {T : BlowupTower X n Y} {U : BlowupTower W n Z}
    (hT : IsClosedPointTower X T) (e : X ≅ W) {k : Y ≅ Z} (hk : IsLift e T U k)
    (g : Y ⟶ P) (hU : IsClosedPointTower P ((U₀).append U)) :
    let : SmoothOfRelativeDimension 2 fX :=
      (by simpa using Module.finrank_eq_card_basis b : Module.finrank ℤ N = 2) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X := isNoetherian_of_finiteType fX
    let v : Additive (LineBundleClass X) × (Fin n → ℤ) :=
      (T.picardMarking hT fX).symm (Additive.ofMul (pullback g H))
    let w := (((U₀).append U).picardMarking hU fP).symm
      (Additive.ofMul (pullback (k.inv ≫ g) H))
    v = (Additive.ofMul (pullback e.hom
        ((U₀).picardHom (w.1, fun j ↦ w.2 (j.castAdd n))).toMul),
      fun j ↦ w.2 (j.natAdd 1)) := by
  intro _ _ v w
  apply (LinearEquiv.symm_apply_eq _).mpr
  apply Additive.toMul.injective
  rw [picardMarking_apply, ← hk.pullback_picardHom, ← picardHom_append,
    ← picardMarking_apply _ hU fP, LinearEquiv.apply_symm_apply]
  simp only [toMul_ofMul, pullback_comp, Iso.hom_inv_id_assoc]

include hc in
/-- A resolving morphism and its transport across the blowup of a plane vertex have
matching Picard coordinates in the plane and Hirzebruch-one markings. -/
theorem hirzebruchOne_resolution_coordinates {Y Z : Scheme} {n : ℕ}
    {T : BlowupTower X n Y} {U : BlowupTower W n Z}
    (hT : IsClosedPointTower X T) (hp : IsClosed ({p} : Set P))
    (e : X ≅ W) (he : e.hom ≫ π ≫ fP = fX)
    (hE : (J).comap (e.hom ≫ π) = Φ.rayBoundaryIdeal hΦ (r 0))
    {k : Y ≅ Z} (hk : IsLift e T U k)
    (g : Y ⟶ P) (hg : g ≫ fP = T.toBase ≫ fX)
    (hbir : Scheme.BirationalOver g (𝟙 P))
    (hU : IsClosedPointTower P ((U₀).append U))
    (hg' : (k.inv ≫ g) ≫ fP = ((U₀).append U).toBase ≫ fP)
    (hbir' : Scheme.BirationalOver (k.inv ≫ g) (𝟙 P)) :
    let : SmoothOfRelativeDimension 2 fX :=
      (by simpa using Module.finrank_eq_card_basis b : Module.finrank ℤ N = 2) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X := isNoetherian_of_finiteType fX
    let v : Additive (LineBundleClass X) × (Fin n → ℤ) :=
      (T.picardMarking hT fX).symm (Additive.ofMul (pullback g H))
    let w : Additive (LineBundleClass P) × (Fin (1 + n) → ℤ) :=
      (((U₀).append U).picardMarking hU fP).symm (Additive.ofMul (pullback (k.inv ≫ g) H))
    degree w.1 = (C).repr v.1 0 ∧
      w.2 (Fin.castAdd n (0 : Fin 1)) = (C).repr v.1 1 - (C).repr v.1 0 ∧
      ∀ j : Fin n, w.2 (j.natAdd 1) = v.2 j := by
  intro hdim hnoeth v w
  let := hdim
  let := hnoeth
  have hv : v = (Additive.ofMul (pullback e.hom
      ((U₀).picardHom (w.1, fun j ↦ w.2 (j.castAdd n))).toMul), fun j ↦ w.2 (j.natAdd 1)) :=
    prepend_picard_coordinates b hΦ hT e hk g hU
  have hfirst : w.2 (Fin.castAdd n (0 : Fin 1)) = (C).repr v.1 1 - (C).repr v.1 0 := by
    rw [hv]
    exact hirzebruchOne_section_coefficient b hΦ hc r hr hp e he hE w.1
      (fun j ↦ w.2 (j.castAdd n))
  have hrest (j : Fin n) : w.2 (j.natAdd 1) = v.2 j := (congrArg (fun z ↦ z.2 j) hv).symm
  have hH := (hT.homaloidal_intersection_identities_of_hirzebruch b 1 hΦ hc r hr g hg hbir).2
  have hP := (hU.homaloidal_intersection_identities (k.inv ≫ g) hg' hbir').2
  have hsum : (∑ j, -w.2 j) = -w.2 (Fin.castAdd n (0 : Fin 1)) + ∑ j, -v.2 j := by
    rw [Fin.sum_univ_add (a := 1) (b := n), Fin.sum_univ_one]
    simp only [hrest]
  -- The two canonical-degree formulas determine the new plane degree.
  have hcanon : (∑ j, -w.2 j) = degree w.1 * 3 - 3 := by
    rw [classIntersectionNumber_projectivePlane, mk_canonicalBundle_projectivePlane,
      Module.Basis.picardTwistEquiv_apply_twist, ofMul_toMul, mul_neg, neg_neg] at hP
    exact hP
  have hsumH : (∑ j, -v.2 j) = 2 * (C).repr v.1 0 + (C).repr v.1 1 - 3 := by
    simpa only [Nat.cast_one, sub_eq_add_neg, Int.reduceNeg, Int.reduceAdd, one_mul] using hH
  exact ⟨by omega, hfirst, hrest⟩

end Marking

end

include hc in
/-- Contracting the negative section of the first Hirzebruch surface gives a
point-blowup tower over the plane resolving the transported morphism.
For the resolved line class with original coordinates `(a, b)`, the new
plane degree is `a`. The new exceptional coordinate is `b - a` and all
later exceptional coordinates agree in their original order. If the original
fiber degree is positive and all base orders lie in `[0, b / 2]`, the
Sarkisov bidegree strictly decreases. -/
theorem exists_plane_resolution_of_hirzebruchOne {Y : Scheme} {n : ℕ}
    {T : BlowupTower X n Y} (hT : IsClosedPointTower X T)
    (g : Y ⟶ P) (hg : g ≫ fP = T.toBase ≫ fX)
    (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 fX :=
      (by simpa using Module.finrank_eq_card_basis b : Module.finrank ℤ N = 2) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : Smooth fX := Φ.smooth_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X := isNoetherian_of_finiteType fX
    let v : Additive (LineBundleClass X) × (Fin n → ℤ) :=
      (T.picardMarking hT fX).symm (Additive.ofMul (pullback g H))
    let α := (C).repr v.1 0
    let β := (C).repr v.1 1
    ∃ (d : Basis (Fin 2) ℤ N) (s : Φ.IsSubdivision (Fan.projectiveSpace d Φ.lattice))
      (Z : Scheme) (U : BlowupTower P (1 + n) Z) (hU : IsClosedPointTower P U)
      (k : Y ≅ Z),
      k.hom ≫ U.toBase = T.toBase ≫ s.toFanHom.algebraicMap ≫
        (Fan.projectivePlaneIso d Φ.lattice).hom ≫ (Pi.basisFun ℂ (Fin 3)).polynomialProjIso.hom ∧
      (k.inv ≫ g) ≫ fP = U.toBase ≫ fP ∧
      Scheme.BirationalOver (k.inv ≫ g) (𝟙 P) ∧
      let w : Additive (LineBundleClass P) × (Fin (1 + n) → ℤ) :=
        (U.picardMarking hU fP).symm (Additive.ofMul (pullback (k.inv ≫ g) H))
      degree w.1 = α ∧
      w.2 (Fin.castAdd n (0 : Fin 1)) = β - α ∧
      (∀ j : Fin n, w.2 (j.natAdd 1) = v.2 j) ∧
      (0 < β → (∀ j : Fin n, 0 ≤ -v.2 j ∧ 2 * (-v.2 j) ≤ β) →
        planeSarkisovBidegree (degree w.1).toNat (∑ j, (-w.2 j).toNat) <
          hirzebruchSarkisovBidegree β.toNat (∑ j, (-v.2 j).toNat)) := by
  intro hcones hdim hsmooth hnoeth v α β
  let := hcones
  let := hdim
  let := hsmooth
  let := hnoeth
  obtain ⟨d, s, p, hp, e, he, hover, hE⟩ := hirzebruchOne_plane_blowup b hΦ hc r hr
  let J := (Scheme.fromSpecResidueField P p).ker
  let : J.blowup.Over S := ⟨J.blowupToBase ≫ fP⟩
  let : e.hom.IsOver S := ⟨hover⟩
  let : J.blowup.IsProjectiveOver ℂ := J.isProjectiveOver_blowup_of_isNoetherianRing ℂ
  let : (X).IsProjectiveOver ℂ := Scheme.IsProjectiveOver.of_isClosedImmersion ℂ e.hom
  let U₀ := BlowupTower.snoc BlowupTower.nil J
  let R := T.transport e
  let U := U₀.append R.tower
  have hU₀ : IsClosedPointTower P U₀ := IsClosedPointTower.nil.snoc p hp rfl
  have hU := hU₀.append (R.isLift.isClosedPointTower hT)
  have hproj : R.iso.hom ≫ U.toBase = T.toBase ≫ e.hom ≫ J.blowupToBase := by
    rw [toBase_append, ← Category.assoc, R.isLift.hom_toBase, Category.assoc,
      toBase_snoc, toBase_nil, Category.comp_id]
  have hf : (R.iso.inv ≫ g) ≫ fP = U.toBase ≫ fP := by
    apply (cancel_epi R.iso.hom).mp
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc R.iso.hom, hproj, Category.assoc, Category.assoc, hover, hg]
  have hbir' : Scheme.BirationalOver (R.iso.inv ≫ g) (𝟙 P) := by
    refine Scheme.BirationalOver.trans (sY := g) ⟨.ofIso R.iso.symm, ?_⟩ hbir
    simp [Scheme.PartialIso.IsOver, Scheme.PartialIso.ofIso]
  refine ⟨d, s, _, U, hU, R.iso, hproj.trans (by rw [he]), hf, hbir', ?_⟩
  dsimp only
  obtain ⟨hdegree, hfirst, hrest⟩ :=
    hirzebruchOne_resolution_coordinates b hΦ hc r hr hT hp e hover hE
      R.isLift g hg hbir hU hf hbir'
  refine ⟨hdegree, hfirst, hrest, fun hβ hm ↦ ?_⟩
  have hH := hT.homaloidal_intersection_identities_of_hirzebruch b 1 hΦ hc r hr g hg hbir
  have hsq : (∑ j, (-v.2 j) ^ 2) = 2 * α * β - (1 : ℤ) * β ^ 2 - 1 := by
    simpa only [neg_sq, Nat.cast_one] using hH.1
  have hsumH : (∑ j, -v.2 j) = 2 * α + (2 - (1 : ℤ)) * β - 3 := by
    simpa only [Nat.cast_one] using hH.2
  have hlt : 2 * α < 3 * β := by
    simpa only [Int.reduceAdd] using two_mul_lt_of_hirzebruch_homaloidal hβ hm hsq hsumH
  have hltNat : 2 * α.toNat < 3 * β.toNat := by omega
  rw [hdegree, ← toLex_ofLex (planeSarkisovBidegree _ _), ofLex_planeSarkisovBidegree,
    ← toLex_ofLex (hirzebruchSarkisovBidegree _ _), ofLex_hirzebruchSarkisovBidegree]
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hltNat)

end QPainleve.BlowupTower.IsClosedPointTower

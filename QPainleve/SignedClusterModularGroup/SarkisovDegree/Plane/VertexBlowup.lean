/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.SectionContraction

import QPainleve.AlgebraicGeometry.Blowup.Projective.Global
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Blowup.Tower.Reorder
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Sarkisov degree under a plane vertex blowup

When a specified plane resolution begins at a torus-fixed vertex, the first
blowup becomes the Hirzebruch-one base and the tail of the resolution transports
over that base. The new fiber degree is the plane degree minus the order at
the vertex. This is the torus-fixed plane case of Proposition 8.11 in
[Lutz's appendix to Hacking and Keating][HKL].
When a vertex is absent from the projected centers, a single blowup of its
inverse image on the final scheme gives the corresponding Hirzebruch-one
resolution. This is the toric preparation for the smooth-edge case.

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=71
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry LineBundleClass Chow TauCeti.SymmetricAlgebra
open TauCeti.Toric Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "degree" => Module.Basis.picardTwistEquiv (Pi.basisFun ℂ (Fin 3))
local notation "fP" => (P ↘ S)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (d : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i) (a : Option (Fin 2))

local notation "Ψ" => Fan.projectiveSpace d hi
local notation "hΨ" => Fan.isRegular_projectiveSpace d hi
local notation "σ" => Fan.projectiveSpaceMaximalCone d hi a
local notation "Φ" => Fan.starSubdivisionAlong Ψ hΨ (Subtype.property σ)
local notation "z" => Fan.distinguishedPointHom Ψ σ
local notation "D" => Fan.projectivePlaneIso d hi ≪≫
  Module.Basis.polynomialProjIso (Pi.basisFun ℂ (Fin 3))
local notation "p" => (z ≫ Iso.hom D) (IsLocalRing.closedPoint ℂ)
local notation "J" => Scheme.Hom.ker (Scheme.fromSpecResidueField P p)
local notation "W" => Scheme.IdealSheafData.blowup J
local notation "U₀" => BlowupTower.snoc BlowupTower.nil J
local notation "X" => Fan.algebraicRealization Φ
local notation "fX" => (X ↘ S)
local notation "hΦ" => Fan.isRegular_starSubdivisionAlong Ψ hΨ (Subtype.property σ)

private theorem isClosed_projectivePlane_vertex : IsClosed ({p} : Set P) := by
  have : IsClosedImmersion z := Fan.isClosedImmersion_distinguishedPointHom _ _
  have : IsClosedImmersion (z ≫ (D).hom) := inferInstance
  exact (Set.range_eq_singleton (f := fun x : S ↦ (z ≫ (D).hom) x)
    (fun x ↦ congrArg (fun y : S ↦ (z ≫ (D).hom) y) (Subsingleton.elim x _))) ▸
      (z ≫ (D).hom).isClosedEmbedding.isClosed_range

private theorem exists_vertex_blowup_comparison :
    ∃ (hσ : (σ).val ≠ ⊥) (b : Basis (Fin 2) ℤ N) (r : Fin 4 ≃ (Φ).Ray) (e : X ≅ W),
      (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, ((1 : ℕ) : ℤ) • b 0 - b 1] ∧
      e.hom ≫ (J).blowupToBase =
        ((Ψ).starSubdivisionAlong_isSubdivision hΨ (σ).property hσ).toFanHom.algebraicMap ≫
        (D).hom ∧
      e.hom ≫ (J).blowupToBase ≫ fP = fX ∧
      (J).comap (e.hom ≫ (J).blowupToBase) = (Φ).rayBoundaryIdeal hΦ (r 0) := by
  obtain ⟨hσ, b, e₀, hrays, hgen, he₀, hE⟩ :=
    Fan.exists_blowup_projectivePlane_vertex_hirzebruchOne d hi a
  obtain ⟨r, hr⟩ := Fan.exists_rayEquiv_of_hirzebruch_ray_generators b 1
    (by simpa only [Nat.cast_one, one_smul] using hrays)
  have : IsClosedImmersion z := Fan.isClosedImmersion_distinguishedPointHom _ _
  have : IsClosedImmersion (z ≫ (D).hom) := inferInstance
  have hJ : (J).comap (D).hom = (z).ker := by
    rw [← (z ≫ (D).hom).ker_eq_ker_fromSpecResidueField, (z).comap_ker_comp_of_isClosedImmersion]
  let e := e₀ ≪≫ (J).blowupIso D hJ
  have he : e.hom ≫ (J).blowupToBase =
      ((Ψ).starSubdivisionAlong_isSubdivision hΨ (σ).property hσ).toFanHom.algebraicMap ≫
        (D).hom := by
    calc
      _ = (e₀.hom ≫ (z).ker.blowupToBase) ≫ (D).hom := by
        simp only [e, Iso.trans_hom, Category.assoc, blowupIso_hom_blowupToBase]
      _ = _ := congrArg (· ≫ (D).hom) he₀
  have hr₀ : (Ψ).starSubdivisionAlongRay hΨ (σ).property hσ = r 0 :=
    Fan.Ray.primitiveGenerator_injective (hgen.trans (congrFun hr 0).symm)
  refine ⟨hσ, b, r, e, hr, he, ?_, ?_⟩
  · rw [← Category.assoc, he]
    simp only [Iso.trans_hom, Category.assoc, over_eq_projToSpec,
      Module.Basis.polynomialProjIso_hom_over, Fan.projectivePlaneIso_hom_toSpecCoeff,
      FanHom.algebraicMap_comp_algebraicRealizationStructureMap, Fan.algebraicRealization_over]
  · rw [he, comap_comp, hJ, ← he₀]
    exact hr₀ ▸ hE

/-- A specified plane resolution whose first blowup is at the given toric
vertex transports to a resolution over the corresponding Hirzebruch-one
surface. The transported morphism factors the specified resolution through the plane link.
The new ruling coordinates are the old plane degree and that degree minus
the first base order. All subsequent orders, including infinitely near ones,
retain their indices in the tail. The high-order vertex link strictly
decreases the Sarkisov bidegree. -/
theorem exists_hirzebruch_resolution_of_plane_vertex {Y : Scheme} {n : ℕ}
    {U : BlowupTower W n Y} (hP : IsClosedPointTower P ((U₀).append U))
    (g : Y ⟶ P) (hg : g ≫ fP = ((U₀).append U).toBase ≫ fP)
    (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let w := (((U₀).append U).picardMarking hP fP).symm (Additive.ofMul (pullback g H))
    let δ := degree w.1
    let m := fun j ↦ -w.2 j
    ∃ (hσ : (σ).val ≠ ⊥) (b : Basis (Fin 2) ℤ N)
      (r : Fin 4 ≃ (Φ).Ray)
      (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, ((1 : ℕ) : ℤ) • b 0 - b 1])
      (Z : Scheme) (T : BlowupTower X n Z) (hT : IsClosedPointTower X T)
      (e : X ≅ W) (k : Y ≅ Z),
      IsLift e.symm U T k ∧
      e.hom ≫ (J).blowupToBase =
        ((Ψ).starSubdivisionAlong_isSubdivision hΨ (σ).property hσ).toFanHom.algebraicMap ≫
        (D).hom ∧
      k.hom ≫ T.toBase ≫
          ((Ψ).starSubdivisionAlong_isSubdivision hΨ (σ).property hσ).toFanHom.algebraicMap ≫
          (D).hom = ((U₀).append U).toBase ∧
      (k.inv ≫ g) ≫ fP = T.toBase ≫ fX ∧
      Scheme.BirationalOver (k.inv ≫ g) (𝟙 P) ∧
      let hc : (Φ).IsComplete :=
        ((Ψ).starSubdivisionAlong_isSubdivision hΨ (σ).property hσ).isComplete_iff.mpr
          (Fan.isComplete_projectiveSpace d hi)
      let : Nonempty (Φ).cones := hc.nonempty_cones
      let : SmoothOfRelativeDimension 2 fX := by
        have hdim : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
        simpa only [hdim, Fan.algebraicRealization_over] using
          (Φ).smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
      let : Smooth fX := (Φ).smooth_algebraicRealizationStructureMap hΦ
      let : IsNoetherian X := isNoetherian_of_finiteType fX
      let v := (T.picardMarking hT fX).symm (Additive.ofMul (pullback (k.inv ≫ g) H))
      let C := (Φ).hirzebruchPicardBasis b 1 hΦ r hr
      C.repr v.1 0 = δ ∧
      C.repr v.1 1 = δ - m (Fin.castAdd n (0 : Fin 1)) ∧
      (∀ j : Fin n, -v.2 j = m (j.natAdd 1)) ∧
      (0 < δ → δ < 3 * m (Fin.castAdd n (0 : Fin 1)) →
        0 < C.repr v.1 1 ∧
        hirzebruchSarkisovBidegree (C.repr v.1 1).toNat (∑ j, (-v.2 j).toNat) <
          planeSarkisovBidegree δ.toNat (∑ j, (m j).toNat)) := by
  intro w δ m
  have hU := (IsClosedPointTower.append_iff.mp hP).2
  obtain ⟨hσ, b, r, e, hr, he, hover, hE⟩ := exists_vertex_blowup_comparison d hi a
  let s := (Ψ).starSubdivisionAlong_isSubdivision hΨ (σ).property hσ
  have hc : (Φ).IsComplete := s.isComplete_iff.mpr (Fan.isComplete_projectiveSpace d hi)
  let : Nonempty (Φ).cones := hc.nonempty_cones
  let : SmoothOfRelativeDimension 2 fX := by
    have hdim : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
    simpa only [hdim, Fan.algebraicRealization_over] using
      (Φ).smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : Smooth fX := (Φ).smooth_algebraicRealizationStructureMap hΦ
  let : (W).Over S := ⟨(J).blowupToBase ≫ fP⟩
  let : e.hom.IsOver S := ⟨hover⟩
  let : (W).IsProjectiveOver ℂ := (J).isProjectiveOver_blowup_of_isNoetherianRing ℂ
  let : (X).IsProjectiveOver ℂ := Scheme.IsProjectiveOver.of_isClosedImmersion ℂ e.hom
  let : IsNoetherian X := isNoetherian_of_finiteType fX
  let R := U.transport e.symm
  have hT : IsClosedPointTower X R.tower := R.isLift.isClosedPointTower hU
  have hπ : R.iso.hom ≫ R.tower.toBase ≫ e.hom ≫ (J).blowupToBase =
      ((U₀).append U).toBase := by
    rw [← Category.assoc R.iso.hom, R.isLift.hom_toBase, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc, toBase_append, toBase_snoc, toBase_nil, Category.comp_id]
  have hf : (R.iso.inv ≫ g) ≫ fP = R.tower.toBase ≫ fX := by
    apply (cancel_epi R.iso.hom).mp
    rw [← Category.assoc R.iso.hom, Iso.hom_inv_id_assoc, hg, ← hπ]
    simp only [Category.assoc, hover]
  have hb : Scheme.BirationalOver (R.iso.inv ≫ g) (𝟙 P) := by
    refine Scheme.BirationalOver.trans (sY := g) ⟨.ofIso R.iso.symm, ?_⟩ hbir
    simp [Scheme.PartialIso.IsOver, Scheme.PartialIso.ofIso]
  refine ⟨hσ, b, r, hr, _, R.tower, hT, e, R.iso, R.isLift, he, ?_, hf, hb, ?_⟩
  · simpa only [← he] using hπ
  · intro _ _ _ _ _ v C
    obtain ⟨hd, hm, ht⟩ := hirzebruchOne_resolution_coordinates b hΦ hc r hr hT
      (isClosed_projectivePlane_vertex d hi a) e hover hE R.isLift.symm
      (R.iso.inv ≫ g) hf hb hP (by simpa only [Iso.symm_inv, Iso.hom_inv_id_assoc] using hg)
      (by simpa only [Iso.symm_inv, Iso.hom_inv_id_assoc] using hbir)
    simp only [Iso.symm_inv, Iso.hom_inv_id_assoc] at hd hm ht
    -- Read the shared comparison in the named coordinates before doing integer arithmetic.
    change δ = C.repr v.1 0 at hd
    change w.2 (Fin.castAdd n (0 : Fin 1)) = C.repr v.1 1 - C.repr v.1 0 at hm
    have hβ : C.repr v.1 1 = δ - m (Fin.castAdd n (0 : Fin 1)) := by
      dsimp only [m]
      omega
    refine ⟨hd.symm, hβ, fun j ↦ congrArg Neg.neg (ht j).symm, ?_⟩
    intro hδ hhigh
    have hsq := (hP.homaloidal_intersection_identities g hg hbir).1
    rw [classIntersectionNumber_projectivePlane] at hsq
    have hsq' : (∑ j, (m j) ^ 2) = δ ^ 2 - 1 := by
      simpa only [δ, m, w, neg_sq, toMul_ofMul, ofMul_toMul, ← pow_two] using hsq
    simpa only [hβ] using hirzebruchSarkisovBidegree_lt_plane_of_high_order hδ _ hsq' hhigh _ _

private theorem birationalOver_prepend_vertex {Y Z : Scheme} {n : ℕ}
    {T : BlowupTower P n Y} (hT : IsClosedPointTower P T) {A : Y.IdealSheafData}
    {q : Y} (hq : IsClosed ({q} : Set Y)) (hA : A = (Y.fromSpecResidueField q).ker)
    (e : A.blowup ≅ Z) {g : Y ⟶ P} (hg : Scheme.BirationalOver g (𝟙 P)) :
    Scheme.BirationalOver (e.inv ≫ A.blowupToBase ≫ g) (𝟙 P) := by
  let := hT.isIntegral fP
  let := hT.smoothOfRelativeDimension fP
  have hU : IsClosedPointTower Y (BlowupTower.nil.snoc A) := .snoc .nil q hq hA
  have : IsModification A.blowupToBase := by
    simpa only [toBase_snoc, toBase_nil, Category.comp_id] using
      hU.isModification_of_smoothOfRelativeDimension_two (T.toBase ≫ fP)
  obtain ⟨u, hu⟩ := IsModification.birationalOver A.blowupToBase
  have hπ : Scheme.BirationalOver (A.blowupToBase ≫ g) g :=
    ⟨u, by simpa only [Category.assoc, Category.comp_id] using congrArg (· ≫ g) hu⟩
  have he : Scheme.BirationalOver (e.inv ≫ A.blowupToBase ≫ g) (A.blowupToBase ≫ g) :=
    ⟨.ofIso e.symm, by simp [Scheme.PartialIso.IsOver, Scheme.PartialIso.ofIso]⟩
  exact he.trans (hπ.trans hg)

/-- Blow up a torus-fixed plane vertex absent from the projected centers of a specified
resolution, and transport the tower over the resulting Hirzebruch-one surface.
The comparison uses one extra blowup on the original resolved surface, at the inverse
image of the given vertex. It factors the original projection through the specified toric
subdivision, keeps all original centers in order over the plane, and preserves their total
exceptional coordinates. Both new ruling coordinates equal the old plane degree. -/
theorem exists_prepend_plane_vertex_blowup {Y : Scheme} {n : ℕ}
    {T : BlowupTower P n Y} (hT : IsClosedPointTower P T)
    (hp : p ∉ Set.range hT.baseCenter) (g : Y ⟶ P)
    (hg : g ≫ fP = T.toBase ≫ fP) (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let A := (J).comap T.toBase
    let v := (T.picardMarking hT fP).symm (Additive.ofMul (pullback g H))
    ∃ (q : Y) (hσ : (σ).val ≠ ⊥) (b : Basis (Fin 2) ℤ N) (r : Fin 4 ≃ (Φ).Ray)
      (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, ((1 : ℕ) : ℤ) • b 0 - b 1])
      (Z : Scheme) (U : BlowupTower X n Z) (hU : IsClosedPointTower X U) (k : A.blowup ≅ Z),
      let π := ((Ψ).starSubdivisionAlong_isSubdivision hΨ (σ).property hσ).toFanHom.algebraicMap ≫
        (D).hom
      let g' := k.inv ≫ A.blowupToBase ≫ g
      IsClosed ({q} : Set Y) ∧ T.toBase q = p ∧ A = (Y.fromSpecResidueField q).ker ∧
      k.hom ≫ U.toBase ≫ π = A.blowupToBase ≫ T.toBase ∧
      (∀ j, π (hU.baseCenter j) = hT.baseCenter j) ∧
      g' ≫ fP = U.toBase ≫ fX ∧ Scheme.BirationalOver g' (𝟙 P) ∧
      let hc : (Φ).IsComplete :=
        ((Ψ).starSubdivisionAlong_isSubdivision hΨ (σ).property hσ).isComplete_iff.mpr
          (Fan.isComplete_projectiveSpace d hi)
      let : Nonempty (Φ).cones := hc.nonempty_cones
      let : SmoothOfRelativeDimension 2 fX := by
        have hdim : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
        simpa only [hdim, Fan.algebraicRealization_over] using
          (Φ).smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
      let : Smooth fX := (Φ).smooth_algebraicRealizationStructureMap hΦ
      let : IsNoetherian X := isNoetherian_of_finiteType fX
      let w := (U.picardMarking hU fX).symm (Additive.ofMul (pullback g' H))
      let C := (Φ).hirzebruchPicardBasis b 1 hΦ r hr
      C.repr w.1 0 = degree v.1 ∧ C.repr w.1 1 = degree v.1 ∧ w.2 = v.2 := by
  intro A v
  obtain ⟨q, _, tail, e, hTail, hq, hqp, hA, he, hcenters, hmark⟩ :=
    hT.exists_prepend_closed_point_blowup (isClosed_projectivePlane_vertex d hi a) hp
  have hV : IsClosedPointTower P ((U₀).append tail) :=
    (IsClosedPointTower.nil.snoc p (isClosed_projectivePlane_vertex d hi a) rfl).append hTail
  have he' : e.hom ≫ tail.toBase ≫ (J).blowupToBase = A.blowupToBase ≫ T.toBase := he
  let g₁ := e.inv ≫ A.blowupToBase ≫ g
  have hg₁ : g₁ ≫ fP = ((U₀).append tail).toBase ≫ fP := by
    apply (cancel_epi e.hom).mp
    simp only [g₁, Category.assoc, Iso.hom_inv_id_assoc, hg, toBase_append, toBase_snoc,
      toBase_nil, Category.id_comp, reassoc_of% he']
  have hb₁ := birationalOver_prepend_vertex hT hq hA e hbir
  obtain ⟨hσ, b, r, hr, Z, U, hU, f, k, hLift, hf, hproj, hover, hb, hcoord⟩ :=
    exists_hirzebruch_resolution_of_plane_vertex d hi a hV g₁ hg₁ hb₁
  let π := ((Ψ).starSubdivisionAlong_isSubdivision hΨ (σ).property hσ).toFanHom.algebraicMap ≫
    (D).hom
  have hπ : k.hom ≫ U.toBase ≫ π = tail.toBase ≫ (J).blowupToBase := by
    simpa only [π, Category.assoc, toBase_append, toBase_snoc, toBase_nil, Category.comp_id]
      using hproj
  have hk : (e ≪≫ k).hom ≫ U.toBase ≫ π = A.blowupToBase ≫ T.toBase := by
    calc
      _ = e.hom ≫ (k.hom ≫ U.toBase ≫ π) := by simp only [Iso.trans_hom, Category.assoc]
      _ = e.hom ≫ tail.toBase ≫ (J).blowupToBase := congrArg (e.hom ≫ ·) hπ
      _ = _ := he'
  have hf' : f.hom ≫ (J).blowupToBase = π := hf
  have hbase : f.inv ≫ π = (J).blowupToBase := by
    rw [← hf', Iso.inv_hom_id_assoc]
  refine ⟨q, hσ, b, r, hr, Z, U, hU, e ≪≫ k, hq, hqp, hA, hk, ?_,
    by simpa only [g₁, Iso.trans_inv, Category.assoc] using hover,
    by simpa only [g₁, Iso.trans_inv, Category.assoc] using hb, ?_⟩
  · intro j
    rw [← hLift.hom_baseCenter hTail hU, ← Scheme.Hom.comp_apply, Iso.symm_hom, hbase, hcenters j]
  · have hv : (T.picardHom (v.1, v.2)).toMul = pullback g H := by
      rw [← picardMarking_apply T hT fP, Prod.mk.eta, LinearEquiv.apply_symm_apply]
      rfl
    have hw : (((U₀).append tail).picardMarking hV fP).symm (Additive.ofMul (pullback g₁ H)) =
        (v.1, Fin.addCases (fun _ : Fin 1 ↦ 0) v.2) := by
      apply (LinearEquiv.symm_apply_eq _).mpr
      apply Additive.toMul.injective
      rw [picardMarking_apply, ← hmark, hv]
      simp only [toMul_ofMul, g₁, pullback_comp, Category.assoc, A]
    -- The zero coefficient at the extra blowup drops out of the vertex formulas.
    rw [hw] at hcoord
    intro _ _ _ _ _ w C
    obtain ⟨h₀, h₁, h₂, -⟩ := hcoord
    simp only [Fin.addCases_left, Fin.addCases_right, neg_zero, sub_zero] at h₀ h₁ h₂
    simpa only [w, C, g₁, Iso.trans_inv, Category.assoc] using
      And.intro h₀ (And.intro h₁ (funext fun j ↦ neg_injective (h₂ j)))

end QPainleve.BlowupTower.IsClosedPointTower

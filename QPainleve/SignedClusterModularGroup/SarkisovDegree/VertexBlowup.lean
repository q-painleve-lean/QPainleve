/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.SectionContraction

import QPainleve.AlgebraicGeometry.Blowup.Projective.Global
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Sarkisov degree under a plane vertex blowup

When a specified plane resolution begins at a torus-fixed vertex, the first
blowup becomes the Hirzebruch-one base and the tail of the resolution transports
over that base. The new fiber degree is the plane degree minus the order at
the vertex. This is the torus-fixed plane case of Proposition 8.11 in
[Lutz's appendix to Hacking and Keating][HKL].

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
  refine ⟨hσ, b, r, hr, _, R.tower, hT, e, R.iso, R.isLift, ?_, hf, hb, ?_⟩
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

end QPainleve.BlowupTower.IsClosedPointTower

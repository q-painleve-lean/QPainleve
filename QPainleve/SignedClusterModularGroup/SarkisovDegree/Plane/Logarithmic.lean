/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Subdivision
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.VertexBlowup

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Modules.Differentials.PoleIdeal
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.Multiplicity

/-!
# Logarithmic Sarkisov decrease at a plane vertex

A high-order base point at a toric vertex gives a strictly smaller resolution
over the first Hirzebruch surface. Its projection on the original resolving
surface and its closed-point tower on the transported surface both carry the
original pole ideal. This allows the next logarithmic link to use the output
tower directly.

This is the plane-vertex case of Proposition 8.11 and the pole comparison in
the proof of Theorem 8.4 of [Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=71
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData TauCeti.SymmetricAlgebra
open TauCeti.Toric

namespace QPainleve.BlowupTower.IsClosedPointTower

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Plane" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "degree" => Module.Basis.picardTwistEquiv (Pi.basisFun ℂ (Fin 3))
local notation "s" => (Plane ↘ S)
local notation "X[" A "]" => Fan.algebraicRealization A
local notation "B[" A "," h "]" => Fan.boundaryIdeal A (Fan.IsComplete.nonempty_cones h)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (d : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i) (a : Option (Fin 2))

local notation "Π" => Fan.projectiveSpace d hi
local notation "hΠ" => Fan.isRegular_projectiveSpace d hi
local notation "hcΠ" => Fan.isComplete_projectiveSpace d hi
local notation "σ" => Fan.projectiveSpaceMaximalCone d hi a
local notation "Φ" => Fan.starSubdivisionAlong Π hΠ (Subtype.property σ)
local notation "hΦ" => Fan.isRegular_starSubdivisionAlong Π hΠ (Subtype.property σ)
local notation "π[" h "]" =>
  FanHom.algebraicMap (Fan.IsSubdivision.toFanHom
    (Fan.starSubdivisionAlong_isSubdivision Π hΠ (Subtype.property σ) h))
local notation "hcΦ[" h "]" =>
  Iff.mpr (Fan.IsSubdivision.isComplete_iff
    (Fan.starSubdivisionAlong_isSubdivision Π hΠ (Subtype.property σ) h)) hcΠ
local notation "eP" =>
  Fan.projectivePlaneIso d hi ≪≫ Module.Basis.polynomialProjIso (Pi.basisFun ℂ (Fin 3))
local notation "p" => (Fan.distinguishedPointHom Π σ ≫ Iso.hom eP) (IsLocalRing.closedPoint ℂ)
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis d) (Fintype.card_fin 2)

private theorem poleIdeal_of_vertex_projection {Y : Scheme} [IsIntegral Y] [Y.Over S]
    [SmoothOfRelativeDimension 2 (Y ↘ S)] (hσ : (σ).val ≠ ⊥)
    (q : Y ⟶ X[Φ]) (f : Y ⟶ Plane) [q.IsOver S] [f.IsOver S] [IsDominant q]
    (hq : q ≫ π[hσ] ≫ (eP).hom = f) (D : Y.IdealSheafData) :
    letI : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    ((B[Π,hcΠ]).comap (eP).inv).comap f = D * ramificationIdealSheaf ℂ f →
      (B[Φ,hcΦ[hσ]]).comap q = D * ramificationIdealSheaf ℂ q := by
  dsimp only
  intro hf
  let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : Nonempty (Π).cones := hcΠ.nonempty_cones
  let : Nonempty (Φ).cones := Fan.IsComplete.nonempty_cones hcΦ[hσ]
  let : SmoothOfRelativeDimension 2 (X[Π] ↘ S) := by
    simpa only [Fan.algebraicRealization_over, rankTwo] using
      (Π).smoothOfRelativeDimension_algebraicRealizationStructureMap hΠ
  let : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := by
    simpa only [Fan.algebraicRealization_over, rankTwo] using
      (Φ).smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let := Fan.projectivePlaneIso_trans_polynomialProjIso_hom_isOver d hi (Pi.basisFun ℂ (Fin 3))
  let : (eP).inv.IsOver S := inferInstance
  have h := comap_eq_mul_ramificationIdealSheaf_comp ℂ f (eP).inv 2
    (D := B[Π,hcΠ]) (P := (B[Π,hcΠ]).comap (eP).inv) (by simp only [
      ramificationIdealSheaf_eq_top_of_isOpenImmersion, mul_top]) hf
  have he : f ≫ (eP).inv = q ≫ π[hσ] := by
    rw [← hq, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h' : (B[Π,hcΠ]).comap (q ≫ π[hσ]) = D * ramificationIdealSheaf ℂ (q ≫ π[hσ]) :=
    (congrArg (B[Π,hcΠ]).comap he.symm).trans
      (h.trans (congrArg (D * ·) (ramificationIdealSheaf_congr ℂ he)))
  let J := (Π).starSubdivisionAlong_isSubdivision hΠ (σ).property hσ
  have hB := J.comap_boundaryIdeal_eq_mul_ramificationIdealSheaf hΠ hΦ hcΠ rankTwo
  have hCartier :=
    (J.isEffectiveCartier_ramificationIdealSheaf hΠ hΦ hcΠ rankTwo).comap_of_isDominant q
  exact (comap_eq_mul_ramificationIdealSheaf_comp_iff ℂ q π[hσ] 2 hCartier hB).mp h'

/-- A first center of order greater than one third of the plane degree over a specified
toric vertex gives a logarithmic Sarkisov decrease. The regular representative of the
vertex blowup is defined on the original resolution and has the same pole ideal there.
On the transported closed-point tower the pole ideal is its image under the resolving
isomorphism. The morphism to the target plane is transported by the same isomorphism.
The first Hirzebruch surface has fiber degree `d - m` for plane degree `d` and vertex
order `m`, and every remaining order retains its relative position. -/
theorem exists_sarkisov_decrease_of_logarithmic_plane_vertex
    {Y : Scheme} {n : ℕ} {T : BlowupTower Plane (n + 1) Y} (hT : IsClosedPointTower Plane T)
    (j : Fin (n + 1)) (hj : hT.baseCenter j = p) (hfirst : ∀ l < j, hT.baseCenter l ≠ p)
    (g : Y ⟶ Plane) (hg : g ≫ s = T.toBase ≫ s) (hbir : Scheme.BirationalOver g (𝟙 Plane))
    (D : Y.IdealSheafData) :
    letI : IsIntegral Y := hT.isIntegral s
    letI : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two s
    letI : Y.Over S := ⟨T.toBase ≫ s⟩
    letI : T.toBase.IsOver S := ⟨rfl⟩
    letI : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s
    letI : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let w := (T.picardMarking hT s).symm (Additive.ofMul (pullback g H))
    let δ := degree w.1
    let m := fun l ↦ -w.2 l
    ((B[Π,hcΠ]).comap (eP).inv).comap T.toBase = D * ramificationIdealSheaf ℂ T.toBase →
    δ < 3 * m j →
    ∃ (hσ : (σ).val ≠ ⊥) (b : Basis (Fin 2) ℤ N) (r : Fin 4 ≃ (Φ).Ray)
      (hr : (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, (1 : ℤ) • b 0 - b 1])
      (Z : Scheme) (U : BlowupTower X[Φ] n Z) (hU : IsClosedPointTower X[Φ] U) (k : Y ≅ Z),
      let q := k.hom ≫ U.toBase
      letI : Nonempty (Π).cones := hcΠ.nonempty_cones
      letI : Nonempty (Φ).cones := Fan.IsComplete.nonempty_cones hcΦ[hσ]
      letI : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := by
        simpa only [rankTwo, Fan.algebraicRealization_over] using
          (Φ).smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
      letI : Smooth (X[Φ] ↘ S) := SmoothOfRelativeDimension.smooth 2 _
      letI : IsNoetherian X[Φ] := isNoetherian_of_finiteType (X[Φ] ↘ S)
      letI : Z.Over S := ⟨U.toBase ≫ X[Φ] ↘ S⟩
      letI : U.toBase.IsOver S := ⟨rfl⟩
      letI : SmoothOfRelativeDimension 2 (Z ↘ S) := hU.smoothOfRelativeDimension (X[Φ] ↘ S)
      letI : Smooth (Z ↘ S) := SmoothOfRelativeDimension.smooth 2 _
      ∃ hqOver : q.IsOver S,
        letI := hqOver
        (X[Φ]).IsProjectiveOver ℂ ∧
        q ≫ π[hσ] ≫ (eP).hom = T.toBase ∧
        T.toBase.toRationalMap.comp
          ((eP).inv.toRationalMap.comp ((Π).denseTorusPartialIso Φ).toRationalMap) =
          q.toRationalMap ∧
        (B[Φ,hcΦ[hσ]]).comap q = D * ramificationIdealSheaf ℂ q ∧
        (B[Φ,hcΦ[hσ]]).comap U.toBase = D.comap k.inv * ramificationIdealSheaf ℂ U.toBase ∧
        (k.inv ≫ g) ≫ s = U.toBase ≫ X[Φ] ↘ S ∧
        Scheme.BirationalOver (k.inv ≫ g) (𝟙 Plane) ∧
        let v := (U.picardMarking hU (X[Φ] ↘ S)).symm (Additive.ofMul (pullback (k.inv ≫ g) H))
        let C := (Φ).hirzebruchPicardBasis b 1 hΦ r hr
        C.repr v.1 0 = δ ∧ C.repr v.1 1 = δ - m j ∧
        (∀ l : Fin n, -v.2 l = m (j.succAbove l)) ∧
        0 < C.repr v.1 1 ∧
        hirzebruchSarkisovBidegree (C.repr v.1 1).toNat (∑ l, (-v.2 l).toNat) <
          planeSarkisovBidegree δ.toNat (∑ l, (m l).toNat) := by
  dsimp only
  intro hpole hhigh
  let : IsIntegral Y := hT.isIntegral s
  let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two s
  let : Y.Over S := ⟨T.toBase ≫ s⟩
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s
  let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  obtain ⟨hσ, b, r, hr, Z, U, hU, k, hq, hrat, hg', hbir', hcoords⟩ :=
    hT.exists_sarkisov_decrease_of_plane_vertex d hi a j hj hfirst g hg hbir
  let := hcΠ.nonempty_cones
  let := Fan.IsComplete.nonempty_cones hcΦ[hσ]
  let := Fan.projectivePlaneIso_trans_polynomialProjIso_hom_isOver d hi (Pi.basisFun ℂ (Fin 3))
  let : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := by
    simpa only [rankTwo, Fan.algebraicRealization_over] using
      (Φ).smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : Smooth (X[Φ] ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsNoetherian X[Φ] := isNoetherian_of_finiteType (X[Φ] ↘ S)
  let : Z.Over S := ⟨U.toBase ≫ X[Φ] ↘ S⟩
  let : U.toBase.IsOver S := ⟨rfl⟩
  let : SmoothOfRelativeDimension 2 (Z ↘ S) := hU.smoothOfRelativeDimension (X[Φ] ↘ S)
  let : Smooth (Z ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let q := k.hom ≫ U.toBase
  let : IsModification U.toBase :=
    hU.isModification_of_smoothOfRelativeDimension_two (X[Φ] ↘ S)
  let : IsDominant q := inferInstanceAs (IsDominant (k.hom ≫ U.toBase))
  have hqOver : q.IsOver S := ⟨by
    have he := (reassoc_of% hq) s
    simpa only [q, Category.assoc, comp_over (eP).hom S, comp_over π[hσ] S,
      comp_over T.toBase S] using he⟩
  let := hqOver
  have hqPole := poleIdeal_of_vertex_projection d hi a hσ q T.toBase hq D hpole
  let : k.hom.IsOver S := ⟨(Category.assoc _ _ _).symm.trans (comp_over q S)⟩
  let : k.inv.IsOver S := inferInstance
  have htransport := comap_eq_mul_ramificationIdealSheaf_comp ℂ k.inv q 2
    (Q := D.comap k.inv) hqPole
    (by simp only [ramificationIdealSheaf_eq_top_of_isOpenImmersion, mul_top])
  have he : k.inv ≫ q = U.toBase := by
    simp only [q, Iso.inv_hom_id_assoc]
  have hUPole : (B[Φ,hcΦ[hσ]]).comap U.toBase =
      D.comap k.inv * ramificationIdealSheaf ℂ U.toBase :=
    (congrArg (B[Φ,hcΦ[hσ]]).comap he.symm).trans
      (htransport.trans (congrArg (D.comap k.inv * ·) (ramificationIdealSheaf_congr ℂ he)))
  obtain ⟨hδ, -, -⟩ := hT.plane_degree_eq_one_or_exists_high_baseCenter g hg hbir
  obtain ⟨h₁, h₂, h₃, hlt⟩ := hcoords
  exact ⟨hσ, b, r, hr, Z, U, hU, k, hqOver,
    Fan.isProjectiveOver_projectivePlane_vertex_starSubdivision d hi a,
    hq, hrat, hqPole, hUPole, hg', hbir', h₁, h₂, h₃, hlt hδ hhigh⟩

end QPainleve.BlowupTower.IsClosedPointTower

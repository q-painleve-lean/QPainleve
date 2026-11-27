/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.BaseChange.FunctionField
public import QPainleve.Geometry.Toric.Fan.Picard.Homaloidal
public import QPainleve.Geometry.Toric.Fan.Picard.Quadric
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.ElementaryTransform

import QPainleve.SignedClusterModularGroup.SarkisovDegree.Multiplicity

/-!
# Sarkisov degree under exchange of the quadric rulings

The toric exchange of rulings transports a specified resolution over the quadric.
In the transported resolution the fiber and section coefficients of the line class
are interchanged, while the ordered exceptional coefficients are preserved.
The no-high-multiplicity case therefore strictly decreases the Sarkisov bidegree.

See Lutz's appendix to Hacking and Keating,
[*Homological mirror symmetry for log Calabi–Yau surfaces*, proof of Theorem 8.4](
https://arxiv.org/abs/2005.05010v3).
-/

public section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra
open TauCeti.Toric

namespace QPainleve.BlowupTower.IsClosedPointTower

variable (K : Type) [Field K] [IsAlgClosed K]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

local notation "S" => Spec (CommRingCat.of K)
local notation "X" => (Φ.finiteFanScheme K)
local notation "f" => (X ↘ S)
local notation "P" => Proj (homogeneousSubmodule K (Fin 3 → K))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle K (Fin 3 → K) 1)
local notation "Pic" => Additive (LineBundleClass X)
local notation "C" => Fan.hirzebruchPicardBasis K b 0 hΦ r hr
local notation "E" => Fan.quadricRulingExchange b hΦ hc r hr
local notation "τ" => FanHom.finiteFanSchemeHom K (FanEquiv.toFanHom (E))
local notation "Q(" T ")" => BlowupTower.transport T (asIso τ)
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)

variable {Y : Scheme.{0}} {n : ℕ} {T : BlowupTower (Φ.finiteFanScheme K) n Y}
  (hT : IsClosedPointTower (Φ.finiteFanScheme K) T)

variable [(Φ.finiteFanScheme K).IsProjectiveOver K]

/-- If all base multiplicities of a resolved quadric-to-plane map are at most half
the positive fiber degree, transport by the ruling exchange strictly decreases the
Sarkisov bidegree. The same lift identifies the new resolving morphism with the
original one and the new projection with the original projection followed by the
regular toric ruling exchange. -/
theorem rulingExchange_bidegree_lt_of_no_high_multiplicity
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f)
    (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : SmoothOfRelativeDimension 2 f := by
      rw [Fan.finiteFanScheme_over K]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ
    let q := Q(T)
    let hQ := q.isLift.isClosedPointTower hT
    let g' := q.iso.inv ≫ g
    let v : Pic × (Fin n → ℤ) := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    let w : Pic × (Fin n → ℤ) :=
      (q.tower.picardMarking hQ f).symm (Additive.ofMul (pullback g' H))
    let d := (C).repr v.1 1
    let M := (∑ j, -v.2 j).toNat
    0 < d → (∀ j, 0 ≤ -v.2 j ∧ 2 * (-v.2 j) ≤ d) →
      q.iso.hom ≫ g' = g ∧ q.iso.hom ≫ q.tower.toBase = T.toBase ≫ τ ∧
      g' ≫ (P ↘ S) = q.tower.toBase ≫ f ∧
      Scheme.BirationalOver g' (𝟙 P) ∧ 0 < (C).repr w.1 1 ∧
      hirzebruchSarkisovBidegree ((C).repr w.1 1).toNat (∑ j, -w.2 j).toNat <
        hirzebruchSarkisovBidegree d.toNat M := by
  intro hSmooth q hQ g' v w d M hd hm
  let : SmoothOfRelativeDimension 2 f := hSmooth
  have hg' : q.iso.hom ≫ g' = g := q.iso.hom_inv_id_assoc g
  refine ⟨hg', q.isLift.hom_toBase, ?_, ?_, ?_⟩
  · apply (cancel_epi q.iso.hom).mp
    rw [← Category.assoc, hg', hg, ← Category.assoc, q.isLift.hom_toBase,
      Category.assoc, asIso_hom, comp_over τ S]
  · have he : Scheme.BirationalOver (q.iso.inv ≫ g) g :=
      ⟨Scheme.PartialIso.ofIso q.iso.symm, by
        simp [Scheme.PartialIso.IsOver, Scheme.PartialIso.ofIso, ← Scheme.topIso_hom]⟩
    exact he.trans hbir
  · have ⟨hsq, hsum⟩ :=
      hT.homaloidal_intersection_identities_of_hirzebruch K b 0 hΦ hc r hr g hg hbir
    simp only [Nat.cast_zero, zero_mul, sub_zero] at hsq hsum
    have hlt := two_mul_lt_of_hirzebruch_homaloidal (e := 0) (a := (C).repr v.1 0) hd hm
      (by simpa only [neg_sq, zero_mul, sub_zero] using hsq) (by simpa only [sub_zero] using hsum)
    have hbase := (hT.picardMarking_symm_rulingExchange K b hΦ hc r hr (pullback g H)).1
    have hW : w = (q.tower.picardMarking hQ f).symm
        (Additive.ofMul (pullback q.iso.inv (pullback g H))) := by
      simp only [w, g', pullback_comp]
    have hdegree : (C).repr w.1 1 = (C).repr v.1 0 := by
      rw [hW]
      simpa only [Equiv.swap_apply_right] using hbase (1 : Fin 2)
    rw [hdegree]
    have hnonneg : 0 ≤ ∑ j, v.2 j ^ 2 := Finset.sum_nonneg fun j _ ↦ sq_nonneg (v.2 j)
    have hpos : 0 < 2 * (C).repr v.1 0 * (C).repr v.1 1 := by
      dsimp only [v] at hnonneg ⊢
      omega
    refine ⟨pos_of_mul_pos_right (pos_of_mul_pos_left hpos hd.le) (by norm_num), ?_⟩
    rw [Prod.Lex.lt_iff, ofLex_hirzebruchSarkisovBidegree, ofLex_hirzebruchSarkisovBidegree]
    apply Or.inl
    omega

end QPainleve.BlowupTower.IsClosedPointTower

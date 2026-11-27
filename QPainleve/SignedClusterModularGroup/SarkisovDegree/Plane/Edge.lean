/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Picard
public import QPainleve.Geometry.Toric.Fan.Picard.Quadric
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.Link
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.SmoothSection

import QPainleve.Geometry.Toric.Fan.Mutation.Hirzebruch
import QPainleve.Geometry.Toric.Fan.Picard.Homaloidal

/-!
# Sarkisov degree at a smooth point of a plane edge

After the opposite vertex has been blown up, the edge is the section of
self-intersection one on the first Hirzebruch surface. Mutation at the edge
center followed by the quadric ruling exchange gives a specified resolution
with smaller Sarkisov degree. The same resolved surface represents both
partial composites, with their total exceptional coordinates tracked.

This is the smooth-edge plane case of Proposition 8.11 in
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra TauCeti.Toric

open TauCeti.Toric.Fan

namespace QPainleve.BlowupTower.IsClosedPointTower

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ Fan.Ray.primitiveGenerator (r j)) = ![b 0, b 1, -b 0, (1 : ℤ) • b 0 - b 1])
  (ρ : Φ.Ray) (c : k₀ˣ)

local notation "S" => Spec (CommRingCat.of k₀)
local notation "X" => (Φ.finiteFanScheme k₀)
local notation "f" => (X ↘ S)
local notation "P" => Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle k₀ (Fin 3 → k₀) 1)
local notation "v" => Fan.Ray.primitiveGenerator ρ
local notation "hv" => Fan.Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Fan.Ray.hull_primitiveGenerator_mem ρ
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "center" =>
  Fan.Ray.binomialCenter ρ k₀ rankTwo (b.detDualEquiv_self v)
    (Fan.Ray.surjective_detCharacter ρ b) c
local notation "C" => Fan.hirzebruchPicardBasis k₀ b 1 hΦ r hr

variable (hρ : ρ = r 2)

-- Ray zero is opposite to the pivot on ray two.
local notation "hOpp" =>
  Eq.mpr (congrArg (fun u : N ↦ hull ℝ {i u} ∈ Φ.cones)
    (Eq.trans (congrArg (fun p : Φ.Ray ↦ -Fan.Ray.primitiveGenerator p) hρ)
      (Eq.trans (congrArg Neg.neg (congrFun hr 2))
        (Eq.trans (neg_neg (b 0)) (Eq.symm (congrFun hr 0))))))
    (Fan.Ray.hull_primitiveGenerator_mem (r 0))

local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "X'" => Fan.finiteFanScheme k₀ Ψ
local notation "f'" => (X' ↘ S)
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hOpp) hΦ
local notation "hc'" => Iff.mpr (Φ.isComplete_mutationFan_iff b hv hp hOpp) hc
local notation "s" => r.trans (Φ.mutationFanRayEquiv b hv hp hOpp)
local notation "μ" =>
  Scheme.PartialMap.toRationalMap (Φ.mutationPartialMap k₀ b (c : k₀) hv hp hOpp)
local notation "C'(" d "," hd ")" => Fan.hirzebruchPicardBasis k₀ d 0 hΨ s hd

variable {n : ℕ} {W : Scheme.{0}} {T : BlowupTower (Φ.finiteFanScheme k₀) (n + 1) W}
  (hT : IsClosedPointTower (Φ.finiteFanScheme k₀) T) (j : Fin (n + 1))

local notation "k" => Fin.castAdd n (0 : Fin 1)
local notation "reorder(" x ")" =>
  (Fin.addCases (fun _ : Fin 1 ↦ x j) (x ∘ Fin.succAbove j) : Fin (1 + n) → ℤ)
local notation "newCoeffs(" d "," x ")" => Function.update (reorder(x)) k (-d - x j)

private theorem edgeLink_coordinates
    (d : Basis (Fin 2) ℤ N)
    (hd : (fun l : Fin 4 ↦ ((s) l).primitiveGenerator) =
      ![d 0, d 1, -d 0, (0 : ℤ) • d 0 - d 1])
    {Z : Scheme} (U : BlowupTower X' (1 + n) Z) (e : W ≅ Z)
    (hmark :
      let : Nonempty (Ψ).cones := (hc').nonempty_cones
      ∀ (a β : ℤ) (x : Fin (n + 1) → ℤ),
        pullback e.inv (T.picardHom (a • C 0 + β • C 1, x)).toMul =
          (U.picardHom ((a + x j) • C'(d,hd) 0 + β • C'(d,hd) 1,
            newCoeffs(β,x))).toMul)
    (hU : IsClosedPointTower X' U) (L : LineBundleClass W) :
    let : SmoothOfRelativeDimension 2 f :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
    let : Nonempty (Ψ).cones := (hc').nonempty_cones
    let : SmoothOfRelativeDimension 2 f' :=
      Eq.mp (congrArg (fun d ↦ SmoothOfRelativeDimension d f') rankTwo)
        ((Ψ).smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΨ)
    let x := (T.picardMarking hT f).symm (Additive.ofMul L)
    let τ := ((Fan.quadricRulingExchange d hΨ hc' s hd).toFanHom.finiteFanSchemeHom k₀)
    let q := U.transport (asIso τ)
    let hQ := q.isLift.isClosedPointTower hU
    let y := (q.tower.picardMarking hQ f').symm
      (Additive.ofMul (pullback (e ≪≫ q.iso).inv L))
    (C'(d,hd)).repr y.1 0 = (C).repr x.1 1 ∧
    (C'(d,hd)).repr y.1 1 = (C).repr x.1 0 + x.2 j ∧
    y.2 = newCoeffs((C).repr x.1 1,x.2) := by
  intro hs hne hs' x τ q hQ y
  let := hs
  let := hne
  let := hs'
  let a := (C).repr x.1 0
  let β := (C).repr x.1 1
  have hx : a • C 0 + β • C 1 = x.1 := by
    simpa only [Fin.sum_univ_two, a, β] using (C).sum_repr x.1
  have hL : (T.picardHom x).toMul = L := by
    rw [← picardMarking_apply T hT f, LinearEquiv.apply_symm_apply, toMul_ofMul]
  let z := (U.picardMarking hU f').symm (Additive.ofMul (pullback e.inv L))
  have hz : z = ((a + x.2 j) • C'(d,hd) 0 + β • C'(d,hd) 1, newCoeffs(β,x.2)) := by
    apply (LinearEquiv.symm_apply_eq _).mpr
    apply Additive.toMul.injective
    rw [toMul_ofMul, picardMarking_apply]
    simpa only [hx, Prod.mk.eta, hL] using hmark a β x.2
  have hcoord : (C'(d,hd)).repr z.1 0 = a + x.2 j ∧ (C'(d,hd)).repr z.1 1 = β := by
    rw [hz]
    constructor <;>
      norm_num only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Basis.repr_self,
        Finsupp.single_apply, smul_eq_mul, Fin.zero_ne_one, (by decide : (1 : Fin 2) ≠ 0),
        ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add]
  have hswap : (∀ l : Fin 2, (C'(d,hd)).repr y.1 l =
      (C'(d,hd)).repr z.1 (Equiv.swap 0 1 l)) ∧ y.2 = z.2 := by
    simpa only [y, z, Iso.trans_inv, pullback_comp] using
      hU.picardMarking_symm_rulingExchange k₀ d hΨ hc' s hd (pullback e.inv L)
  refine ⟨(hswap.1 0).trans ?_, (hswap.1 1).trans ?_, hswap.2.trans (congrArg Prod.snd hz)⟩
  · simpa only [Equiv.swap_apply_left] using hcoord.2
  · simpa only [Equiv.swap_apply_right] using hcoord.1

private theorem edgeMutation_marking
    (hj : hT.baseCenter j = center (IsLocalRing.closedPoint k₀))
    (hfirst : ∀ l < j, hT.baseCenter l ≠ center (IsLocalRing.closedPoint k₀))
    (d : Basis (Fin 2) ℤ N) (hd₀ : d 0 = b 0) (hd₁ : d 1 = b 1 - b 0)
    (hd : (fun l : Fin 4 ↦ ((s) l).primitiveGenerator) =
      ![d 0, d 1, -d 0, (0 : ℤ) • d 0 - d 1]) :
    let : SmoothOfRelativeDimension 2 f :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
    let : IsIntegral W := hT.isIntegral f
    let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two f
    let : Nonempty (Ψ).cones := (hc').nonempty_cones
    ∃ (Z : Scheme) (U : BlowupTower X' (1 + n) Z) (e : W ≅ Z),
      IsClosedPointTower X' U ∧
      e.hom ≫ U.toBase ≫ f' = T.toBase ≫ f ∧
      T.toBase.toRationalMap.comp μ = (e.hom ≫ U.toBase).toRationalMap ∧
      ∀ (a β : ℤ) (x : Fin (n + 1) → ℤ),
        pullback e.inv (T.picardHom (a • C 0 + β • C 1, x)).toMul =
          (U.picardHom ((a + x j) • C'(d,hd) 0 + β • C'(d,hd) 1, newCoeffs(β,x))).toMul := by
  intro hs hW hπ hne
  let := hs
  let := hW
  let := hπ
  let := hne
  obtain ⟨Z, U, e, hU, hover, he, -, -, -, hmark⟩ :=
    (ρ).exists_sarkisov_decrease_of_smooth_section_center b hOpp c hΦ hT j hj hfirst
  refine ⟨Z, U, e, hU, hover, he, fun a β x ↦ ?_⟩
  let q := Fan.Ray.ofPrimitiveGenerator (ρ).isPrimitiveGenerator.isPrimitive.neg hOpp
  have hq : q = r 0 := by
    apply Fan.Ray.primitiveGenerator_injective
    rw [Fan.Ray.primitiveGenerator_ofPrimitiveGenerator, hρ, congrFun hr 2, congrFun hr 0]
    exact neg_neg _
  have hρ' : (s) 2 = (Φ.mutationFanRayEquiv b hv hp hOpp) ρ :=
    congrArg (Φ.mutationFanRayEquiv b hv hp hOpp) hρ.symm
  have hF : mutationFiberClass k₀ b ρ hΦ = mutationFiberClass k₀ b (r 2) hΦ :=
    congrArg (fun p ↦ mutationFiberClass k₀ b p hΦ) hρ
  have hfiber := mutationFiberClass_of_opposite_section k₀ b hΦ r 1 0
    (by simpa only [zero_smul, sub_zero] using hr)
  have hfiber' : mutationFiberClass k₀ b ((Φ.mutationFanRayEquiv b hv hp hOpp) ρ) hΨ =
      (Ψ).rayChartDivisorToPicard k₀ hΨ (Pi.single ((s) 1) 1) := by
    rw [← hρ']
    exact mutationFiberClass_of_opposite_section k₀ b hΨ s 0 1
      (by simpa only [hd₀, hd₁, one_smul] using hd)
  dsimp only [q] at hq
  have h := (hmark false a β x).1
  simpa only [Bool.false_eq_true, ↓reduceIte, add_zero, hq, hF, hfiber, hfiber',
    Fan.hirzebruchPicardBasis_apply_zero, Fan.hirzebruchPicardBasis_apply_one,
    Fan.rayChartDivisorToPicard_single, one_smul, Equiv.trans_apply] using h

include hc in
private theorem edge_bidegree_lt [(X).IsProjectiveOver k₀]
    (g : W ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f)
    (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : SmoothOfRelativeDimension 2 f :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
    let x := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    let a := (C).repr x.1 0
    let β := (C).repr x.1 1
    let M := (a - β).toNat + ∑ l, (-x.2 l).toNat
    0 < a → a < 3 * (-x.2 j) → ∀ M' : ℕ,
      0 < a + x.2 j ∧
      hirzebruchSarkisovBidegree (a + x.2 j).toNat M' < planeSarkisovBidegree a.toNat M := by
  intro hs x a β M ha hj M'
  let := hs
  have hsq : ∑ l, (x.2 l) ^ 2 = 2 * a * β - β ^ 2 - 1 := by
    simpa only [Nat.cast_one, one_mul] using
      (hT.homaloidal_intersection_identities_of_hirzebruch k₀ b 1 hΦ hc r hr g hg hbir).1
  let m : Fin ((n + 1) + 1) → ℤ := Fin.cons (a - β) (fun l : Fin (n + 1) ↦ -x.2 l)
  have hm : ∑ l, (m l) ^ 2 = a ^ 2 - 1 := by
    rw [Fin.sum_univ_succ]
    simp only [m, Fin.cons_zero, Fin.cons_succ, neg_sq]
    nlinarith only [hsq]
  simpa only [m, Fin.cons_succ, sub_neg_eq_add] using
    hirzebruchSarkisovBidegree_lt_plane_of_high_order ha j.succ hm
      (by simpa only [m, Fin.cons_succ] using hj) M M'

include hρ in
/-- After blowing up the opposite vertex of a plane boundary edge, a resolution
with a proper center on the strict transform of the edge transports across the
elementary mutation and the quadric ruling exchange. Both partial composites on
the original resolved surface are regular, and the resolving map to the plane is
transported along the resulting isomorphism.

If the prepared ruling coordinates are `(a, β)` and the selected center has order
`m`, the final ruling coordinates are `(β, a - m)`, the order at the reverse
center is `β - m`, and all other exceptional coefficients retain their relative
order. For `a > 0` and `m > a / 3` the final bidegree is strictly smaller than the
plane bidegree, which counts the opposite vertex with order `a - β`. -/
theorem exists_quadric_resolution_of_plane_edge_link [(X).IsProjectiveOver k₀]
    (hj : hT.baseCenter j = center (IsLocalRing.closedPoint k₀))
    (hfirst : ∀ l < j, hT.baseCenter l ≠ center (IsLocalRing.closedPoint k₀))
    (g : W ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f)
    (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : SmoothOfRelativeDimension 2 f :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
    let : IsIntegral W := hT.isIntegral f
    let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two f
    let : Nonempty (Ψ).cones := (hc').nonempty_cones
    let : SmoothOfRelativeDimension 2 f' :=
      Eq.mp (congrArg (fun d ↦ SmoothOfRelativeDimension d f') rankTwo)
        ((Ψ).smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΨ)
    let x := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    let a := (C).repr x.1 0
    let β := (C).repr x.1 1
    ∃ (d : Basis (Fin 2) ℤ N)
      (hd : (fun l : Fin 4 ↦ ((s) l).primitiveGenerator) =
        ![d 0, d 1, -d 0, (0 : ℤ) • d 0 - d 1])
      (Z : Scheme) (U : BlowupTower X' (1 + n) Z) (hU : IsClosedPointTower X' U)
      (e : W ≅ Z) (p : W ⟶ X'),
      let τ := ((Fan.quadricRulingExchange d hΨ hc' s hd).toFanHom.finiteFanSchemeHom k₀)
      let g' := e.inv ≫ g
      T.toBase.toRationalMap.comp μ = p.toRationalMap ∧
      p ≫ f' = T.toBase ≫ f ∧
      e.hom ≫ U.toBase = p ≫ τ ∧
      e.hom ≫ g' = g ∧
      g' ≫ (P ↘ S) = U.toBase ≫ f' ∧
      Scheme.BirationalOver g' (𝟙 P) ∧
      let y := (U.picardMarking hU f').symm (Additive.ofMul (pullback g' H))
      (C'(d,hd)).repr y.1 0 = β ∧
      (C'(d,hd)).repr y.1 1 = a + x.2 j ∧
      y.2 k = -β - x.2 j ∧
      (∀ l : Fin n, y.2 (l.natAdd 1) = x.2 (j.succAbove l)) ∧
      (0 < a → a < 3 * (-x.2 j) →
        0 < (C'(d,hd)).repr y.1 1 ∧
        hirzebruchSarkisovBidegree ((C'(d,hd)).repr y.1 1).toNat (∑ l, (-y.2 l).toNat) <
          planeSarkisovBidegree a.toNat ((a - β).toNat + ∑ l, (-x.2 l).toNat)) := by
  intro hs hW hπ hne hs' x a β
  let := hs
  let := hW
  let := hπ
  let := hne
  let := hs'
  obtain ⟨d, hd₀, hd₁, hd⟩ :=
    (ρ).mutationFan_hirzebruch_ray_generators b hOpp 1 r hr false hρ
  have hd' : (fun l : Fin 4 ↦ ((s) l).primitiveGenerator) =
      ![d 0, d 1, -d 0, (0 : ℤ) • d 0 - d 1] := hd
  obtain ⟨Z, U, e, hU, hover, he, hmark⟩ :=
    edgeMutation_marking k₀ b hΦ hc r hr ρ c hρ hT j hj hfirst d hd₀
      (by simpa only [Bool.false_eq_true, ↓reduceIte] using hd₁) hd'
  let τ := ((Fan.quadricRulingExchange d hΨ hc' s hd').toFanHom.finiteFanSchemeHom k₀)
  let q := U.transport (asIso τ)
  let hQ := q.isLift.isClosedPointTower hU
  let p := e.hom ≫ U.toBase
  let E := e ≪≫ q.iso
  have hproj : E.hom ≫ q.tower.toBase = p ≫ τ := by
    simp only [E, Iso.trans_hom, Category.assoc, q.isLift.hom_toBase, asIso_hom, p]
  have hg' : (E.inv ≫ g) ≫ (P ↘ S) = q.tower.toBase ≫ f' := by
    apply (cancel_epi E.hom).mp
    rw [← Category.assoc E.hom, Iso.hom_inv_id_assoc, hg,
      ← Category.assoc E.hom, hproj, Category.assoc, comp_over τ S]
    exact hover.symm
  have hb : Scheme.BirationalOver (E.inv ≫ g) (𝟙 P) := by
    refine Scheme.BirationalOver.trans (sY := g) ⟨.ofIso E.symm, ?_⟩ hbir
    simp [Scheme.PartialIso.IsOver, Scheme.PartialIso.ofIso]
  refine ⟨d, hd', _, q.tower, hQ, E, p, he, hover, hproj, E.hom_inv_id_assoc g, hg', hb, ?_⟩
  intro y
  have hcoords : (C'(d,hd')).repr y.1 0 = β ∧ (C'(d,hd')).repr y.1 1 = a + x.2 j ∧
      y.2 = newCoeffs(β,x.2) := by
    simpa only [y, E, pullback_comp] using
      edgeLink_coordinates k₀ b hΦ hc r hr ρ hρ hT j d hd' U e hmark hU (pullback g H)
  rw [hcoords.2.2]
  refine ⟨hcoords.1, hcoords.2.1, Function.update_self .., ?_, fun ha hj' ↦ ?_⟩
  · intro l
    have hl : l.natAdd 1 ≠ k := by simp [Fin.ext_iff, Fin.val_natAdd]
    simp only [Function.update_of_ne hl, Fin.addCases_right, Function.comp_apply]
  · rw [hcoords.2.1]
    exact edge_bidegree_lt k₀ b hΦ hc r hr hT j g hg hbir ha hj' _

end QPainleve.BlowupTower.IsClosedPointTower

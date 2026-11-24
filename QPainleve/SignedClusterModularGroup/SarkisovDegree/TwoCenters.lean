/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.OppositeSection
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Quadric

import QPainleve.Geometry.Toric.Fan.Mutation.Center
import QPainleve.SignedClusterModularGroup.SarkisovDegree.QuadricFiber
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Decrease
import TauCeti.Data.Fin.Basic
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic

/-!
# The two smooth centers of the quadric Sarkisov block

The selected centers on opposite sections of a quadric lie on distinct fibers
of the mutation ruling. After the first elementary transformation, the other
center remains the first occurrence of that point on the opposite section of the
Hirzebruch surface. The second transformation and the final ruling exchange
produce a quadric with smaller Sarkisov degree.

This is the block with two smooth centers in Case B of Proposition 8.11 in
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=72
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone TauCeti.Toric
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular)
  (hc : Φ.IsComplete) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

local notation "ρ" => r 0
local notation "v" => Fan.Ray.primitiveGenerator (ρ)
local notation "hv" => Fan.Ray.primitiveGenerator_ne_zero (ρ)
local notation "hp" => Fan.Ray.hull_primitiveGenerator_mem (ρ)
local notation "hop" => Fan.hull_neg_primitiveGenerator_mem_of_hirzebruch b 0 r hr
local notation "Ψ" => Φ.mutationFan b hv hp hop
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hop) hΦ
local notation "hcΨ" => Iff.mpr (Φ.isComplete_mutationFan_iff b hv hp hop) hc
local notation "rayEquiv" => Φ.mutationFanRayEquiv b hv hp hop
local notation "s" => r.trans (rayEquiv)
local notation "hs" => Fan.Ray.mutationFan_hirzebruch_ray_generators_of_section_zero
  (ρ) b hop 0 r hr rfl
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X" => Φ.algebraicRealization
local notation "X'" => Fan.algebraicRealization Ψ
local notation "fX" => (X ↘ S)
local notation "fX'" => (X' ↘ S)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "fP" => (P ↘ S)
local notation "C" => Fan.hirzebruchPicardBasis b 0 hΦ r hr
local notation "C'" => Fan.hirzebruchPicardBasis b 1 hΨ s hs
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "center[" u "," c "]" =>
  (Fan.Ray.binomialCenter u rankTwo (b.detDualEquiv_self (Fan.Ray.primitiveGenerator u))
    (Fan.Ray.surjective_detCharacter u b) c)
local notation "pt" => IsLocalRing.closedPoint ℂ
local notation "I[" c "]" => Fan.Ray.mutationSourceCenterIdeal b (ρ) c
local notation "J[" c "]" => Fan.Ray.mutationTargetCenterIdeal b (ρ) hop c
local notation "G[" c "]" => Fan.Ray.mutationBlowupIso b (ρ) hop c
local notation "reverseRay" => Φ.mutationFanCenterRays b (fun _ : Unit ↦ r 0) () hop ()
local notation "compOpen[" c "]" => Φ.mutationComplement b
  (Φ.detCharacter_nonneg_or_nonpos b hv hp hop) (c : ℂ)

variable {n : ℕ} {Y : Scheme}

local notation "first" => Fin.castAdd n (0 : Fin 1)

local notation "targetOpen[" c "]" => Fan.mutationComplement (Ψ) b
  (Φ.mutationDetCharacter_nonneg_or_nonpos b hv hp hop) (c : ℂ)

private theorem oppositeCenter_mutationComplement (c d : ℂˣ) (hcd : d * c ≠ 1) :
    ∃ x : (compOpen[c]).toScheme,
      (compOpen[c]).ι x = center[r 2,d] pt ∧
      (targetOpen[c]).ι ((Φ.mutationComplementIso b (c : ℂ) hv hp hop).hom x) =
        center[s 2,d] pt := by
  have hv₀ : v = b 0 := congrFun hr 0
  have hzero : (r 2).primitiveGenerator = -v := hv₀ ▸ congrFun hr 2
  have hdet : b.det ![(r 2).primitiveGenerator, v] = 0 := by
    rw [hzero, ← b.detDualEquiv_apply, map_neg, LinearMap.neg_apply, b.detDualEquiv_self, neg_zero]
  have hne : (r 2).primitiveGenerator ≠ v := by
    intro h
    obtain ⟨f, hf⟩ := TauCeti.isPrimitive_def.mp (r 0).isPrimitiveGenerator.isPrimitive
    have he := congrArg (fun u ↦ f u) (hzero.symm.trans h)
    simp [hf] at he
  obtain ⟨p, hp₀, hp₁⟩ := Fan.exists_binomialCenter_mutationComplementIso b (r 2)
    hv hp hop c d (r 0).isPrimitiveGenerator.isPrimitive
    (fun h ↦ (hne h).elim) (fun _ ↦ hcd)
  refine ⟨p pt, congrArg (fun f : Spec (.of ℂ) ⟶ X ↦ f pt) hp₀, ?_⟩
  have heq := congrArg (fun f : Spec (.of ℂ) ⟶ X' ↦ f pt) hp₁
  simp only [hdet, max_self, zpow_zero, mul_one] at heq
  exact heq

private theorem first_oppositeCenter_of_mutation
    {T : BlowupTower X (n + 1) Y} (hT : IsClosedPointTower X T)
    {Z : Scheme} {U : BlowupTower X' (1 + n) Z} (hU : IsClosedPointTower X' U)
    (c d : ℂˣ) {j : Fin (n + 1)} {l : Fin n} (hcd : d * c ≠ 1)
    (hl : hT.baseCenter (j.succAbove l) = center[r 2,d] pt)
    (hlfirst : ∀ k < j.succAbove l, hT.baseCenter k ≠ center[r 2,d] pt)
    (hreverse : hU.baseCenter first = center[reverseRay,c⁻¹] pt)
    (hcenters : ∀ k : Fin n, ∃ p : (I[c]).blowup,
      (I[c]).blowupToBase p = hT.baseCenter (j.succAbove k) ∧
      (J[c]).blowupToBase ((G[c]).hom p) = hU.baseCenter (k.natAdd 1)) :
    hU.baseCenter (l.natAdd 1) = center[s 2,d] pt ∧
      ∀ k < l.natAdd 1, hU.baseCenter k ≠ center[s 2,d] pt := by
  obtain ⟨x, hx, hx'⟩ := oppositeCenter_mutationComplement b r hr c d hcd
  obtain ⟨p, hp₀, hp₁⟩ := hcenters l
  have htarget := hp₁.symm.trans (((r 0).mutationBlowupIso_apply_over_complement b hop c p x
     (hp₀.trans (hl.trans hx.symm))).trans hx')
  refine ⟨htarget, fun k hk ↦ ?_⟩
  induction k using Fin.addCases with
  | left k =>
    have hk₀ : k = 0 := Subsingleton.elim _ _
    subst k
    rw [hreverse, ← hx']
    intro heq
    have hmem : center[reverseRay,c⁻¹] pt ∈ (J[c]).support := by
      rw [Fan.Ray.mutationTargetCenterIdeal_eq]
      exact (center[reverseRay,c⁻¹]).range_subset_ker_support ⟨pt, rfl⟩
    have hdis := (Scheme.IdealSheafData.comap_eq_top_iff (J[c]) (targetOpen[c]).ι).mp
      ((r 0).mutationTargetCenterIdeal_comap_complement b hop c)
    have hout : (targetOpen[c]).ι ((Φ.mutationComplementIso b (c : ℂ) hv hp hop).hom x) ∉
        (J[c]).support := by
      have h : (Φ.mutationComplementIso b (c : ℂ) hv hp hop).hom x ∈
          (targetOpen[c]).ι ⁻¹ᵁ (J[c]).support.compl := by
        rw [hdis]
        trivial
      exact h
    exact hout (heq ▸ hmem)
  | right k =>
    obtain ⟨q, hq₀, hq₁⟩ := hcenters k
    intro heq
    have hqp := ((r 0).mutationBlowupIso_projected_eq_iff b hop c
      (q := p) (by rw [hp₀, hl, ← hx]; exact x.property)).mp
        (hq₁.trans (heq.trans (htarget.symm.trans hp₁.symm)))
    exact hlfirst _ (Fin.strictMono_succAbove _ ((Fin.natAdd_lt_natAdd_iff 1).mp hk))
      (hq₀.symm.trans (hqp.trans (hp₀.trans hl)))

local notation "m" => LinearMap.toAddMonoidHom (b.detDualEquiv v)
local notation "hru" => Φ.detCharacter_nonneg_or_nonpos b hv hp hop
local notation "f" => Φ.characterRuling m hru
local notation "rulingPoint[" c "]" =>
  projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 0 (-(↑c⁻¹ : ℂ))

include hr in
private theorem quadric_opposite_center_on_pivot_fiber (c : ℂˣ) :
    center[r 2,c⁻¹] ≫ f = rulingPoint[c] := by
  have hv₀ : v = b 0 := congrFun hr 0
  have hv₂ : (r 2).primitiveGenerator = -v := hv₀ ▸ congrFun hr 2
  have hχ : (b.detDualEquiv (r 2).primitiveGenerator).toAddMonoidHom = -m := by
    simp only [hv₂, map_neg]
    rfl
  have hz : m (r 2).primitiveGenerator = 0 := by
    simp [hv₂, -Basis.detDualEquiv_apply, Basis.detDualEquiv_self]
  have hneg := (r 2).binomialCenter_neg_inv rankTwo hz ((r 0).surjective_detCharacter b) c
  have he : center[r 2,c⁻¹] = (r 2).binomialCenter rankTwo hz
      ((r 0).surjective_detCharacter b) c := by
    convert hneg using 1
    congr 1
  rw [he]
  exact (r 2).binomialCenter_comp_characterRuling hru rankTwo hz
    ((r 0).surjective_detCharacter b) c

local notation "swappedBasis" => b.reindex (Equiv.swap 0 1)
local notation "swappedRays" =>
  Equiv.trans (Equiv.trans (Equiv.swap (0 : Fin 4) 1) (Equiv.swap 2 3)) r

include hr in
private theorem quadric_swapped_generators :
    (fun j ↦ ((swappedRays) j).primitiveGenerator) =
      ![(swappedBasis) 0, (swappedBasis) 1, -(swappedBasis) 0,
        (0 : ℤ) • (swappedBasis) 0 - (swappedBasis) 1] := by
  have hj (j : Fin 4) := congrFun hr j
  funext j
  fin_cases j <;>
    simp [Equiv.swap_apply_def, Basis.reindex_apply, Equiv.trans_apply, hj]

private theorem quadric_mutationRuling_ne_of_two_high_orders
    [Φ.algebraicRealization.IsProjectiveOver ℂ]
    {T : BlowupTower X (n + 1) Y} (hT : IsClosedPointTower X T)
    (g : Y ⟶ P) (hg : g ≫ fP = T.toBase ≫ fX) (hbir : Scheme.BirationalOver g (𝟙 P))
    {j l : Fin (n + 1)} (hjl : j ≠ l) (c : ℂˣ)
    (hj : hT.baseCenter j = center[r 0,c] pt)
    (hjfirst : ∀ k < j, hT.baseCenter k ≠ hT.baseCenter j)
    (hlfirst : ∀ k < l, hT.baseCenter k ≠ hT.baseCenter l) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 fX := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let x : Additive (LineBundleClass X) × (Fin (n + 1) → ℤ) :=
      (T.picardMarking hT fX).symm (Additive.ofMul (pullback g H))
    let β := (C).repr x.1 0
    let orders := fun k ↦ -x.2 k
    (∀ k, 0 ≤ orders k) →
    β < 2 * orders j → orders j ≤ β →
    β < 2 * orders l → orders l ≤ β →
    (∀ k, k ≠ j → k ≠ l → 2 * orders k ≤ β) →
    f (hT.baseCenter j) ≠ f (hT.baseCenter l) := by
  intro hcones hdim x β orders hn hjhigh hjle hlhigh hlle hsmall
  let := hcones
  let := hdim
  let bs := (swappedBasis)
  let rs := (swappedRays)
  have hrs := quadric_swapped_generators b r hr
  let Calt := Fan.hirzebruchPicardBasis bs 0 hΦ rs hrs
  have hC : Calt = (C).reindex (Equiv.swap 0 1) := by
    have he : Calt.repr.symm = ((C).reindex (Equiv.swap 0 1)).repr.symm := by
      apply (Finsupp.basisSingleOne : Basis (Fin 2) ℤ (Fin 2 →₀ ℤ)).ext'
      intro k
      simp only [Finsupp.coe_basisSingleOne, Basis.repr_symm_single_one]
      fin_cases k <;> simp [Calt, rs, Basis.reindex_apply, Equiv.swap_apply_def, Equiv.trans_apply]
    exact Basis.repr_injective (congrArg LinearEquiv.symm he)
  have hβ : (Fan.hirzebruchPicardBasis bs 0 hΦ rs hrs).repr
      ((T.picardMarking hT fX).symm (Additive.ofMul (pullback g H))).1 1 = β := by
    have he : Calt.repr x.1 1 = β := by
      simp only [hC, Basis.repr_reindex_apply, Equiv.symm_swap, Equiv.swap_apply_right, β]
    exact he
  have hv₀ : v = b 0 := congrFun hr 0
  have hm : (bs.coord 0).toAddMonoidHom = m := by
    apply congrArg LinearMap.toAddMonoidHom
    apply b.ext
    intro k
    fin_cases k <;>
      simp [bs, hv₀, Basis.coord_apply,
        -Basis.detDualEquiv_apply, Basis.detDualEquiv_self, Basis.detDualEquiv_apply_basis_zero_one]
  have hf : Φ.characterRuling (bs.coord 0).toAddMonoidHom
      (Φ.nonneg_or_nonpos_quadric_transverse_character bs rs hrs) = f := by congr
  have ht : Φ.characterRuling (bs.coord 0).toAddMonoidHom
      (Φ.nonneg_or_nonpos_quadric_transverse_character bs rs hrs) (hT.baseCenter j) ∈
        Set.range (rulingPoint[c]) := by
    rw [hf, hj]
    exact ⟨pt, (congrArg (fun k : Spec (.of ℂ) ⟶ projectiveLine ℂ ↦ k pt)
      ((r 0).binomialCenter_comp_characterRuling hru rankTwo
        (b.detDualEquiv_self v) ((r 0).surjective_detCharacter b) c)).symm⟩
  have hne := hT.ne_quadric_transverse_ruling_of_two_high_base_orders
    bs hΦ hc rs hrs g hg hbir hjl hjfirst hlfirst (-c⁻¹)
      (by simpa only [Units.val_neg] using ht)
  dsimp only at hne
  rw [hβ, hf] at hne
  exact hne hn hjhigh hjle hlhigh hlle hsmall

include hc in
private theorem quadric_pair_fiber_degree
    [Φ.algebraicRealization.IsProjectiveOver ℂ]
    [Nonempty Φ.cones] [SmoothOfRelativeDimension 2 fX]
    {T : BlowupTower X (n + 1) Y} (hT : IsClosedPointTower X T)
    (g : Y ⟶ P) (hg : g ≫ fP = T.toBase ≫ fX) (hbir : Scheme.BirationalOver g (𝟙 P))
    {j l : Fin (n + 1)} (hjl : j ≠ l) :
    let x : Additive (LineBundleClass X) × (Fin (n + 1) → ℤ) :=
      (T.picardMarking hT fX).symm (Additive.ofMul (pullback g H))
    let β := (C).repr x.1 0
    let α := (C).repr x.1 1
    let orders := fun k ↦ -x.2 k
    β < 2 * orders j → orders j ≤ β → β < 2 * orders l → orders l ≤ β →
    (∀ k, k ≠ j → k ≠ l → 0 ≤ orders k ∧ 2 * orders k ≤ β) →
    0 < β + α - orders j - orders l ∧ β + α - orders j - orders l < β := by
  intro x β α orders hjhigh hjle hlhigh hlle hsmall
  have ⟨hsq, hsum⟩ := hT.homaloidal_intersection_identities_of_hirzebruch b 0 hΦ hc r hr g hg hbir
  have hβ : 0 < β := by omega
  apply quadric_sarkisov_degree_decrease_of_pair hβ hjl ?_ ?_ hjhigh.le hjle hlhigh.le hlle hsmall
  · have hmul : 2 * α * β = 2 * β * α := mul_right_comm ..
    simpa only [orders, α, β, x, neg_sq, Nat.cast_zero, zero_mul, sub_zero, hmul] using hsq
  · simpa only [orders, α, β, x, Nat.cast_zero, sub_zero, add_comm (2 * β)] using hsum

local notation "σ" => s 2
local notation "w" => Fan.Ray.primitiveGenerator (σ)
local notation "hw" => Fan.Ray.primitiveGenerator_ne_zero (σ)
local notation "hwPos" => Fan.Ray.hull_primitiveGenerator_mem (σ)
local notation "hwOpp" => Fan.hull_neg_primitiveGenerator_mem_of_hirzebruch_section_two b 1 s hs
local notation "Ω" => Fan.mutationFan (Ψ) b hw hwPos hwOpp
local notation "hΩ" => Iff.mpr (Fan.isRegular_mutationFan_iff (Ψ) b hw hwPos hwOpp) hΨ
local notation "hcΩ" => Iff.mpr (Fan.isComplete_mutationFan_iff (Ψ) b hw hwPos hwOpp) hcΨ
local notation "t" => Equiv.trans s (Fan.mutationFanRayEquiv (Ψ) b hw hwPos hwOpp)
local notation "X''" => Fan.algebraicRealization Ω
local notation "fX''" => (X'' ↘ S)

local notation "mut₀[" c "]" =>
  Scheme.PartialMap.toRationalMap (Φ.mutationPartialMap b (c : ℂ) hv hp hop)
local notation "mut₁[" d "]" =>
  Scheme.PartialMap.toRationalMap (Fan.mutationPartialMap (Ψ) b (d : ℂ) hw hwPos hwOpp)
local notation "τ[" a "," ht "]" =>
  FanHom.algebraicMap (FanEquiv.toFanHom (Fan.quadricRulingExchange a hΩ hcΩ t ht))

/-- The two smooth high-order centers on opposite sections of a quadric give a
degree-decreasing block on the original resolving surface. The input quadric is
written in the frame of the exchanged ruling. The projections after each
mutation and after the final ruling exchange are regular on that surface.

If the original fiber and section coordinates are `(β, α)` in this frame and
the two base orders are `m₁, m₂`, the final coordinates after exchanging the
rulings are `(α, β + α - m₁ - m₂)`. The exceptional coordinates of the new
reverse pivots are `m₂ - α` followed by `m₁ - α`. The other exceptional
coordinates retain their original relative order. -/
theorem exists_quadric_resolution_of_two_smooth_high_centers
    [Φ.algebraicRealization.IsProjectiveOver ℂ]
    {T : BlowupTower X (n + 2) Y} (hT : IsClosedPointTower X T)
    (g : Y ⟶ P) (hg : g ≫ fP = T.toBase ≫ fX) (hbir : Scheme.BirationalOver g (𝟙 P))
    (c d : ℂˣ) (j : Fin (n + 2)) (l : Fin (n + 1))
    (hj : hT.baseCenter j = center[r 0,c] pt)
    (hl : hT.baseCenter (j.succAbove l) = center[r 2,d] pt)
    (hjfirst : ∀ k < j, hT.baseCenter k ≠ center[r 0,c] pt)
    (hlfirst : ∀ k < j.succAbove l, hT.baseCenter k ≠ center[r 2,d] pt) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : Nonempty (Ψ).cones := (hcΨ).nonempty_cones
    let : Nonempty (Ω).cones := (hcΩ).nonempty_cones
    let : SmoothOfRelativeDimension 2 fX := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : SmoothOfRelativeDimension 2 fX' := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo ▸ (Ψ).smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
    let : SmoothOfRelativeDimension 2 fX'' := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo ▸ (Ω).smoothOfRelativeDimension_algebraicRealizationStructureMap hΩ
    let : IsIntegral Y := hT.isIntegral fX
    let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two fX
    let x : Additive (LineBundleClass X) × (Fin (n + 2) → ℤ) :=
      (T.picardMarking hT fX).symm (Additive.ofMul (pullback g H))
    let β := (C).repr x.1 0
    let α := (C).repr x.1 1
    let orders := fun k ↦ -x.2 k
    β < 2 * orders j → orders j ≤ β →
    β < 2 * orders (j.succAbove l) → orders (j.succAbove l) ≤ β →
    (∀ k, k ≠ j → k ≠ j.succAbove l → 0 ≤ orders k ∧ 2 * orders k ≤ β) →
    ∃ (a : Basis (Fin 2) ℤ N)
      (ht : (fun k ↦ ((t) k).primitiveGenerator) = ![a 0, a 1, -a 0, (0 : ℤ) • a 0 - a 1])
      (Z : Scheme) (U : BlowupTower X' (1 + (n + 1)) Z) (hU : IsClosedPointTower X' U)
      (e : Y ≅ Z) (W : Scheme) (V₀ : BlowupTower X'' (1 + (1 + n)) W)
      (hV : IsClosedPointTower X'' V₀) (k : Z ≅ W),
      let q := V₀.transport (asIso τ[a,ht])
      let hQ := q.isLift.isClosedPointTower hV
      let p₁ := e.hom ≫ U.toBase
      let p₂ := (e ≪≫ k).hom ≫ V₀.toBase
      let p₃ := (e ≪≫ k ≪≫ q.iso).hom ≫ q.tower.toBase
      let g' := (e ≪≫ k ≪≫ q.iso).inv ≫ g
      let : IsModification U.toBase := hU.isModification_of_smoothOfRelativeDimension_two fX'
      let : IsDominant p₁ := inferInstance
      T.toBase.toRationalMap.comp mut₀[c] = p₁.toRationalMap ∧
      p₁.toRationalMap.comp mut₁[d] = p₂.toRationalMap ∧
      p₃ = p₂ ≫ τ[a,ht] ∧
      g' ≫ fP = q.tower.toBase ≫ fX'' ∧
      Scheme.BirationalOver g' (𝟙 P) ∧
      let y := (q.tower.picardMarking hQ fX'').symm (Additive.ofMul (pullback g' H))
      let C'' := Fan.hirzebruchPicardBasis a 0 hΩ t ht
      C''.repr y.1 0 = α ∧
      C''.repr y.1 1 = β + α - orders j - orders (j.succAbove l) ∧
      y.2 (Fin.castAdd (1 + n) (0 : Fin 1)) = orders (j.succAbove l) - α ∧
      y.2 ((Fin.castAdd n (0 : Fin 1)).natAdd 1) =
        orders j - α ∧
      (∀ u : Fin n, y.2 (u.natAdd 1 |>.natAdd 1) = x.2 (j.succAbove (l.succAbove u))) ∧
      0 < C''.repr y.1 1 ∧
      hirzebruchSarkisovBidegree (C''.repr y.1 1).toNat (∑ u, -y.2 u).toNat <
        hirzebruchSarkisovBidegree β.toNat (∑ u, orders u).toNat := by
  intro hX hX' hX'' hdim hdim' hdim'' hY hmod x β α orders hjhigh hjle hlhigh hlle hsmall
  let := hX
  let := hX'
  let := hX''
  let := hdim
  let := hdim'
  let := hdim''
  let := hY
  let := hmod
  -- Separate the two fibers before transporting the second pivot.
  have hjl := (Fin.succAbove_ne j l).symm
  have hn (u : Fin (n + 2)) : 0 ≤ orders u := by
    rcases eq_or_ne u j with rfl | hu
    · omega
    rcases eq_or_ne u (j.succAbove l) with rfl | hu'
    · omega
    exact (hsmall u hu hu').1
  have hne := quadric_mutationRuling_ne_of_two_high_orders b hΦ hc r hr hT g hg hbir hjl c hj
    (by simpa only [hj] using hjfirst) (by simpa only [hl] using hlfirst)
    hn hjhigh hjle hlhigh hlle (fun u huj hul ↦ (hsmall u huj hul).2)
  have hdc : d * c ≠ 1 := by
    intro hdc
    have hd := mul_eq_one_iff_eq_inv.mp hdc
    apply hne
    rw [hj, hl, hd]
    exact congrArg (fun a : Spec (.of ℂ) ⟶ projectiveLine ℂ ↦ a pt)
      (((r 0).binomialCenter_comp_characterRuling hru rankTwo
        (b.detDualEquiv_self v) ((r 0).surjective_detCharacter b) c).trans
        (quadric_opposite_center_on_pivot_fiber b r hr c).symm)
  obtain ⟨Z, U, hU, e, hmap, hg₁, hbir₁, hrev, hcenters, ha, hb, hm, hmrest⟩ :=
    hT.exists_hirzebruchOne_resolution_of_quadric_mutation b hΦ hc r hr g hg hbir c j hj hjfirst
  obtain ⟨hL, hLfirst⟩ :=
    first_oppositeCenter_of_mutation b r hr hT hU c d hdc hl hlfirst hrev hcenters
  obtain ⟨a, ht, W, V₀, hV, k, hnext, _, hover, hcoord⟩ :=
    hU.exists_quadric_resolution_of_hirzebruchOne_mutation b hΨ hcΨ s hs d
      (l.natAdd 1) hL hLfirst
  -- Pull the two link projections and the plane resolution back to the original surface.
  refine ⟨a, ht, Z, U, hU, e, W, V₀, hV, k, ?_⟩
  intro q hQ p₁ p₂ p₃ g' hmodU hdom
  let := hmodU
  let := hdom
  let : IsIntegral Z := hU.isIntegral fX'
  have hcomp : p₁.toRationalMap.comp mut₁[d] = p₂.toRationalMap := by
    have he := congrArg (e.hom.toRationalMap.comp ·) hnext
    rw [← Scheme.RationalMap.comp_assoc] at he
    simpa only [p₁, p₂, Iso.trans_hom, Category.assoc, Scheme.RationalMap.comp_toRationalMap,
      Scheme.Hom.toRationalMap_compHom] using he
  have hthird : p₃ = p₂ ≫ τ[a,ht] := by
    simp only [p₃, p₂, Iso.trans_hom, Category.assoc, q.isLift.hom_toBase, asIso_hom]
  have hg' : g' ≫ fP = q.tower.toBase ≫ fX'' := by
    dsimp only [g']
    apply (cancel_epi (e ≪≫ k ≪≫ q.iso).hom).mp
    rw [← Category.assoc, Iso.hom_inv_id_assoc]
    have he := congrArg (e.hom ≫ ·) hg₁
    have hk := congrArg (e.hom ≫ ·) hover.symm
    simpa only [Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc] using he.trans hk
  have hbir' : Scheme.BirationalOver g' (𝟙 P) :=
    Scheme.BirationalOver.trans (sY := g)
      ⟨.ofIso (e ≪≫ k ≪≫ q.iso).symm,
        by simp [g', Scheme.PartialIso.IsOver, Scheme.PartialIso.ofIso]⟩ hbir
  refine ⟨hmap, hcomp, hthird, hg', hbir', ?_⟩
  -- Read the marked line class through both links in the order of the retained centers.
  intro y C''
  have h₂ := hcoord (pullback (e.inv ≫ g) H)
  dsimp only at h₂
  simp only [Iso.trans_inv, pullback_comp, Category.assoc] at h₂
  obtain ⟨h₂a, h₂b, h₂m, h₂rest⟩ := h₂
  have hy : C''.repr y.1 1 = β + α - orders j - orders (j.succAbove l) := by
    simpa only [y, g', C'', Iso.trans_inv, Category.assoc, ha, hmrest, orders, sub_neg_eq_add]
      using h₂b
  have hd : 0 < β + α - orders j - orders (j.succAbove l) ∧
      β + α - orders j - orders (j.succAbove l) < β :=
    quadric_pair_fiber_degree b hΦ hc r hr hT g hg hbir hjl hjhigh hjle hlhigh hlle hsmall
  refine ⟨by simpa only [y, g', C'', Iso.trans_inv, Category.assoc, hb] using h₂a,
    hy, ?_, ?_, ?_, hy ▸ hd.1, ?_⟩
  · have he : y.2 (Fin.castAdd (1 + n) (0 : Fin 1)) = -α - x.2 (j.succAbove l) := by
      simp only [hb, hmrest] at h₂m
      dsimp only [y, g']
      simp only [Iso.trans_inv, Category.assoc]
      convert h₂m using 2
    rw [he]
    dsimp only [orders]
    ring
  · simpa only [y, g', Iso.trans_inv, Category.assoc, Fin.natAdd_succAbove_castAdd, hm,
      orders, sub_eq_add_neg, add_comm] using h₂rest (Fin.castAdd n (0 : Fin 1))
  · intro u
    simpa only [y, g', Iso.trans_inv, Category.assoc, Fin.natAdd_succAbove_natAdd, hmrest] using
      h₂rest (u.natAdd 1)
  · have hlt := hd.2
    simp only [Prod.Lex.lt_iff, ofLex_hirzebruchSarkisovBidegree, hy]
    exact Or.inl (by omega)

end QPainleve.BlowupTower.IsClosedPointTower

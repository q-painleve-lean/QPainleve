/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.OppositeSection
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Quadric.Basic

import QPainleve.Geometry.Toric.Fan.Mutation.Center
import QPainleve.Geometry.Toric.Fan.Mutation.Logarithmic
import QPainleve.Geometry.Toric.Fan.Mutation.PointTower
import QPainleve.Geometry.Toric.Fan.Picard.Quadric
import TauCeti.Data.Fin.Basic
import QPainleve.AlgebraicGeometry.Modules.Differentials.PoleIdeal
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic

/-!
# The two smooth centers of the quadric Sarkisov block

The selected centers on opposite sections of a quadric lie on distinct fibers
of the mutation ruling. After the first elementary transformation, the other
center remains the first occurrence of that point on the opposite section of the
Hirzebruch surface. The second transformation and the final ruling exchange
produce a quadric with the specified new Picard coordinates.

This is the block with two smooth centers in Case B of Proposition 8.11 in
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=72
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone TauCeti.Toric
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra
open Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

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
local notation "S" => Spec (CommRingCat.of k₀)
local notation "X" => (Φ.finiteFanScheme k₀)
local notation "X'" => Fan.finiteFanScheme k₀ Ψ
local notation "fX" => (X ↘ S)
local notation "fX'" => (X' ↘ S)
local notation "P" => Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle k₀ (Fin 3 → k₀) 1)
local notation "fP" => (P ↘ S)
local notation "C" => Fan.hirzebruchPicardBasis k₀ b 0 hΦ r hr
local notation "C'" => Fan.hirzebruchPicardBasis k₀ b 1 hΨ s hs
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "B[" Δ "," hcΔ "]" => Fan.toricBoundaryIdeal k₀ Δ (Fan.IsComplete.nonempty_cones hcΔ)
local notation "center[" u "," c "]" =>
  (Fan.Ray.binomialCenter u k₀ rankTwo (b.detDualEquiv_self (Fan.Ray.primitiveGenerator u))
    (Fan.Ray.surjective_detCharacter u b) c)
local notation "pt" => IsLocalRing.closedPoint k₀
local notation "I[" c "]" => Fan.Ray.mutationSourceCenterIdeal b (ρ) c
local notation "J[" c "]" => Fan.Ray.mutationTargetCenterIdeal b (ρ) hop c
local notation "G[" c "]" => Fan.Ray.mutationBlowupIso b (ρ) hop c
local notation "reverseRay" => Φ.mutationFanCenterRays b (fun _ : Unit ↦ r 0) () hop ()
local notation "compOpen[" c "]" => Φ.mutationComplement b
  (Φ.detCharacter_nonneg_or_nonpos b hv hp hop) (c : k₀)

variable {n : ℕ} {Y : Scheme}

local notation "first" => Fin.castAdd n (0 : Fin 1)

local notation "targetOpen[" c "]" => Fan.mutationComplement (Ψ) b
  (Φ.mutationDetCharacter_nonneg_or_nonpos b hv hp hop) (c : k₀)

omit [IsAlgClosed k₀] in
private theorem oppositeCenter_mutationComplement (c d : k₀ˣ) (hcd : d * c ≠ 1) :
    ∃ x : (compOpen[c]).toScheme,
      (compOpen[c]).ι x = center[r 2,d] pt ∧
      (targetOpen[c]).ι ((Φ.mutationComplementIso b (c : k₀) hv hp hop).hom x) =
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
  refine ⟨p pt, congrArg (fun f : Spec (.of k₀) ⟶ X ↦ f pt) hp₀, ?_⟩
  have heq := congrArg (fun f : Spec (.of k₀) ⟶ X' ↦ f pt) hp₁
  simp only [hdet, max_self, zpow_zero, mul_one] at heq
  exact heq

omit [IsAlgClosed k₀] in
private theorem first_oppositeCenter_of_mutation
    {T : BlowupTower X (n + 1) Y} (hT : IsClosedPointTower X T)
    {Z : Scheme} {U : BlowupTower X' (1 + n) Z} (hU : IsClosedPointTower X' U)
    (c d : k₀ˣ) {j : Fin (n + 1)} {l : Fin n} (hcd : d * c ≠ 1)
    (hl : hT.baseCenter (j.succAbove l) = center[r 2,d] pt)
    (hlfirst : ∀ k < j.succAbove l, hT.baseCenter k ≠ center[r 2,d] pt)
    (hreverse : hU.baseCenter first = center[reverseRay,c⁻¹] pt)
    (hcenters : ∀ k : Fin n, ∃ p : (I[c]).blowup,
      (I[c]).blowupToBase p = hT.baseCenter (j.succAbove k) ∧
      (J[c]).blowupToBase ((G[c]).hom p) = hU.baseCenter (k.natAdd 1)) :
    hU.baseCenter (l.natAdd 1) = center[s 2,d] pt ∧
      ∀ k < l.natAdd 1, hU.baseCenter k ≠ center[s 2,d] pt := by
  obtain ⟨x, hx, hx'⟩ := oppositeCenter_mutationComplement k₀ b r hr c d hcd
  have hmem : hT.baseCenter (j.succAbove l) ∈ compOpen[c] := by
    rw [hl, ← hx]
    exact x.property
  obtain ⟨htarget, hfirst⟩ :=
    (r 0).baseCenter_of_mutation_of_mem_complement k₀ b hop c hT hU j l hreverse hcenters hmem
  have heq : (⟨hT.baseCenter (j.succAbove l), hmem⟩ : (compOpen[c]).toScheme) = x :=
    Subtype.ext (hl.trans hx.symm)
  have hImage := htarget.trans (heq.symm ▸ hx')
  refine ⟨hImage, ?_⟩
  simpa only [hImage] using hfirst (by simpa only [hl] using hlfirst)

local notation "m" => LinearMap.toAddMonoidHom (b.detDualEquiv v)
local notation "hru" => Φ.detCharacter_nonneg_or_nonpos b hv hp hop
local notation "f" => Φ.characterRuling k₀ m hru
local notation "rulingPoint[" c "]" =>
  projectiveLine.polynomialPoint k₀ (RingHom.id k₀) 0 (-(↑c⁻¹ : k₀))

include hr in
omit [IsAlgClosed k₀] in
private theorem quadric_opposite_center_on_pivot_fiber (c : k₀ˣ) :
    center[r 2,c⁻¹] ≫ f = rulingPoint[c] := by
  have hv₀ : v = b 0 := congrFun hr 0
  have hv₂ : (r 2).primitiveGenerator = -v := hv₀ ▸ congrFun hr 2
  have hχ : (b.detDualEquiv (r 2).primitiveGenerator).toAddMonoidHom = -m := by
    simp only [hv₂, map_neg]
    rfl
  have hz : m (r 2).primitiveGenerator = 0 := by
    simp [hv₂, -Basis.detDualEquiv_apply, Basis.detDualEquiv_self]
  have hneg := (r 2).binomialCenter_neg_inv k₀ rankTwo hz ((r 0).surjective_detCharacter b) c
  have he : center[r 2,c⁻¹] = (r 2).binomialCenter k₀ rankTwo hz
      ((r 0).surjective_detCharacter b) c := by
    convert hneg using 1
    congr 1
  rw [he]
  exact (r 2).binomialCenter_comp_characterRuling k₀ hru rankTwo hz
    ((r 0).surjective_detCharacter b) c

local notation "swappedBasis" => b.reindex (Equiv.swap 0 1)
local notation "swappedRays" =>
  Equiv.trans (Equiv.trans (Equiv.swap (0 : Fin 4) 1) (Equiv.swap 2 3)) r

private theorem quadric_mutationRuling_ne_of_lt_sum_first_base_orders
    [(Φ.finiteFanScheme k₀).IsProjectiveOver k₀]
    {T : BlowupTower X (n + 1) Y} (hT : IsClosedPointTower X T)
    (g : Y ⟶ P) (hg : g ≫ fP = T.toBase ≫ fX)
    {j l : Fin (n + 1)} (hjl : j ≠ l) (c : k₀ˣ)
    (hj : hT.baseCenter j = center[r 0,c] pt)
    (hjfirst : ∀ k < j, hT.baseCenter k ≠ hT.baseCenter j)
    (hlfirst : ∀ k < l, hT.baseCenter k ≠ hT.baseCenter l) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 fX := by
      rw [Fan.finiteFanScheme_over k₀]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
    let x : Additive (LineBundleClass X) × (Fin (n + 1) → ℤ) :=
      (T.picardMarking hT fX).symm (Additive.ofMul (pullback g H))
    let α := (C).repr x.1 1
    let orders := fun k ↦ -x.2 k
    α < orders j + orders l →
    f (hT.baseCenter j) ≠ f (hT.baseCenter l) := by
  intro hcones hdim x α orders hsum
  let := hcones
  let := hdim
  let bs := (swappedBasis)
  let rs := (swappedRays)
  have hrs := Fan.quadric_swapped_generators b r hr
  have hα : (Fan.hirzebruchPicardBasis k₀ bs 0 hΦ rs hrs).repr x.1 0 = α := by
    rw [Fan.hirzebruchPicardBasis_quadric_swap k₀ b hΦ r hr, Basis.repr_reindex_apply]
    rfl
  have hv₀ : v = b 0 := congrFun hr 0
  have hm : (bs.coord 0).toAddMonoidHom = m := by
    apply congrArg LinearMap.toAddMonoidHom
    apply b.ext
    intro k
    fin_cases k <;>
      simp [bs, hv₀, Basis.coord_apply,
        -Basis.detDualEquiv_apply, Basis.detDualEquiv_self, Basis.detDualEquiv_apply_basis_zero_one]
  have hf : Φ.characterRuling k₀ (bs.coord 0).toAddMonoidHom
      (Φ.nonneg_or_nonpos_quadric_transverse_character bs rs hrs) = f := by congr
  have ht : Φ.characterRuling k₀ (bs.coord 0).toAddMonoidHom
      (Φ.nonneg_or_nonpos_quadric_transverse_character bs rs hrs) (hT.baseCenter j) ∈
        Set.range (rulingPoint[c]) := by
    rw [hf, hj]
    exact ⟨pt, (congrArg (fun k : Spec (.of k₀) ⟶ projectiveLine k₀ ↦ k pt)
      ((r 0).binomialCenter_comp_characterRuling k₀ hru rankTwo
        (b.detDualEquiv_self v) ((r 0).surjective_detCharacter b) c)).symm⟩
  have hne := hT.ne_quadric_transverse_ruling_of_lt_sum_first_base_orders k₀
    bs hΦ hc rs hrs g hg hjl hjfirst hlfirst (-c⁻¹)
      (by simpa only [Units.val_neg] using ht)
  dsimp only at hne
  rw [hα, hf] at hne
  exact hne hsum

local notation "σ" => s 2
local notation "w" => Fan.Ray.primitiveGenerator (σ)
local notation "hw" => Fan.Ray.primitiveGenerator_ne_zero (σ)
local notation "hwPos" => Fan.Ray.hull_primitiveGenerator_mem (σ)
local notation "hwOpp" => Fan.hull_neg_primitiveGenerator_mem_of_hirzebruch_section_two b 1 s hs
local notation "Ω" => Fan.mutationFan (Ψ) b hw hwPos hwOpp
local notation "hΩ" => Iff.mpr (Fan.isRegular_mutationFan_iff (Ψ) b hw hwPos hwOpp) hΨ
local notation "hcΩ" => Iff.mpr (Fan.isComplete_mutationFan_iff (Ψ) b hw hwPos hwOpp) hcΨ
local notation "t" => Equiv.trans s (Fan.mutationFanRayEquiv (Ψ) b hw hwPos hwOpp)
local notation "X''" => Fan.finiteFanScheme k₀ Ω
local notation "fX''" => (X'' ↘ S)

local notation "mut₀[" c "]" =>
  Scheme.PartialMap.toRationalMap (Φ.mutationPartialMap k₀ b (c : k₀) hv hp hop)
local notation "mut₁[" d "]" =>
  Scheme.PartialMap.toRationalMap (Fan.mutationPartialMap k₀ (Ψ) b (d : k₀) hw hwPos hwOpp)
local notation "τ[" a "," ht "]" =>
  FanHom.finiteFanSchemeHom k₀ (FanEquiv.toFanHom (Fan.quadricRulingExchange a hΩ hcΩ t ht))

/-- Two first centers on opposite smooth sections of a quadric give a resolved
block when their combined order exceeds the degree on a fiber of the mutation
ruling. The input quadric is
written in the frame of the exchanged ruling. The projections after each
mutation and after the final ruling exchange are regular on that surface and
have the same pole ideal as the original projection, when it has a pole
factorization. The returned quadric tower carries the transported pole ideal.

If the original fiber and section coordinates are `(β, α)` in this frame and
the two base orders are `m₁, m₂`, the final coordinates after exchanging the
rulings are `(α, β + α - m₁ - m₂)`. The exceptional coordinates of the new
reverse pivots are `m₂ - α` followed by `m₁ - α`. The other exceptional
coordinates retain their original relative order. -/
theorem exists_quadric_resolution_of_two_smooth_centers
    [(Φ.finiteFanScheme k₀).IsProjectiveOver k₀]
    {T : BlowupTower X (n + 2) Y} (hT : IsClosedPointTower X T)
    (g : Y ⟶ P) (hg : g ≫ fP = T.toBase ≫ fX) (hbir : Scheme.BirationalOver g (𝟙 P))
    (c d : k₀ˣ) (j : Fin (n + 2)) (l : Fin (n + 1))
    (hj : hT.baseCenter j = center[r 0,c] pt)
    (hl : hT.baseCenter (j.succAbove l) = center[r 2,d] pt)
    (hjfirst : ∀ k < j, hT.baseCenter k ≠ center[r 0,c] pt)
    (hlfirst : ∀ k < j.succAbove l, hT.baseCenter k ≠ center[r 2,d] pt) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : Nonempty (Ψ).cones := (hcΨ).nonempty_cones
    let : Nonempty (Ω).cones := (hcΩ).nonempty_cones
    let : SmoothOfRelativeDimension 2 fX := by
      rw [Fan.finiteFanScheme_over k₀]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
    let : SmoothOfRelativeDimension 2 fX' := by
      rw [Fan.finiteFanScheme_over k₀]
      exact rankTwo ▸ (Ψ).smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΨ
    let : SmoothOfRelativeDimension 2 fX'' := by
      rw [Fan.finiteFanScheme_over k₀]
      exact rankTwo ▸ (Ω).smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΩ
    let : IsIntegral Y := hT.isIntegral fX
    let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two fX
    let x : Additive (LineBundleClass X) × (Fin (n + 2) → ℤ) :=
      (T.picardMarking hT fX).symm (Additive.ofMul (pullback g H))
    let β := (C).repr x.1 0
    let α := (C).repr x.1 1
    let orders := fun k ↦ -x.2 k
    α < orders j + orders (j.succAbove l) →
    ∃ (a : Basis (Fin 2) ℤ N)
      (ht : (fun k ↦ ((t) k).primitiveGenerator) = ![a 0, a 1, -a 0, (0 : ℤ) • a 0 - a 1])
      (Z : Scheme) (U : BlowupTower X' (1 + (n + 1)) Z) (hU : IsClosedPointTower X' U)
      (e : Y ≅ Z) (W : Scheme) (V₀ : BlowupTower X'' (1 + (1 + n)) W)
      (hV : IsClosedPointTower X'' V₀) (k : Z ≅ W),
      let q := V₀.transport (asIso τ[a,ht])
      let hQ := q.isLift.isClosedPointTower hV
      let p₁ := e.hom ≫ U.toBase
      let p₂ := e.hom ≫ k.hom ≫ V₀.toBase
      let p₃ := (e ≪≫ k ≪≫ q.iso).hom ≫ q.tower.toBase
      let g' := (e ≪≫ k ≪≫ q.iso).inv ≫ g
      let : IsModification U.toBase := hU.isModification_of_smoothOfRelativeDimension_two fX'
      let : IsDominant p₁ := inferInstance
      T.toBase.toRationalMap.comp mut₀[c] = p₁.toRationalMap ∧
      p₁.toRationalMap.comp mut₁[d] = p₂.toRationalMap ∧
      p₃ = p₂ ≫ τ[a,ht] ∧
      g' ≫ fP = q.tower.toBase ≫ fX'' ∧
      Scheme.BirationalOver g' (𝟙 P) ∧
      (letI : Y.Over S := ⟨T.toBase ≫ fX⟩
       letI : T.toBase.IsOver S := ⟨rfl⟩
       letI : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension fX
       letI : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
       ∀ D : Y.IdealSheafData,
         ∃ (hp₁ : p₁.IsOver S) (hp₂ : p₂.IsOver S) (hp₃ : p₃.IsOver S),
           letI := hp₁
           letI := hp₂
           letI := hp₃
           B[Φ,hc].comap T.toBase = D * ramificationIdealSheaf k₀ T.toBase →
             B[Ψ,hcΨ].comap p₁ = D * ramificationIdealSheaf k₀ p₁ ∧
             B[Ω,hcΩ].comap p₂ = D * ramificationIdealSheaf k₀ p₂ ∧
             B[Ω,hcΩ].comap p₃ = D * ramificationIdealSheaf k₀ p₃ ∧
             B[Ω,hcΩ].comap q.tower.toBase =
               D.comap (e ≪≫ k ≪≫ q.iso).inv * hQ.ramificationIdealSheafToBase k₀) ∧
      let y := (q.tower.picardMarking hQ fX'').symm (Additive.ofMul (pullback g' H))
      let C'' := Fan.hirzebruchPicardBasis k₀ a 0 hΩ t ht
      C''.repr y.1 0 = α ∧
      C''.repr y.1 1 = β + α - orders j - orders (j.succAbove l) ∧
      y.2 (Fin.castAdd (1 + n) (0 : Fin 1)) = orders (j.succAbove l) - α ∧
      y.2 ((Fin.castAdd n (0 : Fin 1)).natAdd 1) =
        orders j - α ∧
      ∀ u : Fin n, y.2 (u.natAdd 1 |>.natAdd 1) = x.2 (j.succAbove (l.succAbove u)) := by
  intro hX hX' hX'' hdim hdim' hdim'' hY hmod x β α orders hsum
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
  have hne := quadric_mutationRuling_ne_of_lt_sum_first_base_orders k₀ b hΦ hc r hr hT g hg
    hjl c hj (by simpa only [hj] using hjfirst) (by simpa only [hl] using hlfirst) hsum
  have hdc : d * c ≠ 1 := by
    intro hdc
    have hd := mul_eq_one_iff_eq_inv.mp hdc
    apply hne
    rw [hj, hl, hd]
    exact congrArg (fun a : Spec (.of k₀) ⟶ projectiveLine k₀ ↦ a pt)
      (((r 0).binomialCenter_comp_characterRuling k₀ hru rankTwo
        (b.detDualEquiv_self v) ((r 0).surjective_detCharacter b) c).trans
        (quadric_opposite_center_on_pivot_fiber k₀ b r hr c).symm)
  obtain ⟨Z, U, hU, e, hmap, hg₁, hbir₁, hrev, hcenters, ha, hb, hm, hmrest⟩ :=
    hT.exists_hirzebruchOne_resolution_of_quadric_mutation k₀ b hΦ hc r hr g hg hbir c j hj hjfirst
  obtain ⟨hL, hLfirst⟩ :=
    first_oppositeCenter_of_mutation k₀ b r hr hT hU c d hdc hl hlfirst hrev hcenters
  obtain ⟨a, ht, W, V₀, hV, k, hnext, _, hover, hcoord⟩ :=
    hU.exists_quadric_resolution_of_hirzebruchOne_mutation k₀ b hΨ hcΨ s hs d
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
  refine ⟨hmap, hcomp, hthird, hg', hbir', ?_, ?_⟩
  -- Carry the pole factorization through both mutations and the ruling exchange.
  · intro D
    let : Y.Over S := ⟨T.toBase ≫ fX⟩
    let : T.toBase.IsOver S := ⟨rfl⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension fX
    let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    obtain ⟨hp₁, hpole₁⟩ := (r 0).mutation_resolution_poleIdeal_iff k₀ b hop c hT hΦ hc p₁ D hmap
    let : p₁.IsOver S := hp₁
    have he : e.hom ≫ U.toBase ≫ fX' = Y ↘ S :=
      (Category.assoc _ _ _).symm.trans (comp_over p₁ S)
    obtain ⟨hp₂, hpole₂⟩ := (s 2).mutation_resolution_poleIdeal_iff_of_iso k₀
      b hwOpp d hΨ hcΨ hU e he (k.hom ≫ V₀.toBase) D hnext
    let : p₂.IsOver S := hp₂
    let : p₃.IsOver S := ⟨hthird ▸ comp_over (p₂ ≫ τ[a,ht]) S⟩
    refine ⟨hp₁, hp₂, ‹_›, fun hpole ↦ ?_⟩
    have h₁ := hpole₁.mp (by simpa only [hT.ramificationIdealSheafToBase_def k₀] using hpole)
    have h₂ := hpole₂.mp h₁
    let : Smooth fX'' := hdim''.smooth
    have hτ : B[Ω,hcΩ].comap τ[a,ht] = B[Ω,hcΩ] * ramificationIdealSheaf k₀ τ[a,ht] := by
      rw [ramificationIdealSheaf_eq_top_of_isOpenImmersion k₀ (τ[a,ht]), mul_top]
      exact (Fan.quadricRulingExchange a hΩ hcΩ t ht).comap_toricBoundaryIdeal_finiteFanSchemeHom
        k₀ _ _
    have hram : ramificationIdealSheaf k₀ p₃ = ramificationIdealSheaf k₀ (p₂ ≫ τ[a,ht]) :=
      ramificationIdealSheaf_congr k₀ hthird
    have h₃ : B[Ω,hcΩ].comap p₃ = D * ramificationIdealSheaf k₀ p₃ := by
      rw [hram]
      exact (congrArg (Scheme.IdealSheafData.comap B[Ω,hcΩ]) hthird).trans
        (comap_eq_mul_ramificationIdealSheaf_comp k₀ p₂ τ[a,ht] 2 hτ h₂)
    refine ⟨h₁, h₂, h₃, ?_⟩
    -- The next block uses the pole ideal on the top of the returned point tower.
    let k₂ := e ≪≫ k ≪≫ q.iso
    let : q.top.Over S := ⟨q.tower.toBase ≫ fX''⟩
    let : q.tower.toBase.IsOver S := ⟨rfl⟩
    let : SmoothOfRelativeDimension 2 (q.top ↘ S) := hQ.smoothOfRelativeDimension fX''
    let : k₂.hom.IsOver S := ⟨(Category.assoc _ _ _).symm.trans (comp_over p₃ S)⟩
    simpa only [IsIso.inv_eq_of_hom_inv_id k₂.hom_inv_id, hQ.ramificationIdealSheafToBase_def k₀]
      using (comap_eq_mul_ramificationIdealSheaf_comp_iff_of_isIso k₀ k₂.hom q.tower.toBase 2).mp h₃
  -- Read the marked line class through both links in the order of the retained centers.
  intro y C''
  have h₂ := hcoord (pullback (e.inv ≫ g) H)
  dsimp only at h₂
  simp only [Iso.trans_inv, pullback_comp, Category.assoc] at h₂
  obtain ⟨h₂a, h₂b, h₂m, h₂rest⟩ := h₂
  have hy : C''.repr y.1 1 = β + α - orders j - orders (j.succAbove l) := by
    simpa only [y, g', C'', Iso.trans_inv, Category.assoc, ha, hmrest, orders, sub_neg_eq_add]
      using h₂b
  refine ⟨by simpa only [y, g', C'', Iso.trans_inv, Category.assoc, hb] using h₂a,
    hy, ?_, ?_, ?_⟩
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

end QPainleve.BlowupTower.IsClosedPointTower

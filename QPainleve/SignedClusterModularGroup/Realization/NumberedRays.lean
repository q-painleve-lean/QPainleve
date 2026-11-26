/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Data.Set.PowersetCard
public import QPainleve.Geometry.Toric.Fan.Boundary.Numbering
public import QPainleve.SignedClusterModularGroup.Realization.MarkedComparison
public import QPainleve.SignedClusterModularGroup.Realization.Tropical

import Mathlib.Order.Hom.PowersetCard
import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.ComponentOrder
import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Surviving
import TauCeti.Data.ZMod.FinEquiv

/-!
# Numbered surviving boundary rays

In a fixed ordered toric presentation, the marked Picard pullbacks determine
which strict boundary rays survive the contractions. The oriented subdivision
and the initial component then determine the numbering of the surviving rays
and the corresponding marked boundary classes. The increasing ray offsets
give a fixed-cardinality set for computing the boundary order table.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve.BlowupTower
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones] {r m n : ℕ} [NeZero m] [NeZero n]
  {L : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "XTor[" l "]" => Spec (CommRingCat.of (LaurentRing ℂ (Fin l)))
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "center" c:arg => (fun j : Fin _ ↦ c (ofAdd (Pi.single j 1)))

variable [PrestableFamily ((Φ.boundaryIdeal h₀).subscheme ↘ S)]
  {γ : Type*} {a : γ → ((Φ.boundaryIdeal h₀).subscheme ↘ S).smoothLocus}
  {T : NodalCycleNumbering a m} {origin : ZMod m}
  {ι : L →ₗ[ℤ] Additive (LineBundleClass Φ.algebraicRealization) × (Fin r → ℤ)}

local notation "F" => LinearMap.BilinForm.prod (Chow.intersectionBilinForm ℂ Φ.algebraicRealization)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))

namespace ContractedToricFiber

variable {c d : Multiplicative (Fin r → ℤ) →* ℂˣ} {P Q : MarkedSurface ℂ n B XTor[r]}
  (p : ContractedToricFiber b s hΦ T origin ι c P)
  (q : ContractedToricFiber b s hΦ T origin ι d Q)

local notation "rayAt" => Φ.rayFinEquivOfNodalCycleNumbering hΦ T origin

private theorem strictMono_boundaryRayOffset (hP : D[P].IsEffectiveCartier) :
    StrictMono fun j : Fin n ↦ (rayAt).symm (p.numberedBoundaryRays hP (ZMod.finEquiv n j)) := by
  let : PrestableFamily (P.boundary ↘ S) := P.prestable
  let e := Φ.rayEquivOfNodalCycleNumbering hΦ T
  have he (j : ZMod m) : (Φ.boundaryNormalizationComponentEquiv hΦ).symm (T.component j) =
      e j :=
    (Equiv.symm_apply_eq _).mpr (Φ.boundaryNormalizationComponentEquiv_rayEquivOfNodalCycleNumbering
      hΦ T j).symm
  let u := (p.numberedBoundaryRays hP).trans e.symm.toEmbedding
  have hzero : u 0 = origin := by
    simp only [u, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      p.numberedBoundaryRays_zero, he, Equiv.symm_apply_apply]
  have hu (j : ZMod n) : p.boundaryMap (T.componentGenericPoint (u j)) =
      P.cycle.componentGenericPoint j := by
    apply (p.numberedBoundaryRays_eq_iff hP j (u j)).mp
    simp only [he, u, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Equiv.apply_symm_apply]
  intro j k hjk
  simpa only [Fin.lt_def,
    Fan.rayFinEquivOfNodalCycleNumbering_symm_apply, ZMod.finEquiv_symm_apply_val,
    hzero, u, Function.Embedding.trans_apply, Equiv.toEmbedding_apply] using
    p.orientedSubdivision.strictMono_componentSection u hu hjk

/-- The finite offsets of surviving toric rays in the contracted boundary numbering,
starting at the ray of component zero. -/
noncomputable def numberedBoundaryRayOffsets (hP : D[P].IsEffectiveCartier) : Fin n ↪o Fin m :=
  OrderEmbedding.ofStrictMono _ (p.strictMono_boundaryRayOffset hP)

/-- The offset of a component is the inverse ray index applied to its surviving ray. -/
@[simp]
theorem numberedBoundaryRayOffsets_apply (hP : D[P].IsEffectiveCartier) (j : Fin n) :
    p.numberedBoundaryRayOffsets hP j =
      (rayAt).symm (p.numberedBoundaryRays hP (ZMod.finEquiv n j)) :=
  (rfl)

/-- Membership in the offset range is equivalent to survival of the corresponding ray. -/
theorem mem_range_numberedBoundaryRayOffsets_iff (hP : D[P].IsEffectiveCartier) (k : Fin m) :
    k ∈ Set.range (p.numberedBoundaryRayOffsets hP) ↔
      rayAt k ∈ Set.range (p.numberedBoundaryRays hP) := by
  simp only [Set.mem_range, numberedBoundaryRayOffsets_apply, Equiv.symm_apply_eq]
  exact ((ZMod.finEquiv n).surjective.exists
    (p := fun j ↦ p.numberedBoundaryRays hP j = rayAt k)).symm

/-- The offsets of the surviving rays, with cardinality given by the contracted boundary. -/
noncomputable def survivingBoundaryRayOffsets (hP : D[P].IsEffectiveCartier) :
    Set.powersetCard (Fin m) n :=
  Set.powersetCard.ofFinEmbEquiv (p.numberedBoundaryRayOffsets hP)

/-- An offset belongs to the survivor set exactly when its ray survives. -/
@[simp]
theorem mem_survivingBoundaryRayOffsets (hP : D[P].IsEffectiveCartier) (k : Fin m) :
    k ∈ p.survivingBoundaryRayOffsets hP ↔
      rayAt k ∈ Set.range (p.numberedBoundaryRays hP) :=
  (Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range _ _).trans
    (p.mem_range_numberedBoundaryRayOffsets_iff hP k)

/-- Sorting the survivor set recovers the offsets in the contracted boundary numbering. -/
@[simp]
theorem orderEmbOfFin_survivingBoundaryRayOffsets (hP : D[P].IsEffectiveCartier) :
    (p.survivingBoundaryRayOffsets hP).val.orderEmbOfFin
      (p.survivingBoundaryRayOffsets hP).prop = p.numberedBoundaryRayOffsets hP := by
  rw [← Set.powersetCard.ofFinEmbEquiv_symm_apply, survivingBoundaryRayOffsets,
    Equiv.symm_apply_apply]

/-- The contracted boundary numbering is the increasing enumeration of the surviving
ray offsets, read from the specified initial toric ray. -/
theorem numberedBoundaryRays_eq_orderEmbOfFin (hP : D[P].IsEffectiveCartier)
    (survivors : Set.powersetCard (Fin m) n)
    (hkeep : ∀ k ∈ survivors, rayAt k ∈ Set.range (p.numberedBoundaryRays hP)) :
    ∀ j : Fin n, p.numberedBoundaryRays hP (ZMod.finEquiv n j) =
      rayAt (survivors.val.orderEmbOfFin survivors.prop j) := by
  have hsubset : survivors.val ⊆ (p.survivingBoundaryRayOffsets hP).val :=
    fun k hk ↦ (p.mem_survivingBoundaryRayOffsets hP k).mpr (hkeep k hk)
  have heq : survivors = p.survivingBoundaryRayOffsets hP :=
    Subtype.ext (Finset.eq_of_subset_of_card_le hsubset (by simp))
  intro j
  rw [heq, orderEmbOfFin_survivingBoundaryRayOffsets, numberedBoundaryRayOffsets_apply,
    Equiv.apply_symm_apply]

/-- The same set of surviving rays gives the same numbered rays for two contractions
with the same oriented source cycle and initial component. -/
theorem numberedBoundaryRays_eq_of_range_eq
    (hP : D[P].IsEffectiveCartier) (hQ : D[Q].IsEffectiveCartier)
    (hrange : Set.range (p.numberedBoundaryRays hP) = Set.range (q.numberedBoundaryRays hQ)) :
    p.numberedBoundaryRays hP = q.numberedBoundaryRays hQ := by
  have hr : Set.range (p.numberedBoundaryRayOffsets hP) =
      Set.range (q.numberedBoundaryRayOffsets hQ) := by
    ext k
    simp only [mem_range_numberedBoundaryRayOffsets_iff, hrange]
  have h := OrderEmbedding.range_inj_of_wellFoundedLT.mp hr
  apply Function.Embedding.ext
  intro j
  obtain ⟨k, rfl⟩ := (ZMod.finEquiv n).surjective j
  exact (rayAt).symm.injective (by
    simpa only [numberedBoundaryRayOffsets_apply] using DFunLike.congr_fun h k)

variable [Φ.algebraicRealization.IsProjectiveOver ℂ]

/-- Two nodal contractions of one marked toric presentation have the same numbered
rays. The common Picard pullback determines the set of surviving rays. -/
theorem numberedBoundaryRays_eq_of_nodalContractions
    [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S)]
    (hp : p.IsNodalContraction) (hq : q.IsNodalContraction) (hsep : (F).SeparatingRight) :
    p.numberedBoundaryRays hp.cartier = q.numberedBoundaryRays hq.cartier := by
  let : SmoothOfRelativeDimension 2 (P.surface ↘ S) := P.smooth
  let : SmoothOfRelativeDimension 2 (Q.surface ↘ S) := Q.smooth
  let : P.surface.IsProjectiveOver ℂ := P.projective
  let : Q.surface.IsProjectiveOver ℂ := Q.projective
  obtain ⟨_, _, A, hA, e, he⟩ := hp.exists_tower
  obtain ⟨_, _, U, hU, f, hf⟩ := hq.exists_tower
  let G (x : LineBundleClass Q.surface) :=
    (P.picardMarking (Q.picardMarking.symm (Additive.ofMul x))).toMul
  have hG : Function.Surjective G :=
    Additive.toMul.surjective.comp
      (P.picardMarking.surjective.comp (Q.picardMarking.symm.surjective.comp
        Additive.ofMul.surjective))
  have hPic (x : LineBundleClass Q.surface) := (p.marked_pullback
    (Q.picardMarking.symm (Additive.ofMul x))).trans
    (q.marked_pullback (Q.picardMarking.symm (Additive.ofMul x))).symm
  simp only [LinearEquiv.apply_symm_apply, toMul_ofMul, ← he, ← hf] at hPic
  have hover := he.symm ▸ p.projection_over
  have hover' := hf.symm ▸ q.projection_over
  have hD := he.symm ▸ p.support_comap
  have hD' := hf.symm ▸ q.support_comap
  have hkeep := Fan.mem_boundaryPrimes_iff_of_matching_picard_markings hΦ b s
    (center c) hA e.symm hover hD (center d) hU f.symm hover' hD' hsep G hG hPic
  apply p.numberedBoundaryRays_eq_of_range_eq q hp.cartier hq.cartier
  ext ρ
  rw [p.mem_range_numberedBoundaryRays_iff, q.mem_range_numberedBoundaryRays_iff]
  simpa only [Iso.symm_hom, he, hf] using hkeep ρ

/-- Nodal contractions of one marked presentation having the same surviving rays
have the same class at each numbered boundary component. -/
theorem boundaryClass_eq_of_range_numberedBoundaryRays_eq
    (hp : p.IsNodalContraction) (hq : q.IsNodalContraction) (hι : Function.Injective ι)
    (hrange : Set.range (p.numberedBoundaryRays hp.cartier) =
      Set.range (q.numberedBoundaryRays hq.cartier)) :
    P.boundaryClass hp.cartier = Q.boundaryClass hq.cartier := by
  classical
  let : SmoothOfRelativeDimension 2 (P.surface ↘ S) := P.smooth
  let : SmoothOfRelativeDimension 2 (Q.surface ↘ S) := Q.smooth
  let : P.surface.IsProjectiveOver ℂ := P.projective
  let : Q.surface.IsProjectiveOver ℂ := Q.projective
  let := (P.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := (Q.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  obtain ⟨_, _, A, hA, e, he⟩ := hp.exists_tower
  obtain ⟨_, _, U, hU, f, hf⟩ := hq.exists_tower
  have hover := he.symm ▸ p.projection_over
  have hover' := hf.symm ▸ q.projection_over
  have hD := he.symm ▸ p.support_comap
  have hD' := hf.symm ▸ q.support_comap
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  let : SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S) := by
    rw [← hN, Φ.algebraicRealization_over]
    exact Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : IsModification (e.inv ≫ A.toBase) := he.symm ▸ p.modification
  let : IsModification (f.inv ≫ U.toBase) := hf.symm ▸ q.modification
  have hsurvives :
      Set.range (Fan.contractedBoundaryRayEmbedding hΦ b s (center c)
        (e.inv ≫ A.toBase) hD) =
      Set.range (Fan.contractedBoundaryRayEmbedding hΦ b s (center d)
        (f.inv ≫ U.toBase) hD') := by
    simpa only [he, hf, p.range_numberedBoundaryRays, q.range_numberedBoundaryRays,
      boundaryRayEmbedding_def] using hrange
  have hspan := (Fan.markedExceptionalSpan_eq_span_compl_survivingRays hΦ b s
      (center c) hA e.symm hD).trans
    (hsurvives ▸ (Fan.markedExceptionalSpan_eq_span_compl_survivingRays hΦ b s
      (center d) hU f.symm hD').symm)
  have hrays := p.numberedBoundaryRays_eq_of_range_eq q hp.cartier hq.cartier hrange
  funext j
  apply hι
  have hclass := Fan.marked_pullback_prime_eq_of_contractedBoundaryRayEmbedding_eq hΦ b s
    (center c) hA e.symm hover hD (center d) hU f.symm hover' hD' hspan
    (P.numberedBoundaryPrimes hp.cartier j) (Q.numberedBoundaryPrimes hq.cartier j)
    (by simpa only [Iso.symm_hom, he, hf, numberedBoundaryRays_apply,
      boundaryRayEmbedding_def] using congrArg (fun u : ZMod n ↪ Φ.Ray ↦ u j) hrays)
  dsimp only at hclass
  rw [Iso.symm_hom, Iso.symm_hom, he, hf] at hclass
  rw [← p.marked_pullback, ← q.marked_pullback, P.picardMarking_boundaryClass,
    Q.picardMarking_boundaryClass]
  convert hclass using 4 <;> simp only [toMul_ofMul]
  all_goals
    apply congrArg LineBundleClass.primeDivisorClass
    apply Subtype.ext
    simp only [MarkedSurface.numberedBoundaryPrimes_apply_val]

end ContractedToricFiber

namespace GeometricRealization.HasNodalToricTargetModels

variable {T₀ T₁ : Over S} {M : Point T₁ → MarkedSurface ℂ n B XTor[r]}
  {centers : Point T₁ → Multiplicative (Fin r → ℤ) →* ℂˣ}
  {C : T₀.left.PartialMap T₁.left} [C.IsOver T₀.hom T₁.hom]

/-- Nodal models with a common Picard marking have the surviving rays of the reference
contraction at every reached target center. -/
theorem of_nodalContractions [Φ.algebraicRealization.IsProjectiveOver ℂ]
    [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S)]
    (hsep : (F).SeparatingRight)
    {c₀ : Point T₁}
    (p₀ : ContractedToricFiber b s hΦ T origin ι (centers c₀) (M c₀))
    (h₀ : p₀.IsNodalContraction) {U : Set (Point T₁)}
    (p : ∀ c ∈ U, ContractedToricFiber b s hΦ T origin ι (centers c) (M c))
    (h : ∀ c hc, (p c hc).IsNodalContraction)
    (hU : ∀ x : CenterPoint C, x ≫ C.domainTarget ∈ U) :
    HasNodalToricTargetModels (T₀ := T₀) (T₁ := T₁) (b := b) (s := s) (hΦ := hΦ)
      (toricCycle := T) (origin := origin) (ι := ι) (P := M) centers
      (Set.range p₀.boundaryRayEmbedding) C := by
  intro x
  let q := p _ (hU x)
  have hq : q.IsNodalContraction := h _ (hU x)
  refine ⟨q, hq, ?_⟩
  rw [← q.range_numberedBoundaryRays hq.cartier, ← p₀.range_numberedBoundaryRays h₀.cartier,
    q.numberedBoundaryRays_eq_of_nodalContractions p₀ hq h₀ hsep]

end GeometricRealization.HasNodalToricTargetModels

end QPainleve.SignedClusterModularGroup

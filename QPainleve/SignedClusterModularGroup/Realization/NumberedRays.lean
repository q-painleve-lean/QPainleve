/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.MarkedComparison
public import QPainleve.SignedClusterModularGroup.Realization.Tropical

import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.ComponentOrder
import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Surviving

/-!
# Constant numbered boundary rays

In a fixed ordered toric presentation, the marked Picard pullbacks determine
which strict boundary rays survive the contractions. The oriented subdivision
and the initial component then determine the numbering of the surviving rays
and the corresponding marked boundary classes.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve.BlowupTower
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.ContractedToricFiber

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
  {c d : Multiplicative (Fin r → ℤ) →* ℂˣ} {P Q : MarkedSurface ℂ n B XTor[r]}
  (p : ContractedToricFiber b s hΦ T origin ι c P)
  (q : ContractedToricFiber b s hΦ T origin ι d Q)

/-- Numbered boundary rays occur in increasing cyclic distance from the toric origin. -/
theorem strictMono_numberedBoundaryRays (hP : D[P].IsEffectiveCartier) :
    let e := ((Φ.boundaryNormalizationComponentEquiv hΦ).trans T.component.symm)
    StrictMono fun j : Fin n ↦
      (e (p.numberedBoundaryRays hP (ZMod.finEquiv n j)) - origin).val := by
  let : PrestableFamily (P.boundary ↘ S) := P.prestable
  let e := (Φ.boundaryNormalizationComponentEquiv hΦ).trans T.component.symm
  let u := (p.numberedBoundaryRays hP).trans e.toEmbedding
  have hzero : u 0 = origin := by
    simp only [u, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      p.numberedBoundaryRays_zero, e, Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply]
  have hu (j : ZMod n) : p.boundaryMap (T.componentGenericPoint (u j)) =
      P.cycle.componentGenericPoint j := by
    apply (p.numberedBoundaryRays_eq_iff hP j (u j)).mp
    simp only [u, Function.Embedding.trans_apply, Equiv.toEmbedding_apply, e,
      Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  simpa only [hzero, u, Function.Embedding.trans_apply, Equiv.toEmbedding_apply] using
    p.orientedSubdivision.strictMono_componentSection u hu

/-- The same set of surviving rays gives the same numbered rays for two contractions
with the same oriented source cycle and initial component. -/
theorem numberedBoundaryRays_eq_of_range_eq
    (hP : D[P].IsEffectiveCartier) (hQ : D[Q].IsEffectiveCartier)
    (hrange : Set.range (p.numberedBoundaryRays hP) = Set.range (q.numberedBoundaryRays hQ)) :
    p.numberedBoundaryRays hP = q.numberedBoundaryRays hQ := by
  let e := (Φ.boundaryNormalizationComponentEquiv hΦ).trans T.component.symm
  let index (ρ : Φ.Ray) := (e ρ - origin).val
  have hindex : Function.Injective index :=
    (ZMod.val_injective m).comp ((Equiv.subRight origin).injective.comp e.injective)
  let toZMod := fun j : Fin n ↦ ZMod.finEquiv n j
  have hp : StrictMono (index ∘ p.numberedBoundaryRays hP ∘ toZMod) :=
    p.strictMono_numberedBoundaryRays hP
  have hq : StrictMono (index ∘ q.numberedBoundaryRays hQ ∘ toZMod) :=
    q.strictMono_numberedBoundaryRays hQ
  have hs : Function.Surjective toZMod := (ZMod.finEquiv n).surjective
  have hr : Set.range (index ∘ p.numberedBoundaryRays hP ∘ toZMod) =
      Set.range (index ∘ q.numberedBoundaryRays hQ ∘ toZMod) := by
    rw [Set.range_comp, Set.range_comp index, hs.range_comp, hs.range_comp, hrange]
  have h := (hp.range_inj_of_wellFoundedLT hq).mp hr
  apply Function.Embedding.ext
  intro j
  obtain ⟨j, rfl⟩ := hs j
  exact hindex (congrFun h j)

variable [Φ.algebraicRealization.IsProjectiveOver ℂ]

local notation "F" => LinearMap.BilinForm.prod (Chow.intersectionBilinForm ℂ Φ.algebraicRealization)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))

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
    simpa only [he, hf, ← p.range_numberedBoundaryRays hp.cartier,
      ← q.range_numberedBoundaryRays hq.cartier] using hrange
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
    (by simpa only [Iso.symm_hom, he, hf, ← numberedBoundaryRays_apply] using
      congrArg (fun u : ZMod n ↪ Φ.Ray ↦ u j) hrays)
  dsimp only at hclass
  rw [Iso.symm_hom, Iso.symm_hom, he, hf] at hclass
  rw [← p.marked_pullback, ← q.marked_pullback, P.picardMarking_boundaryClass,
    Q.picardMarking_boundaryClass]
  convert hclass using 4 <;> simp only [toMul_ofMul]
  all_goals
    apply congrArg LineBundleClass.primeDivisorClass
    apply Subtype.ext
    simp only [MarkedSurface.numberedBoundaryPrimes_apply_val]

end QPainleve.SignedClusterModularGroup.ContractedToricFiber

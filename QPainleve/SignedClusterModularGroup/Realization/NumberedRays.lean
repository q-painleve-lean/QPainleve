/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.MarkedComparison
public import QPainleve.SignedClusterModularGroup.Realization.Tropical

import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Surviving

/-!
# Constant numbered boundary rays

In a fixed ordered toric presentation, the marked Picard pullbacks determine
which strict boundary rays survive the contractions. The marked boundary
classes determine the labels of those rays, so one order table can be used
at every center.
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

variable
  [Φ.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S)]

local notation "F" => LinearMap.BilinForm.prod (Chow.intersectionBilinForm ℂ Φ.algebraicRealization)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))

/-- The surviving toric rays in two nodal fibers agree in the given numbering
when the common marked boundary classes are distinct. -/
theorem numberedBoundaryRays_eq_of_boundaryClass_eq
    (hp : p.IsNodalContraction) (hq : q.IsNodalContraction) (hsep : (F).SeparatingRight)
    (hmark : ∀ j, P.boundaryClass hp.cartier j = Q.boundaryClass hq.cartier j)
    (hinj : Function.Injective (P.boundaryClass hp.cartier)) (hι : Function.Injective ι) :
    p.numberedBoundaryRays hp.cartier = q.numberedBoundaryRays hq.cartier := by
  classical
  let : SmoothOfRelativeDimension 2 (P.surface ↘ S) := P.smooth
  let : SmoothOfRelativeDimension 2 (Q.surface ↘ S) := Q.smooth
  let : P.surface.IsProjectiveOver ℂ := P.projective
  let : Q.surface.IsProjectiveOver ℂ := Q.projective
  let := (P.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := (Q.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
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
  have hspan := Fan.markedExceptionalSpan_eq_of_matching_picard_markings hΦ b s
    (center c) hA e.symm hover (center d) hU f.symm hover' hsep G hG hPic
  have hkeep := Fan.mem_boundaryPrimes_iff_of_matching_picard_markings hΦ b s
    (center c) hA e.symm hover hD (center d) hU f.symm hover' hD' hsep G hG hPic
  have hrange : Set.range (p.numberedBoundaryRays hp.cartier) =
      Set.range (q.numberedBoundaryRays hq.cartier) := by
    ext ρ
    rw [p.mem_range_numberedBoundaryRays_iff, q.mem_range_numberedBoundaryRays_iff]
    simpa only [Iso.symm_hom, he, hf] using hkeep ρ
  apply Function.Embedding.ext
  intro j
  obtain ⟨k, hk⟩ := hrange.le (Set.mem_range_self j)
  suffices k = j by simpa only [this] using hk.symm
  apply hinj
  rw [hmark k]
  apply hι
  symm
  have hclass := Fan.marked_pullback_prime_eq_of_contractedBoundaryRayEmbedding_eq hΦ b s
    (center c) hA e.symm hover hD (center d) hU f.symm hover' hD' hspan
    (P.numberedBoundaryPrimes hp.cartier j) (Q.numberedBoundaryPrimes hq.cartier k)
    (by simpa only [Iso.symm_hom, he, hf, numberedBoundaryRays_apply] using hk.symm)
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

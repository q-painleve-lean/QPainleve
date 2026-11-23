/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Word
public import QPainleve.Geometry.Toric.Fan.Boundary.Valuation
public import QPainleve.Geometry.Toric.Fan.Mutation.Valuation

import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision
import QPainleve.Geometry.Toric.Fan.Mutation.Charge
import QPainleve.Geometry.Toric.Fan.StarSubdivision.RayInsertion

/-!
# Boundary orders along toric mutation words

Insert the opposite pivot ray by a regular subdivision before each elementary transformation.
The original rays survive subdivision, and the subsequent mutation sends them by its integral
shear. In this way a word transports the original boundary rays into a terminal fan. The
orders of the terminal charge characters at these rays are the entries of the tropical word.

The boundary calculation for an elementary transformation follows Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, §3.1](https://arxiv.org/html/1309.2573v2#S3.SS1).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module Multiplicative PointedCone Quiver
open QPainleve.Cluster

namespace TauCeti.Toric.Fan

variable {N V : Type} {ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Fintype ι] [DecidableEq ι]
  (b : Basis (Fin 2) ℤ N)

local notation "d" => b.detDualEquiv
local notation "trop" => Paths.lift (tropicalPrefunctor (A := ℤ) ι)

local notation "K(" Φ ")" => Scheme.functionField (Fan.algebraicRealization Φ)
local notation "χ" => Multiplicative (ι → ℤ) →* ℂˣ

private theorem ord_mutation_of_subdivision {Ω : Fan i} (h : Ω.IsSubdivision Φ)
    (hΦ : Φ.IsRegular) (hΩ : Ω.IsRegular) [Nonempty Φ.cones] (pivot : Ω.Ray)
    (hopp : hull ℝ {i (-pivot.primitiveGenerator)} ∈ Ω.cones) (c : ℂˣ) :
    let hv := pivot.isPrimitiveGenerator.ne_zero
    let hpos := pivot.hull_primitiveGenerator_mem
    let Ψ := Ω.mutationFan b hv hpos hopp
    let hΨ := (Ω.isRegular_mutationFan_iff b hv hpos hopp).2 hΩ
    letI : Nonempty Ω.cones := ⟨pivot.toCone⟩
    letI : Nonempty Ψ.cones := ⟨((Ω.mutationFanRayEquiv b hv hpos hopp) pivot).toCone⟩
    ∃ q : K(Ψ) ≃ₐ[ℂ] K(Φ), ∀ (ρ : Φ.Ray) (a : K(Ψ)),
      Φ.algebraicRealization.ord (q a) (Φ.rayBoundaryPoint hΦ ρ).val =
        Ψ.algebraicRealization.ord a
          (Ψ.rayBoundaryPoint hΨ (Ω.mutationFanRayEquiv b hv hpos hopp (h.liftRay ρ))).val := by
  dsimp only
  let hv := pivot.isPrimitiveGenerator.ne_zero
  let hpos := pivot.hull_primitiveGenerator_mem
  have : Nonempty Ω.cones := ⟨pivot.toCone⟩
  have : Nonempty (Ω.mutationFan b hv hpos hopp).cones :=
    ⟨((Ω.mutationFanRayEquiv b hv hpos hopp) pivot).toCone⟩
  have := Ω.isIso_mutationComplementPullback b (c : ℂ) hv hpos hopp
  let m := Ω.mutationComplementPullback b (c : ℂ) hv hpos hopp
  let sub := h.toFanHom.algebraicMap
  let e := asIso m ≪≫ (asIso sub.functionFieldMap).symm
  have he (a : K(Ω.mutationFan b hv hpos hopp)) :
      sub.functionFieldMap (e.hom a) = m a := by
    simp [e]
  let q : K(Ω.mutationFan b hv hpos hopp) ≃ₐ[ℂ] K(Φ) :=
    AlgEquiv.ofRingEquiv (f := e.commRingCatIsoToRingEquiv) fun z ↦
      sub.functionFieldMap.hom.injective <| by
        calc
          sub.functionFieldMap (e.hom (algebraMap ℂ _ z)) =
              m (algebraMap ℂ _ z) := he _
          _ = algebraMap ℂ K(Ω) z :=
            Ω.mutationComplementPullback_algebraMap b (c : ℂ) hv hpos hopp z
          _ = sub.functionFieldMap (algebraMap ℂ _ z) :=
            (sub.functionFieldMap_algebraMap ℂ z).symm
  refine ⟨q, fun ρ a ↦ ?_⟩
  have hs : sub.functionFieldMap (q a) = m a := he _
  rw [← h.ord_functionFieldMap_liftRay hΩ hΦ, hs]
  exact Ω.ord_mutationComplementPullback_rayBoundaryPoint b c hv hpos hopp hΩ (h.liftRay ρ) a

private theorem exists_toric_boundary_valuation_transport_mutate {B : SkewExchangeMatrix ι}
    (P : ChargeSeed B N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (s : ι → Φ.Ray)
    (hform : P.form = b.detDualEquiv.toLinearMap) (hcharge : P.charge = rayChargeMap s) (p : ι) :
    ∃ (Ψ : Fan i) (hΨ : Ψ.IsRegular) (hΨc : Ψ.IsComplete) (t : ι → Ψ.Ray) (f : Φ.Ray ↪ Ψ.Ray),
      (Step.chargeTarget ((Generator.mutate p).toStep B) P).charge = rayChargeMap t ∧
      (∀ ρ, rayBoundaryOrders b t (f ρ) =
        (Generator.mutate p).tropical B (rayBoundaryOrders b s ρ)) ∧
      letI : Nonempty Φ.cones := hc.nonempty_cones
      letI : Nonempty Ψ.cones := hΨc.nonempty_cones
      ∃ q : ℂˣ → (K(Ψ) ≃ₐ[ℂ] K(Φ)), ∀ (c : ℂˣ) (ρ : Φ.Ray) (a : K(Ψ)),
        Φ.algebraicRealization.ord (q c a) (Φ.rayBoundaryPoint hΦ ρ).val =
          Ψ.algebraicRealization.ord a (Ψ.rayBoundaryPoint hΨ (f ρ)).val := by
  have hrank : finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  have hv := (s p).isPrimitiveGenerator.ne_zero
  obtain ⟨Ω, hΩ, hreg, hopp⟩ := Φ.exists_regular_subdivision_containing_ray hΦ hrank
    (neg_ne_zero.mpr hv) (Φ.mem_support.mpr (Φ.isComplete_iff.mp hc _))
  let s₀ := hΩ.liftRay ∘ s
  have hopp₀ : hull ℝ {i (-(s₀ p).primitiveGenerator)} ∈ Ω.cones := by
    simpa only [s₀, Function.comp_apply, hΩ.primitiveGenerator_liftRay] using hopp
  let h₀ := (s₀ p).isPrimitiveGenerator.ne_zero
  let h₁ := (s₀ p).hull_primitiveGenerator_mem
  let Ψ := Ω.mutationFan b h₀ h₁ hopp₀
  let t := Ω.mutationFanCenterRays b s₀ p hopp₀
  let g : Φ.Ray ↪ Ω.Ray := ⟨hΩ.liftRay, fun ρ τ h ↦
    Ray.primitiveGenerator_injective (by
      simpa only [hΩ.primitiveGenerator_liftRay] using congrArg Ray.primitiveGenerator h)⟩
  let f := g.trans (Ω.mutationFanRayEquiv b h₀ h₁ hopp₀).toEmbedding
  have hf (ρ : Φ.Ray) : f ρ = Ω.mutationFanRayEquiv b h₀ h₁ hopp₀ (hΩ.liftRay ρ) :=
    rfl
  have hB : ∀ j, B.matrix j p = d (s₀ j).primitiveGenerator (s₀ p).primitiveGenerator := by
    intro j
    rw [← P.matrix_eq, chargeExchangeMatrix_apply, hform, hcharge]
    simp [s₀, Basis.detDualEquiv_apply]
  refine ⟨Ψ, (Ω.isRegular_mutationFan_iff b h₀ h₁ hopp₀).2 hreg,
    (Ω.isComplete_mutationFan_iff b h₀ h₁ hopp₀).2 (hΩ.isComplete_iff.2 hc), t, f, ?_, ?_, ?_⟩
  · rw [Step.chargeTarget_mutate_charge, hform, hcharge,
      ← hΩ.rayChargeMap_liftRay s, ← rayChargeMap_mutationFanCenterRays b s₀ p hopp₀]
  · intro ρ
    have h := Ω.tropical_mutate_eq_rayPairing_mutationFanRayEquiv b s₀ p hopp₀ B hB (hΩ.liftRay ρ)
    have ho : (fun j ↦ d (s₀ j).primitiveGenerator (hΩ.liftRay ρ).primitiveGenerator) =
        rayBoundaryOrders b s ρ := by
      funext j
      simp [s₀, Basis.detDualEquiv_apply]
    rw [ho] at h
    funext j
    simpa only [rayBoundaryOrders_apply, Basis.detDualEquiv_apply, t, hf] using congrFun h.symm j
  · have := hc.nonempty_cones
    have h (c : ℂˣ) := ord_mutation_of_subdivision b hΩ hΦ hreg (s₀ p) hopp₀ c
    choose q hq using h
    exact ⟨q, fun c ρ a ↦ by simpa only [hf, Ψ] using hq c ρ a⟩

private theorem exists_toric_boundary_valuation_transport_step {B C : SkewExchangeMatrix ι}
    (e : B ⟶ C) (he : e.generator.inversionCount = 0)
    (P : ChargeSeed B N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (s : ι → Φ.Ray)
    (hform : P.form = b.detDualEquiv.toLinearMap) (hcharge : P.charge = rayChargeMap s) :
    ∃ (Ψ : Fan i) (hΨ : Ψ.IsRegular) (hΨc : Ψ.IsComplete) (t : ι → Ψ.Ray) (f : Φ.Ray ↪ Ψ.Ray),
      (Step.chargeTarget e P).form = b.detDualEquiv.toLinearMap ∧
      (Step.chargeTarget e P).charge = rayChargeMap t ∧
      (∀ ρ, rayBoundaryOrders b t (f ρ) = Step.tropical e (rayBoundaryOrders b s ρ)) ∧
      letI : Nonempty Φ.cones := hc.nonempty_cones
      letI : Nonempty Ψ.cones := hΨc.nonempty_cones
      ∃ q : (ι → ℂˣ) → (K(Ψ) ≃ₐ[ℂ] K(Φ)), ∀ (c : ι → ℂˣ) (ρ : Φ.Ray) (a : K(Ψ)),
        Φ.algebraicRealization.ord (q c a) (Φ.rayBoundaryPoint hΦ ρ).val =
          Ψ.algebraicRealization.ord a (Ψ.rayBoundaryPoint hΨ (f ρ)).val := by
  obtain ⟨g, rfl⟩ := e
  have hg : g.toStep B = (⟨g, rfl⟩ : Step B (g.target B)) :=
    Step.ext (Generator.toStep_generator g B)
  rw [← hg]
  cases g with
  | invert => simp at he
  | mutate p =>
    obtain ⟨Ψ, hreg, hcomp, t, f, hq, ho, hfield⟩ :=
      exists_toric_boundary_valuation_transport_mutate b P hΦ hc s hform hcharge p
    obtain ⟨q, hq'⟩ := hfield
    exact ⟨Ψ, hreg, hcomp, t, f, by simpa using hform, hq, by simpa using ho,
      fun c ↦ q (c p), fun c ↦ hq' (c p)⟩
  | permute σ =>
    refine ⟨Φ, hΦ, hc, s ∘ σ, Function.Embedding.refl _, by simpa using hform, ?_, ?_, ?_⟩
    · rw [Step.chargeTarget_permute_charge, hcharge]
      apply (Pi.basisFun ℤ ι).ext
      intro j
      have hs : LinearEquiv.funCongrLeft ℤ ℤ σ.symm (Pi.single j 1) =
          Pi.single (σ j) 1 := by
        ext a
        simp [LinearEquiv.funCongrLeft_apply, Pi.single_apply, Equiv.symm_apply_eq]
      simp only [Pi.basisFun_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hs,
        rayChargeMap_single, Function.comp_apply]
    · intro ρ
      ext j
      simp [rayBoundaryOrders_apply]
    · exact ⟨fun _ ↦ AlgEquiv.refl, by simp⟩

/-- For an inversion-free word from a complete regular surface fan, there is a complete
regular terminal fan realizing the transported charges. All initial rays map injectively
to terminal rays, and the determinant orders at each image are the tropical word applied
to the corresponding initial orders. For each center character, the pullbacks along
the subdivisions and mutations give an isomorphism on function fields preserving
orders at every transported ray. -/
theorem exists_toric_boundary_valuation_transport {B C : SkewExchangeMatrix ι}
    (w : Word B C) (hw : w.inversionCount = 0) (P : ChargeSeed B N)
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (s : ι → Φ.Ray)
    (hform : P.form = b.detDualEquiv.toLinearMap) (hcharge : P.charge = rayChargeMap s) :
    ∃ (Ψ : Fan i) (hΨ : Ψ.IsRegular) (hΨc : Ψ.IsComplete) (t : ι → Ψ.Ray) (f : Φ.Ray ↪ Ψ.Ray),
      (w.chargeTarget P).form = b.detDualEquiv.toLinearMap ∧
      (w.chargeTarget P).charge = rayChargeMap t ∧
      (∀ ρ, rayBoundaryOrders b t (f ρ) =
        DFunLike.coe (F := Equiv.Perm (ι → ℤ)) ((trop).map w) (rayBoundaryOrders b s ρ)) ∧
      letI : Nonempty Φ.cones := hc.nonempty_cones
      letI : Nonempty Ψ.cones := hΨc.nonempty_cones
      ∃ q : χ → (K(Ψ) ≃ₐ[ℂ] K(Φ)), ∀ (c : χ) (ρ : Φ.Ray) (a : K(Ψ)),
        Φ.algebraicRealization.ord (q c a) (Φ.rayBoundaryPoint hΦ ρ).val =
          Ψ.algebraicRealization.ord a (Ψ.rayBoundaryPoint hΨ (f ρ)).val := by
  induction w with
  | nil =>
    refine ⟨Φ, hΦ, hc, s, Function.Embedding.refl _, ?_, ?_, ?_, ?_⟩
    · simpa using hform
    · simpa using hcharge
    · intro ρ
      simp [Paths.lift_nil, SingleObj.id_as_one]
    · exact ⟨fun _ ↦ AlgEquiv.refl, by simp⟩
  | cons w e ih =>
    rw [Path.inversionCount_cons, Nat.add_eq_zero_iff] at hw
    obtain ⟨Ω, hΩ, hΩc, t, f, hp, hq, ho, hfield⟩ := ih hw.1
    obtain ⟨Ψ, hΨ, hΨc, t', g, hp', hq', ho', hfield'⟩ :=
      exists_toric_boundary_valuation_transport_step b e hw.2 _ hΩ hΩc t hp hq
    refine ⟨Ψ, hΨ, hΨc, t', f.trans g, ?_, ?_, ?_, ?_⟩
    · simpa using hp'
    · simpa using hq'
    · intro ρ
      rw [Function.Embedding.trans_apply, ho', ho, tropical_map_cons_apply]
    · obtain ⟨q, hq⟩ := hfield
      obtain ⟨r, hr⟩ := hfield'
      refine ⟨fun c ↦ (r (fun j ↦ c (ofAdd (w.exponentEquiv (Pi.single j 1))))).trans (q c),
        fun c ρ a ↦ ?_⟩
      rw [AlgEquiv.trans_apply, hq, hr, Function.Embedding.trans_apply]

end TauCeti.Toric.Fan

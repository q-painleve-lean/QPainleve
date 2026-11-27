/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Mutation.Tower
public import QPainleve.Geometry.Toric.Fan.Subdivision.FunctionField

import QPainleve.AlgebraicGeometry.Blowup.Tower.IsoLocus
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Tower

/-!
# Toric mutation under subdivision

Subdividing a fan before applying the mutation shear subdivides the mutated fan.
The two resulting toric projections intertwine the elementary transformations
as rational maps. A point tower over the subdividing fan that resolves the coarse
mutation also resolves the refined mutation. The comparison uses the binomial
formula for pullback from [Gross, Hacking and Keel, §3.1][GHK].

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative PointedCone QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan.IsSubdivision

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ω : Fan i} (H : Ω.IsSubdivision Φ)
  (b : Module.Basis (Fin 2) ℤ N) {v w : N} (hvw : w = v) (hv : v ≠ 0) (hw : w ≠ 0)
  (hp : hull ℝ {i v} ∈ Φ.cones) (hn : hull ℝ {i (-v)} ∈ Φ.cones)
  (hp' : hull ℝ {i w} ∈ Ω.cones) (hn' : hull ℝ {i (-w)} ∈ Ω.cones)

local notation "Φ'" => Φ.mutationFan b hv hp hn
local notation "Ω'" => Ω.mutationFan b hw hp' hn'

include H hvw in
/-- Applying the same mutation shear to both fans preserves the subdivision. -/
theorem mutation : (Ω').IsSubdivision (Φ') := by
  subst w
  refine ⟨?_, ?_⟩
  · intro σ' hσ'
    obtain ⟨σ, hσ, he⟩ := (Ω.mem_mutationFan_cones b hv hp' hn').mp hσ'
    obtain ⟨τ, hτ, hστ⟩ := H.exists_cone_le hσ
    let τ' := Φ.mutationFanConeEquiv b hv hp hn ⟨τ, hτ⟩
    refine ⟨τ'.val, τ'.property, ?_⟩
    rw [← SetLike.coe_subset_coe, he, Φ.coe_mutationFanConeEquiv]
    exact Set.image_mono hστ
  · rw [support_mutationFan, support_mutationFan, H.support_eq]

section RationalMaps

variable (K : Type) [CommRing K] [IsDomain K]

local notation "π[" H "]" => FanHom.finiteFanSchemeHom K (toFanHom H)
local notation "H'" => H.mutation b hvw hv hw hp hn hp' hn'
local notation "q[" Δ "," c "," h₀ "," h₁ "," h₂ "]" =>
  Scheme.PartialMap.toRationalMap (Fan.mutationPartialMap K Δ b c h₀ h₁ h₂)

/-- The elementary transformations with the same pivot and coefficient commute with the
subdivision morphisms as rational maps. -/
theorem comp_mutationPartialMap (c : K) :
    letI : Nonempty Φ.cones := ⟨⟨_, hp⟩⟩
    letI : Nonempty Ω.cones := ⟨⟨_, hp'⟩⟩
    letI : Nonempty (Φ').cones := ⟨Φ.mutationFanConeEquiv b hv hp hn ⟨_, hp⟩⟩
    letI : Nonempty (Ω').cones := ⟨Ω.mutationFanConeEquiv b hw hp' hn' ⟨_, hp'⟩⟩
    (π[H]).toRationalMap.comp q[Φ,c,hv,hp,hn] =
      q[Ω,c,hw,hp',hn'].comp (π[H']).toRationalMap := by
  subst w
  let : Nonempty Φ.cones := ⟨⟨_, hp⟩⟩
  let : Nonempty Ω.cones := ⟨⟨_, hp'⟩⟩
  let : Nonempty (Φ').cones := ⟨Φ.mutationFanConeEquiv b hv hp hn ⟨_, hp⟩⟩
  let : Nonempty (Ω.mutationFan b hv hp' hn').cones :=
    ⟨Ω.mutationFanConeEquiv b hv hp' hn' ⟨_, hp'⟩⟩
  apply (Scheme.RationalMap.functionFieldMap_eq_iff _ _).mp
  simp only [Scheme.RationalMap.functionFieldMap_comp, Scheme.Hom.functionFieldMap_toRationalMap,
    functionFieldMap_mutationPartialMap_toRationalMap]
  let f := (π[H]).functionFieldAlgHom K
  let g := (π[H.mutation b rfl hv hv hp hn hp' hn']).functionFieldAlgHom K
  let μ := Φ.mutationComplementPullbackAlgHom b c hv hp hn
  let ν := Ω.mutationComplementPullbackAlgHom b c hv hp' hn'
  have he : f.comp μ = ν.comp g := by
    apply (Φ').functionFieldCharacter_algHom_ext K
    intro m
    obtain ⟨m, rfl⟩ := ofAdd.surjective m
    simp only [f, g, μ, ν, AlgHom.comp_apply, Scheme.Hom.functionFieldAlgHom_apply,
      mutationComplementPullbackAlgHom_apply, mutationComplementPullback_character,
      map_mul, map_add, map_one, map_zpow₀, Scheme.Hom.functionFieldMap_algebraMap K,
      FanHom.functionFieldMap_finiteFanSchemeHom_character, toFanHom_latticeMap,
      AddMonoidHom.comp_id]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  simpa only [CommRingCat.comp_apply, f, g, μ, ν, AlgHom.comp_apply,
    Scheme.Hom.functionFieldAlgHom_apply, mutationComplementPullbackAlgHom_apply]
    using DFunLike.congr_fun he x

end RationalMaps

section Resolution

variable (K : Type) [Field K] [PerfectField K] {N V : Type}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ω : Fan i} (H : Ω.IsSubdivision Φ)
  (b : Module.Basis (Fin 2) ℤ N) (ρ : Φ.Ray)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : Kˣ)

local notation "π[" H "]" => FanHom.finiteFanSchemeHom K (toFanHom H)
local notation "σ" => H.liftRay ρ

/-- The opposite pivot ray is retained when lifting a pivot ray to a subdivision. -/
theorem hull_neg_primitiveGenerator_liftRay_mem
    (h : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) :
    hull ℝ {i (-(σ).primitiveGenerator)} ∈ Ω.cones := by
  simpa only [primitiveGenerator_liftRay, Ray.ofPrimitiveGenerator_toCone] using
    H.ray_mem (Ray.ofPrimitiveGenerator ρ.isPrimitiveGenerator.isPrimitive.neg h)

local notation "hOpp'" => H.hull_neg_primitiveGenerator_liftRay_mem ρ hOpp
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "X[" Δ "]" => Fan.finiteFanScheme K Δ
local notation "s[" Δ "]" => Fan.finiteFanSchemeToSpec K Δ
local notation "M[" Δ "," r "," h "]" =>
  Fan.mutationFan Δ b (Ray.primitiveGenerator_ne_zero r) (Ray.hull_primitiveGenerator_mem r) h
local notation "μ[" Δ "," r "," h "]" =>
  Scheme.PartialMap.toRationalMap (Fan.mutationPartialMap K Δ b (c : K)
    (Ray.primitiveGenerator_ne_zero r) (Ray.hull_primitiveGenerator_mem r) h)
local notation "Hμ" => H.mutation b (H.primitiveGenerator_liftRay ρ)
  ρ.primitiveGenerator_ne_zero (Ray.primitiveGenerator_ne_zero σ)
  ρ.hull_primitiveGenerator_mem hOpp (Ray.hull_primitiveGenerator_mem σ) hOpp'
local notation "center[" r "]" => Ray.binomialCenter r K rankTwo
  (b.detDualEquiv_self (Ray.primitiveGenerator r)) (Ray.surjective_detCharacter r b) c
local notation "p[" r "]" => (center[r]) (IsLocalRing.closedPoint K)

variable {n : ℕ} {Z : Scheme} {T : BlowupTower (Ω.finiteFanScheme K) n Z}
  (hT : IsClosedPointTower (Ω.finiteFanScheme K) T) (hΦ : Φ.IsRegular) (hΩ : Ω.IsRegular)

include hT hΦ hΩ in
private theorem liftRayCenter_mem_range_of_resolves (r : Z ⟶ X[M[Φ,ρ,hOpp]]) :
    letI : Nonempty Ω.cones := ⟨(σ).toCone⟩
    letI : Nonempty Φ.cones := ⟨ρ.toCone⟩
    letI : SmoothOfRelativeDimension 2 s[Ω] :=
      rankTwo ▸ Ω.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΩ
    letI : IsIntegral Z := hT.isIntegral s[Ω]
    letI : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two s[Ω]
    (T.toBase ≫ π[H]).toRationalMap.comp μ[Φ,ρ,hOpp] = r.toRationalMap →
      p[σ] ∈ Set.range hT.baseCenter := by
  let : Nonempty Ω.cones := ⟨(σ).toCone⟩
  let : Nonempty Φ.cones := ⟨ρ.toCone⟩
  let : SmoothOfRelativeDimension 2 s[Ω] :=
    rankTwo ▸ Ω.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΩ
  let := hT.isIntegral s[Ω]
  let := hT.isModification_of_smoothOfRelativeDimension_two s[Ω]
  have : Surjective T.toBase := hT.surjective s[Ω]
  obtain ⟨_, _, U, e, _, he, -, -⟩ :=
    H.exists_toric_subdivision_blowup_tower K hΦ hΩ inferInstance rankTwo
  have : IsProper U.toBase := U.isProper_toBase
  have : IsProper (π[H]) := he ▸ inferInstanceAs (IsProper (e.hom ≫ U.toBase))
  have hloc : p[ρ] ∈ (π[H]).isoLocus := H.range_binomialCenter_subset_isoLocus K ρ rankTwo
    (b.detDualEquiv_self ρ.primitiveGenerator) (ρ.surjective_detCharacter b) c
    (Set.mem_range_self _)
  have hp : (π[H]) p[σ] = p[ρ] := calc
    _ = ((center[σ]) ≫ π[H]) (IsLocalRing.closedPoint K) :=
      (Scheme.Hom.comp_apply (center[σ]) (π[H]) _).symm
    _ = p[ρ] := congrArg (fun f : Spec (.of K) ⟶ X[Φ] ↦ f (IsLocalRing.closedPoint K))
      (H.binomialCenter_liftRay_comp_finiteFanSchemeHom K ρ b c)
  intro hr
  have hcoarse := ρ.mutationSourceCenter_mem_centre_of_resolves K b hOpp c (T.toBase ≫ π[H]) r hr
  rw [Scheme.Hom.centre_comp] at hcoarse
  obtain ⟨z, hz, hzρ⟩ := hcoarse.resolve_left (by simpa only [Scheme.Hom.centre_def,
    Set.mem_compl_iff, not_not, SetLike.mem_coe] using hloc)
  have hzσ : z = p[σ] := (π[H]).injOn_preimage_isoLocus
    (by simpa only [Set.mem_preimage, hzρ, SetLike.mem_coe] using hloc)
    (by simpa only [Set.mem_preimage, hp, SetLike.mem_coe] using hloc) (hzρ.trans hp.symm)
  rw [← hT.centre_toBase_eq_range_baseCenter s[Ω], ← hzσ]
  exact hz

include hΦ in
/-- A specified point tower over a regular subdivision that resolves the coarse elementary
transformation also resolves the refined transformation. The unique regular morphism to
the refined target projects to the specified morphism to the coarse target. -/
theorem existsUnique_mutation_resolution (r : Z ⟶ X[M[Φ,ρ,hOpp]]) :
    letI : Nonempty Ω.cones := ⟨(σ).toCone⟩
    letI : Nonempty Φ.cones := ⟨ρ.toCone⟩
    letI : SmoothOfRelativeDimension 2 s[Ω] :=
      rankTwo ▸ Ω.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΩ
    letI : IsIntegral Z := hT.isIntegral s[Ω]
    letI : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two s[Ω]
    (T.toBase ≫ π[H]).toRationalMap.comp μ[Φ,ρ,hOpp] = r.toRationalMap →
      ∃! g : Z ⟶ X[M[Ω,σ,hOpp']],
        T.toBase.toRationalMap.comp μ[Ω,σ,hOpp'] = g.toRationalMap ∧ g ≫ π[Hμ] = r := by
  let : Nonempty Ω.cones := ⟨(σ).toCone⟩
  let : Nonempty Φ.cones := ⟨ρ.toCone⟩
  let : Nonempty (M[Φ,ρ,hOpp]).cones := ⟨Φ.mutationFanConeEquiv b _ _ hOpp ρ.toCone⟩
  let : Nonempty (M[Ω,σ,hOpp']).cones := ⟨Ω.mutationFanConeEquiv b _ _ hOpp' (σ).toCone⟩
  let : SmoothOfRelativeDimension 2 s[Ω] :=
    rankTwo ▸ Ω.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΩ
  let := hT.isIntegral s[Ω]
  let := hT.isModification_of_smoothOfRelativeDimension_two s[Ω]
  intro hr
  have hp := liftRayCenter_mem_range_of_resolves K H b ρ hOpp c hT hΦ hΩ r hr
  obtain ⟨g, hg, huniq⟩ :=
    ((σ).existsUnique_mutation_resolution_of_closedPointTower_iff K b hOpp' c hT hΩ).mpr hp
  refine ⟨g, ⟨hg, ?_⟩, fun q hq ↦ huniq q hq.1⟩
  have hcomm := H.comp_mutationPartialMap (K := K) b (H.primitiveGenerator_liftRay ρ)
    ρ.primitiveGenerator_ne_zero (σ).primitiveGenerator_ne_zero
    ρ.hull_primitiveGenerator_mem hOpp (σ).hull_primitiveGenerator_mem hOpp' (c : K)
  have : Scheme.IsSeparated X[M[Φ,ρ,hOpp]] := inferInstance
  apply Scheme.Hom.toRationalMap_injective
  simpa only [← Scheme.Hom.toRationalMap_compHom, ← Scheme.RationalMap.comp_toRationalMap,
    Scheme.RationalMap.comp_assoc, ← hg, ← hcomm] using hr

end Resolution

end TauCeti.Toric.Fan.IsSubdivision

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Tropical.Basic
public import QPainleve.Geometry.Toric.Fan.Mutation.Pullback
import QPainleve.Geometry.Toric.Fan.Boundary.Binomial
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Boundary valuations under toric mutation

Every generic point of the toric boundary lies in the complement of the pivot fiber.
The mutation isomorphism on that complement sends it to the generic point of the ray
given by the integral shear. Consequently the corresponding orders agree on all
rational functions under pullback. The character calculation uses the binomial twist
of Gross, Hacking and Keel, [*Birational geometry of cluster algebras*, §3.1][GHK].
For the labeled center characters, the induced change of boundary orders is
tropical Y-seed mutation.

[GHK]: https://arxiv.org/html/1309.2573v2#S3.SS1
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra Multiplicative
open TauCeti.AlgebraicGeometry (CodimensionOnePoint)
open TauCeti.AlgebraicGeometry.Scheme (ord_functionFieldMap)

namespace TauCeti.Toric.Fan

variable {K : Type} [CommRing K] [IsDomain K] [IsNoetherianRing K]
  {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i) (b : Module.Basis (Fin 2) ℤ N) {v : N} (c : Kˣ)

/-- Every toric boundary prime lies in the open complement of the pivot fiber. -/
theorem rayBoundaryPoint_mem_mutationComplement (hv : v ≠ 0)
    (h : ∀ σ : Φ.cones,
      (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter (b.detDualEquiv v).toAddMonoidHom x) ∨
        ∀ x ∈ σ.val, Φ.lattice.realCharacter (b.detDualEquiv v).toAddMonoidHom x ≤ 0)
    (hΦ : Φ.IsRegular) (ρ : Φ.Ray) :
    (Φ.rayBoundaryChartPoint (R := K) hΦ ρ).val ∈ Φ.mutationComplement b h (c : K) := by
  let σ := ρ.toCone
  let hσ := Φ.isToricCone σ.property
  let hreg := (isRegular_iff.1 hΦ) _ σ.property
  let r := ρ.toToricRay Φ σ le_rfl
  obtain ⟨side, hs⟩ := Φ.exists_mutationChartCharacter_mem_dualSemigroup b σ (h σ)
  let q : dualSemigroup Φ.lattice σ.val := ⟨mutationChartCharacter b side, hs⟩
  have hq : q ≠ 0 := fun h ↦
    hv ((mutationChartCharacter_eq_zero_iff b side).mp (congrArg Subtype.val h))
  have ha : (cond side (c : K) 1) ≠ 0 := by cases side <;> simp
  have hp := hreg.rayChartPoint_mem_basicOpen_binomial K Φ.lattice hσ r hq ha
    (cond side 1 (c : K))
  change (hreg.rayChartPoint Φ.lattice hσ r K).val ∈
    PrimeSpectrum.basicOpen (Φ.mutationChartBinomial side (c : K) q) at hp
  rw [← Φ.affineChartι_preimage_mutationComplement b σ side hs (c : K) h] at hp
  rw [coe_rayBoundaryChartPoint]
  exact (Scheme.Hom.mem_preimage _).mp hp

variable (hv : v ≠ 0) (hpos : PointedCone.hull ℝ {i v} ∈ Φ.cones)
  (hneg : PointedCone.hull ℝ {i (-v)} ∈ Φ.cones)

local notation "Ψ" => Φ.mutationFan b hv hpos hneg
local notation "h₀" => Φ.detCharacter_nonneg_or_nonpos b hv hpos hneg
local notation "h₁" => Φ.mutationDetCharacter_nonneg_or_nonpos b hv hpos hneg
local notation "U₀" => Φ.mutationComplement b h₀ (c : K)
local notation "U₁" => mutationComplement (Ψ) b h₁ (c : K)
local notation "e" => Φ.mutationComplementIso b (c : K) hv hpos hneg
local notation "pb" => Φ.mutationComplementPullback b (c : K) hv hpos hneg

include hv hpos hneg in
private theorem ord_mutationComplementPullback (x : (U₀).toScheme) :
    letI : Nonempty Φ.cones := ⟨⟨_, hpos⟩⟩
    letI : Nonempty (Ψ).cones := ⟨Φ.mutationFanConeEquiv b hv hpos hneg ⟨_, hpos⟩⟩
    ∀ f : ((Ψ).finiteFanScheme K).functionField,
      (Φ.finiteFanScheme K).ord (pb f) ((U₀).ι x) =
        ((Ψ).finiteFanScheme K).ord f (((e).hom ≫ (U₁).ι) x) := by
  let : Nonempty Φ.cones := ⟨⟨_, hpos⟩⟩
  let : Nonempty (Ψ).cones := ⟨Φ.mutationFanConeEquiv b hv hpos hneg ⟨_, hpos⟩⟩
  intro f
  let := Φ.isIntegral_mutationComplement_source b (c : K) hv hpos hneg
  let := Φ.isIntegral_mutationComplement_target b (c : K) hv hpos hneg
  have := isLocallyNoetherian_of_isOpenImmersion (U₀).ι
  rw [← ord_functionFieldMap (U₀).ι, ← ord_functionFieldMap ((e).hom ≫ (U₁).ι)]
  exact congrArg (fun g ↦ (U₀).toScheme.ord g x) (by
    simpa only [CommRingCat.comp_apply] using ConcreteCategory.congr_hom
      (Φ.mutationComplementPullback_comp_functionFieldMap b (c : K) hv hpos hneg) f)

include hv hpos hneg in
private theorem ord_mutationComplementPullback_character (hΦ : Φ.IsRegular) (ρ : Φ.Ray)
    (a : N →+ ℤ) :
    letI : Nonempty Φ.cones := ⟨⟨_, hpos⟩⟩
    letI : Nonempty (Ψ).cones := ⟨Φ.mutationFanConeEquiv b hv hpos hneg ⟨_, hpos⟩⟩
    (Φ.finiteFanScheme K).ord (pb ((Ψ).functionFieldCharacter K (ofAdd a)))
        (Φ.rayBoundaryChartPoint (R := K) hΦ ρ).val =
      a (Φ.mutationFanRayEquiv b hv hpos hneg ρ).primitiveGenerator := by
  let : Nonempty Φ.cones := ⟨⟨_, hpos⟩⟩
  let : Nonempty (Ψ).cones := ⟨Φ.mutationFanConeEquiv b hv hpos hneg ⟨_, hpos⟩⟩
  have hm : mutationChartCharacter b (v := v) false ≠ 0 := by simpa only
    [ne_eq, mutationChartCharacter_eq_zero_iff] using hv
  obtain ⟨hne, ho⟩ := Φ.ord_rayBoundaryChartPoint_one_add_mul_character K hΦ ρ c
    (by simpa only [mutationChartCharacter_false] using hm)
  have ha := ((Group.isUnit (ofAdd a)).map (Φ.functionFieldCharacter K)).ne_zero
  rw [mutationComplementPullback_character, Scheme.ord_mul ha (zpow_ne_zero _ hne),
    Scheme.ord_zpow, ord_rayBoundaryChartPoint_character K, ho,
    mutationFanRayEquiv_primitiveGenerator, map_add, map_zsmul]
  have h := b.detDualEquiv_swap v ρ.primitiveGenerator
  simp only [LinearMap.toAddMonoidHom_coe, Module.Basis.detDualEquiv_apply] at h ⊢
  have hmin : min 0 (-b.det ![ρ.primitiveGenerator, v]) =
      -max (b.det ![ρ.primitiveGenerator, v]) 0 := by
    simpa only [neg_zero, max_comm] using min_neg_neg (0 : ℤ) (b.det ![ρ.primitiveGenerator, v])
  rw [h, hmin, smul_eq_mul]
  ring

include hv hpos hneg in
/-- The mutation isomorphism takes the generic point of a ray divisor to the generic
point of the sheared ray divisor. -/
theorem mutationComplementIso_hom_rayBoundaryPoint (hΦ : Φ.IsRegular) (ρ : Φ.Ray) :
    ((e).hom ≫ (U₁).ι)
        ⟨(Φ.rayBoundaryChartPoint (R := K) hΦ ρ).val,
          Φ.rayBoundaryPoint_mem_mutationComplement b c hv h₀ hΦ ρ⟩ =
      ((Ψ).rayBoundaryChartPoint (R := K) ((Φ.isRegular_mutationFan_iff b hv hpos hneg).mpr hΦ)
        (Φ.mutationFanRayEquiv b hv hpos hneg ρ)).val := by
  let j := (e).hom ≫ (U₁).ι
  let x : (U₀).toScheme := ⟨_, Φ.rayBoundaryPoint_mem_mutationComplement b c hv h₀ hΦ ρ⟩
  have hx : (U₀).ι x = (Φ.rayBoundaryChartPoint (R := K) hΦ ρ).val := Scheme.Opens.ι_apply _ _
  let hΨ := (Φ.isRegular_mutationFan_iff b hv hpos hneg).mpr hΦ
  let τ := Φ.mutationFanRayEquiv b hv hpos hneg ρ
  let hΦ₀ : Nonempty Φ.cones := ⟨ρ.toCone⟩
  let hΨ₀ : Nonempty (Ψ).cones := ⟨τ.toCone⟩
  have hx' : Order.coheight x = 1 := by
    rw [← coheight_eq_of_isOpenImmersion (U₀).ι, hx]
    exact (Φ.rayBoundaryChartPoint (R := K) hΦ ρ).property
  let y := CodimensionOnePoint.mapOfIsOpenImmersion j ⟨x, hx'⟩
  let hbot := (Ψ).bot_mem hΨ₀.some.property
  have hy : y.val ∉ Set.range ((Ψ).affineChartι K ⟨⊥, hbot⟩) := by
    have ht := Φ.mutationComplementIso_preimage_range_denseTorusι b (c : K)
      hv hpos hneg hΦ₀ hΨ₀
    rw [CodimensionOnePoint.coe_mapOfIsOpenImmersion]
    exact fun h ↦ Φ.rayBoundaryChartPoint_notMem_zeroChart (R := K) hΦ ρ
      (Φ.bot_mem hΦ₀.some.property)
      (hx ▸ (Set.ext_iff.mp ht x).mp h)
  obtain ⟨σ, hσ⟩ : y ∈ Set.range ((Ψ).rayBoundaryChartPoint (R := K) hΨ) :=
    ((Ψ).range_rayBoundaryChartPoint (R := K) hΨ hbot).symm ▸ hy
  have hpoint : ((Ψ).rayBoundaryChartPoint (R := K) hΨ σ).val = j x :=
    (congrArg Subtype.val hσ).trans (CodimensionOnePoint.coe_mapOfIsOpenImmersion j _)
  have hgen (a : N →+ ℤ) : a σ.primitiveGenerator = a τ.primitiveGenerator := by
    let := hΨ₀
    rw [← (Ψ).ord_rayBoundaryChartPoint_character K hΨ σ, hpoint,
      ← ord_mutationComplementPullback Φ b c hv hpos hneg x, hx]
    exact Φ.ord_mutationComplementPullback_character b c hv hpos hneg hΦ ρ a
  have hστ : σ = τ := Ray.primitiveGenerator_injective <|
    b.ext_elem_iff.mpr (fun k ↦ hgen (b.coord k).toAddMonoidHom)
  simpa only [hστ] using hpoint.symm

include hv hpos hneg in
/-- Orders of rational functions at toric boundary rays are transported by the
mutation isomorphism, with ray labels given by the integral shear. -/
theorem ord_mutationComplementPullback_rayBoundaryPoint (hΦ : Φ.IsRegular) (ρ : Φ.Ray) :
    letI : Nonempty Φ.cones := ⟨⟨_, hpos⟩⟩
    letI : Nonempty (Ψ).cones := ⟨Φ.mutationFanConeEquiv b hv hpos hneg ⟨_, hpos⟩⟩
    ∀ f : ((Ψ).finiteFanScheme K).functionField,
      (Φ.finiteFanScheme K).ord (pb f) (Φ.rayBoundaryChartPoint (R := K) hΦ ρ).val =
        ((Ψ).finiteFanScheme K).ord f
          ((Ψ).rayBoundaryChartPoint (R := K) ((Φ.isRegular_mutationFan_iff b hv hpos hneg).mpr hΦ)
            (Φ.mutationFanRayEquiv b hv hpos hneg ρ)).val := by
  intro f
  let x : (U₀).toScheme := ⟨_, Φ.rayBoundaryPoint_mem_mutationComplement b c hv h₀ hΦ ρ⟩
  have hx : (U₀).ι x = (Φ.rayBoundaryChartPoint (R := K) hΦ ρ).val := Scheme.Opens.ι_apply _ _
  rw [← hx, ord_mutationComplementPullback, mutationComplementIso_hom_rayBoundaryPoint]

section CenterRays

open QPainleve.Cluster

variable {ι : Type*} [DecidableEq ι] (s : ι → Φ.Ray) (k : ι)
  (hOpp : PointedCone.hull ℝ {i (-(s k).primitiveGenerator)} ∈ Φ.cones)

local notation "v(" j ")" => Ray.primitiveGenerator (s j)
local notation "hvₖ" => IsPrimitiveGenerator.ne_zero (Ray.isPrimitiveGenerator (s k))
local notation "h₊" => Ray.hull_primitiveGenerator_mem (s k)
local notation "Φ'" => Φ.mutationFan b hvₖ h₊ hOpp
local notation "s'" => Φ.mutationFanCenterRays b s k hOpp
local notation "ρ'(" ρ ")" => Φ.mutationFanRayEquiv b hvₖ h₊ hOpp ρ
local notation "d" => b.detDualEquiv

/-- The integer valuation row of the center characters at the sheared ray
is the tropical mutation of the original row. Only the pivot column of the
exchange matrix enters this calculation. -/
theorem tropical_mutate_eq_rayPairing_mutationFanRayEquiv (B : SkewExchangeMatrix ι)
    (hB : ∀ j, B.matrix j k = d v(j) v(k)) (ρ : Φ.Ray) :
    (Generator.mutate k).tropical B (fun j ↦ d v(j) ρ.primitiveGenerator) =
      fun j ↦ d ((s') j).primitiveGenerator (ρ'(ρ)).primitiveGenerator := by
  funext j
  by_cases hj : j = k
  · subst j
    rw [Generator.tropical_mutate_self, mutationFanCenterRays_primitiveGenerator_self,
      mutationFanRayEquiv_primitiveGenerator, map_neg, LinearMap.neg_apply, map_add, map_zsmul,
      b.detDualEquiv_self, smul_zero, add_zero]
  · rw [Generator.tropical_mutate_of_ne B _ hj, hB, mutationFanCenterRays_primitiveGenerator_of_ne
      Φ b s k hOpp hj, mutationFanRayEquiv_primitiveGenerator]
    have hmin : min 0 (d v(k) ρ.primitiveGenerator) =
        -max (b.det ![ρ.primitiveGenerator, v(k)]) 0 := by
      rw [b.detDualEquiv_swap v(k) ρ.primitiveGenerator, b.detDualEquiv_apply]
      simpa only [neg_zero, max_comm] using
        min_neg_neg (0 : ℤ) (b.det ![ρ.primitiveGenerator, v(k)])
    rw [hmin]
    simp only [posPart_def, ← b.detDualEquiv_apply, map_add, map_zsmul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, b.detDualEquiv_self, mul_zero, add_zero]
    ring

/-- Pulling back the mutated center characters gives the tropical update of the
source boundary valuation row. The target center parameters can be any nonzero
scalars, since constants have order zero along every boundary ray. -/
theorem ord_mutationComplementPullback_centerCharacter (B : SkewExchangeMatrix ι)
    (hB : ∀ j, B.matrix j k = d v(j) v(k)) (hΦ : Φ.IsRegular) (ρ : Φ.Ray)
    (cₖ : Kˣ) (a : ι → Kˣ) :
    letI : Nonempty Φ.cones := ⟨(s k).toCone⟩
    letI : Nonempty (Φ').cones := ⟨(ρ'(ρ)).toCone⟩
    ∀ j, (Φ.finiteFanScheme K).ord
      (Φ.mutationComplementPullback b (cₖ : K) hvₖ h₊ hOpp
        (algebraMap K ((Φ').finiteFanScheme K).functionField (a j : K) *
          (Φ').functionFieldCharacter K (ofAdd (d ((s') j).primitiveGenerator).toAddMonoidHom)))
      (Φ.rayBoundaryChartPoint (R := K) hΦ ρ).val =
      (Generator.mutate k).tropical B (fun l ↦ d v(l) ρ.primitiveGenerator) j := by
  let : Nonempty Φ.cones := ⟨(s k).toCone⟩
  let : Nonempty (Φ').cones := ⟨(ρ'(ρ)).toCone⟩
  intro j
  rw [ord_mutationComplementPullback_rayBoundaryPoint, ord_rayBoundaryChartPoint_mul_character K,
    tropical_mutate_eq_rayPairing_mutationFanRayEquiv Φ b s k hOpp B hB ρ]
  rfl

end CenterRays

end TauCeti.Toric.Fan

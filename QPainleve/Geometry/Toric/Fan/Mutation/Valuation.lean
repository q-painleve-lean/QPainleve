/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Tropical.Basic
public import QPainleve.Geometry.Toric.Fan.Boundary.Basic
public import QPainleve.Geometry.Toric.Fan.Mutation.Pullback
import QPainleve.AlgebraicGeometry.Scheme.FunctionField
import QPainleve.Geometry.Toric.Fan.Boundary.Binomial
import QPainleve.Geometry.Toric.Fan.Mutation.Charge
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Equiv
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order
import TauCeti.Geometry.Toric.Algebraic.BaseChange.Complex

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

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i) (b : Module.Basis (Fin 2) ℤ N) {v : N} (c : ℂˣ)

private theorem rayChartPoint_eq (ρ : Φ.Ray) (hΦ : Φ.IsRegular) :
    let σ := ρ.toCone
    let hσ := Φ.isToricCone σ.property
    let hreg := (isRegular_iff.1 hΦ) _ σ.property
    let r := ρ.toToricRay Φ σ le_rfl
    let e := toMultiplicativeAlgEquiv ℂ ℂ (dualSemigroup Φ.lattice σ.val)
    Spec.map (CommRingCat.ofHom ↑e) (hreg.rayPoint Φ.lattice hσ r).val =
      (hreg.rayChartPoint Φ.lattice hσ r ℂ).val := by
  dsimp only
  let σ := ρ.toCone
  let hσ := Φ.isToricCone σ.property
  let hreg := (isRegular_iff.1 hΦ) _ σ.property
  let r := ρ.toToricRay Φ σ le_rfl
  let e := toMultiplicativeAlgEquiv ℂ ℂ (dualSemigroup Φ.lattice σ.val)
  apply PrimeSpectrum.ext
  change Ideal.comap e.toRingEquiv ((hreg.rayPoint Φ.lattice hσ r).val.asIdeal) = _
  rw [hreg.rayPoint_asIdeal, hreg.rayChartPoint_asIdeal]
  trans (rayIdeal Φ.lattice hσ r).map e.toRingEquiv.symm
  · exact Ideal.comap_symm e.toRingEquiv.symm
  obtain ⟨l, basis, hbase⟩ := hreg.exists_basis_sum
  rw [rayChartIdeal_eq_span_rayCoordinate _ _ _ _ hbase, rayIdeal_eq_span _ _ hbase,
    Ideal.map_span, Set.image_singleton]
  simp only [← AlgEquiv.symm_toRingEquiv, AlgEquiv.coe_toRingEquiv, e,
    toMultiplicativeAlgEquiv_symm_single, toAdd_ofAdd, MonoidAlgebra.of_apply]
  rfl

private theorem rayBoundaryChartPoint_apply (hΦ : Φ.IsRegular) (ρ : Φ.Ray) :
    Φ.finiteFanSchemeComplexIso.hom (Φ.rayBoundaryChartPoint (R := ℂ) hΦ ρ).val =
      (Φ.rayBoundaryPoint hΦ ρ).val := by
  rw [coe_rayBoundaryChartPoint, coe_rayBoundaryPoint, ← Scheme.Hom.comp_apply,
    Φ.affineChartι_finiteFanSchemeComplexIso_hom,
    affineToricSchemeIsoAddMonoidAlgebraSpec_inv_left, Scheme.Hom.comp_apply,
    ← rayChartPoint_eq Φ ρ hΦ]
  have h := Φ.specMap_toMultiplicativeAlgEquiv_comp_additiveAffineToricChartι ρ.toCone
  simpa only [Φ.additiveAffineToricChartι_def, Scheme.Hom.comp_apply]
    using congrArg (fun f ↦ f ((isRegular_iff.1 hΦ _ ρ.toCone.property).rayPoint Φ.lattice
      (Φ.isToricCone ρ.toCone.property) (ρ.toToricRay Φ ρ.toCone le_rfl)).val) h

private theorem functionFieldMap_finiteFanSchemeComplexIso_character
    [Nonempty Φ.cones] (m : N →+ ℤ) :
    Φ.finiteFanSchemeComplexIso.hom.functionFieldMap (Φ.character (ofAdd m)) =
      Φ.functionFieldCharacter ℂ (ofAdd m) := by
  let σ : Φ.cones := ⟨⊥, Φ.bot_mem (Nonempty.some inferInstance : Φ.cones).property⟩
  let a : dualSemigroup Φ.lattice σ.val := ⟨m, by simp [σ]⟩
  have hchart : Φ.affineChartι ℂ σ ≫ Φ.finiteFanSchemeComplexIso.hom =
      Φ.additiveAffineToricChartι σ := by
    rw [Φ.affineChartι_finiteFanSchemeComplexIso_hom,
      affineToricSchemeIsoAddMonoidAlgebraSpec_inv_left, Φ.additiveAffineToricChartι_def]
  apply (Φ.affineChartι ℂ σ).functionFieldMap.hom.injective
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.functionFieldMap_comp,
    Scheme.Hom.functionFieldMap_congr hchart,
    Φ.functionFieldMap_affineChartι_character ℂ σ a]
  exact Φ.functionFieldMap_additiveAffineToricChartι_character σ a

/-- Every toric boundary prime lies in the open complement of the pivot fiber. -/
theorem rayBoundaryPoint_mem_mutationComplement (hv : v ≠ 0)
    (h : ∀ σ : Φ.cones,
      (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter (b.detDualEquiv v).toAddMonoidHom x) ∨
        ∀ x ∈ σ.val, Φ.lattice.realCharacter (b.detDualEquiv v).toAddMonoidHom x ≤ 0)
    (hΦ : Φ.IsRegular) (ρ : Φ.Ray) :
    (Φ.rayBoundaryPoint hΦ ρ).val ∈ Φ.mutationComplement b h (c : ℂ) := by
  let σ := ρ.toCone
  let hσ := Φ.isToricCone σ.property
  let hreg := (isRegular_iff.1 hΦ) _ σ.property
  let r := ρ.toToricRay Φ σ le_rfl
  obtain ⟨side, hs⟩ := Φ.exists_mutationChartCharacter_mem_dualSemigroup b σ (h σ)
  let q : dualSemigroup Φ.lattice σ.val := ⟨mutationChartCharacter b side, hs⟩
  let p := hreg.rayPoint Φ.lattice hσ r
  let A := toMultiplicativeAlgEquiv ℂ ℂ (dualSemigroup Φ.lattice σ.val)
  have hq : q ≠ 0 := fun h ↦
    hv ((mutationChartCharacter_eq_zero_iff b side).mp (congrArg Subtype.val h))
  have ha : (cond side (c : ℂ) 1) ≠ 0 := by cases side <;> simp
  let y : PrimeSpectrum (AddMonoidAlgebra ℂ (dualSemigroup Φ.lattice σ.val)) :=
    Spec.map (CommRingCat.ofHom ↑A) p.val
  have hy : y ∈ PrimeSpectrum.basicOpen (Φ.mutationChartBinomial side (c : ℂ) q) := by
    rw [show y = (hreg.rayChartPoint Φ.lattice hσ r ℂ).val from rayChartPoint_eq Φ ρ hΦ,
      mutationChartBinomial]
    exact hreg.rayChartPoint_mem_basicOpen_binomial ℂ Φ.lattice hσ r hq ha
      (cond side 1 (c : ℂ))
  rw [← Φ.additiveAffineToricChartι_preimage_mutationComplement b σ side hs (c : ℂ) h]
    at hy
  rw [coe_rayBoundaryPoint, ← Φ.specMap_toMultiplicativeAlgEquiv_comp_additiveAffineToricChartι σ,
    Scheme.Hom.comp_apply]
  exact (Scheme.Hom.mem_preimage _).mp hy

variable (hv : v ≠ 0) (hpos : PointedCone.hull ℝ {i v} ∈ Φ.cones)
  (hneg : PointedCone.hull ℝ {i (-v)} ∈ Φ.cones)

local notation "Ψ" => Φ.mutationFan b hv hpos hneg
local notation "h₀" => Φ.detCharacter_nonneg_or_nonpos b hv hpos hneg
local notation "h₁" => Φ.mutationDetCharacter_nonneg_or_nonpos b hv hpos hneg
local notation "U₀" => Φ.mutationComplement b h₀ (c : ℂ)
local notation "U₁" => mutationComplement (Ψ) b h₁ (c : ℂ)
local notation "e" => Φ.mutationComplementIso b (c : ℂ) hv hpos hneg
local notation "pb" => Φ.mutationComplementPullback b (c : ℂ) hv hpos hneg

include hv hpos hneg in
private theorem ord_mutationComplementPullback (x : (U₀).toScheme) :
    letI : Nonempty Φ.cones := ⟨⟨_, hpos⟩⟩
    letI : Nonempty (Ψ).cones := ⟨Φ.mutationFanConeEquiv b hv hpos hneg ⟨_, hpos⟩⟩
    ∀ f : (Ψ).algebraicRealization.functionField,
      Φ.algebraicRealization.ord (pb f) ((U₀).ι x) =
        (Ψ).algebraicRealization.ord f (((e).hom ≫ (U₁).ι) x) := by
  let : Nonempty Φ.cones := ⟨⟨_, hpos⟩⟩
  let : Nonempty (Ψ).cones := ⟨Φ.mutationFanConeEquiv b hv hpos hneg ⟨_, hpos⟩⟩
  intro f
  let := Φ.isIntegral_mutationComplement_source b (c : ℂ) hv hpos hneg
  let := Φ.isIntegral_mutationComplement_target b (c : ℂ) hv hpos hneg
  have := isLocallyNoetherian_of_isOpenImmersion (U₀).ι
  rw [← ord_functionFieldMap (U₀).ι, ← ord_functionFieldMap ((e).hom ≫ (U₁).ι)]
  exact congrArg (fun g ↦ (U₀).toScheme.ord g x) (by
    simpa only [CommRingCat.comp_apply] using ConcreteCategory.congr_hom
      (Φ.mutationComplementPullback_comp_functionFieldMap b (c : ℂ) hv hpos hneg) f)

include hv hpos hneg in
private theorem ord_mutationComplementPullback_character (hΦ : Φ.IsRegular) (ρ : Φ.Ray)
    (a : N →+ ℤ) :
    letI : Nonempty Φ.cones := ⟨⟨_, hpos⟩⟩
    letI : Nonempty (Ψ).cones := ⟨Φ.mutationFanConeEquiv b hv hpos hneg ⟨_, hpos⟩⟩
    Φ.algebraicRealization.ord (pb ((Ψ).character (ofAdd a))) (Φ.rayBoundaryPoint hΦ ρ).val =
      a (Φ.mutationFanRayEquiv b hv hpos hneg ρ).primitiveGenerator := by
  let : Nonempty Φ.cones := ⟨⟨_, hpos⟩⟩
  let : Nonempty (Ψ).cones := ⟨Φ.mutationFanConeEquiv b hv hpos hneg ⟨_, hpos⟩⟩
  have hm : mutationChartCharacter b (v := v) false ≠ 0 := by simpa only
    [ne_eq, mutationChartCharacter_eq_zero_iff] using hv
  let m := (b.detDualEquiv v).toAddMonoidHom
  have hm' : m ≠ 0 := by simpa only [m, mutationChartCharacter_false] using hm
  obtain ⟨hne, ho⟩ := Φ.ord_rayBoundaryChartPoint_one_add_mul_character ℂ hΦ ρ c hm'
  let E := Φ.finiteFanSchemeComplexIso.hom
  let : E.IsOver (Spec (.of ℂ)) := ⟨by
    rw [Fan.finiteFanScheme_over, Fan.algebraicRealization_over]
    exact Φ.finiteFanSchemeComplexIso_hom_comp_algebraicRealizationStructureMap⟩
  let z := 1 + algebraMap ℂ Φ.algebraicRealization.functionField (c : ℂ) *
    Φ.character (ofAdd m)
  have he : E.functionFieldMap z = 1 +
      algebraMap ℂ (Φ.finiteFanScheme ℂ).functionField (c : ℂ) *
        Φ.functionFieldCharacter ℂ (ofAdd m) := by
    dsimp only [z, E]
    rw [map_add, map_one, map_mul, functionFieldMap_finiteFanSchemeComplexIso_character,
      (Φ.finiteFanSchemeComplexIso.hom).functionFieldMap_algebraMap ℂ]
  have hne : z ≠ 0 := fun hz ↦ hne (he.symm ▸ (hz ▸ map_zero _))
  have ho : Φ.algebraicRealization.ord z (Φ.rayBoundaryPoint hΦ ρ).val =
      min 0 (m ρ.primitiveGenerator) := by
    rw [← rayBoundaryChartPoint_apply Φ hΦ ρ, ← ord_functionFieldMap E, he]
    exact ho
  rw [mutationComplementPullback_character,
    Scheme.ord_mul ((Group.isUnit (ofAdd a)).map Φ.character).ne_zero (zpow_ne_zero _ hne),
    Scheme.ord_zpow, ord_rayBoundaryPoint_character, ho, mutationFanRayEquiv_primitiveGenerator,
    map_add, map_zsmul]
  have h := b.detDualEquiv_swap v ρ.primitiveGenerator
  simp only [m, LinearMap.toAddMonoidHom_coe, Module.Basis.detDualEquiv_apply] at h ⊢
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
        ⟨(Φ.rayBoundaryPoint hΦ ρ).val,
          Φ.rayBoundaryPoint_mem_mutationComplement b c hv h₀ hΦ ρ⟩ =
      ((Ψ).rayBoundaryPoint ((Φ.isRegular_mutationFan_iff b hv hpos hneg).mpr hΦ)
        (Φ.mutationFanRayEquiv b hv hpos hneg ρ)).val := by
  let j := (e).hom ≫ (U₁).ι
  let x : (U₀).toScheme := ⟨_, Φ.rayBoundaryPoint_mem_mutationComplement b c hv h₀ hΦ ρ⟩
  have hx : (U₀).ι x = (Φ.rayBoundaryPoint hΦ ρ).val := Scheme.Opens.ι_apply _ _
  let hΨ := (Φ.isRegular_mutationFan_iff b hv hpos hneg).mpr hΦ
  let τ := Φ.mutationFanRayEquiv b hv hpos hneg ρ
  let hΦ₀ : Nonempty Φ.cones := ⟨ρ.toCone⟩
  let hΨ₀ : Nonempty (Ψ).cones := ⟨τ.toCone⟩
  have hx' : Order.coheight x = 1 := by
    rw [← coheight_eq_of_isOpenImmersion (U₀).ι, hx]
    exact (Φ.rayBoundaryPoint hΦ ρ).property
  let y := CodimensionOnePoint.mapOfIsOpenImmersion j ⟨x, hx'⟩
  have hy : y.val ∉ Set.range ((Ψ).denseTorusι hΨ₀) := by
    have ht := Φ.mutationComplementIso_preimage_range_denseTorusι b (c : ℂ)
      hv hpos hneg hΦ₀ hΨ₀
    rw [CodimensionOnePoint.coe_mapOfIsOpenImmersion]
    exact fun h ↦ Φ.rayBoundaryPoint_notMem_range_denseTorusι hΦ ρ
      (hx ▸ (Set.ext_iff.mp ht x).mp h)
  obtain ⟨σ, hσ⟩ : y ∈ Set.range ((Ψ).rayBoundaryPoint hΨ) :=
    ((Ψ).range_rayBoundaryPoint hΨ hΨ₀).symm ▸ hy
  have hpoint : ((Ψ).rayBoundaryPoint hΨ σ).val = j x :=
    (congrArg Subtype.val hσ).trans (CodimensionOnePoint.coe_mapOfIsOpenImmersion j _)
  have hgen (a : N →+ ℤ) : a σ.primitiveGenerator = a τ.primitiveGenerator := by
    let := hΨ₀
    rw [← (Ψ).ord_rayBoundaryPoint_character hΨ σ, hpoint,
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
    ∀ f : (Ψ).algebraicRealization.functionField,
      Φ.algebraicRealization.ord (pb f) (Φ.rayBoundaryPoint hΦ ρ).val =
        (Ψ).algebraicRealization.ord f
          ((Ψ).rayBoundaryPoint ((Φ.isRegular_mutationFan_iff b hv hpos hneg).mpr hΦ)
            (Φ.mutationFanRayEquiv b hv hpos hneg ρ)).val := by
  intro f
  let x : (U₀).toScheme := ⟨_, Φ.rayBoundaryPoint_mem_mutationComplement b c hv h₀ hΦ ρ⟩
  have hx : (U₀).ι x = (Φ.rayBoundaryPoint hΦ ρ).val := Scheme.Opens.ι_apply _ _
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

/-- Pulling back the mutated center characters gives the tropical update of the
source boundary valuation row. The target center parameters can be any nonzero
scalars, since constants have order zero along every boundary ray. -/
theorem ord_mutationComplementPullback_centerCharacter (B : SkewExchangeMatrix ι)
    (hB : ∀ j, B.matrix j k = d v(j) v(k)) (hΦ : Φ.IsRegular) (ρ : Φ.Ray)
    (cₖ : ℂˣ) (a : ι → ℂˣ) :
    letI : Nonempty Φ.cones := ⟨(s k).toCone⟩
    letI : Nonempty (Φ').cones := ⟨(ρ'(ρ)).toCone⟩
    ∀ j, Φ.algebraicRealization.ord
      (Φ.mutationComplementPullback b (cₖ : ℂ) hvₖ h₊ hOpp
        (algebraMap ℂ (Φ').algebraicRealization.functionField (a j : ℂ) *
          (Φ').character (ofAdd (d ((s') j).primitiveGenerator).toAddMonoidHom)))
      (Φ.rayBoundaryPoint hΦ ρ).val =
      (Generator.mutate k).tropical B (fun l ↦ d v(l) ρ.primitiveGenerator) j := by
  let : Nonempty Φ.cones := ⟨(s k).toCone⟩
  let : Nonempty (Φ').cones := ⟨(ρ'(ρ)).toCone⟩
  intro j
  rw [ord_mutationComplementPullback_rayBoundaryPoint, ord_rayBoundaryPoint_mul_character,
    tropical_mutate_eq_rayPairing_mutationFanRayEquiv Φ b s k hOpp B hB ρ]
  rfl

end CenterRays

end TauCeti.Toric.Fan

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Basic
public import QPainleve.Geometry.Toric.Fan.Mutation.Blowup
public import QPainleve.Geometry.Toric.Fan.Point
import QPainleve.Geometry.Toric.Fan.Adjacency
import QPainleve.Geometry.Toric.Fan.Boundary.Intersection
import QPainleve.Geometry.Toric.Fan.Mutation.Valuation
import TauCeti.AlgebraicGeometry.IdealSheaf.Extension

/-!
# The oriented toric boundary under mutation

The integral shear preserves the determinant of two rays in the same cone.
The boundary nodes lie away from the pivot fiber, where the mutation isomorphism
carries the intersection of two adjacent ray divisors to the intersection of their
images. These two facts determine the order of the incident branches.

The mutation is the elementary transformation of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*](https://arxiv.org/html/1309.2573v2#S3.SS1).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone
open AddMonoidAlgebra Multiplicative
open Scheme.IdealSheafData QPainleve QPainleve.BlowupTower

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (b : Basis (Fin 2) ℤ N) {v : N}
  (hv : v ≠ 0) (hp : hull ℝ {i v} ∈ Φ.cones) (hn : hull ℝ {i (-v)} ∈ Φ.cones)

local notation "Ψ" => Φ.mutationFan b hv hp hn
local notation "r" => Φ.mutationFanRayEquiv b hv hp hn
local notation "m" => (LinearMap.toAddMonoidHom (b.detDualEquiv v))
local notation "h₀" => Φ.detCharacter_nonneg_or_nonpos b hv hp hn
local notation "h₁" => Φ.mutationDetCharacter_nonneg_or_nonpos b hv hp hn

/-- Mutation preserves the determinant of the primitive generators of two rays in
a common cone. In particular it preserves the positive order of adjacent rays. -/
theorem detDualEquiv_mutationFanRayEquiv_of_le {σ : Φ.cones} {ρ τ : Φ.Ray}
    (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ) :
    b.detDualEquiv (r ρ).primitiveGenerator (r τ).primitiveGenerator =
      b.detDualEquiv ρ.primitiveGenerator τ.primitiveGenerator := by
  let u := ρ.primitiveGenerator
  let w := τ.primitiveGenerator
  have eq (a : N) : b.det ![a, v] = -b.detDualEquiv v a := by
    rw [← b.detDualEquiv_apply, b.detDualEquiv_swap]
  simp only [mutationFanRayEquiv_primitiveGenerator, eq]
  rcases h₀ σ with h | h
  · have hu := h _ (hρ ρ.primitiveGenerator_mem)
    have hw := h _ (hτ τ.primitiveGenerator_mem)
    rw [IsIntegralLattice.realCharacter_apply] at hu hw
    have hu' : 0 ≤ b.detDualEquiv v ρ.primitiveGenerator := by exact_mod_cast hu
    have hw' : 0 ≤ b.detDualEquiv v τ.primitiveGenerator := by exact_mod_cast hw
    simp only [max_eq_right (neg_nonpos.mpr hu'), max_eq_right (neg_nonpos.mpr hw'),
      zero_smul, add_zero]
  · have hu := h _ (hρ ρ.primitiveGenerator_mem)
    have hw := h _ (hτ τ.primitiveGenerator_mem)
    rw [IsIntegralLattice.realCharacter_apply] at hu hw
    rw [max_eq_left (neg_nonneg.mpr (by exact_mod_cast hu)),
      max_eq_left (neg_nonneg.mpr (by exact_mod_cast hw))]
    let T := LinearEquiv.transvection (f := -b.detDualEquiv v) (v := v)
      (by simp only [LinearMap.neg_apply, Basis.detDualEquiv_self, neg_zero])
    have hT (x : N) : T x = x + (-b.detDualEquiv v x) • v := (rfl)
    have hcomp : T.toLinearMap ∘ ![u, w] = ![T u, T w] := by
      ext j
      fin_cases j <;> rfl
    have hdet : LinearMap.det T.toLinearMap = 1 := by
      rw [← LinearEquiv.coe_det]
      simp [T]
    simpa only [Basis.detDualEquiv_apply, hcomp, hT, hdet, one_mul, u, w]
      using b.det_comp T.toLinearMap ![u, w]

section Complement

variable (c : ℂˣ)

local notation "U₀" => Φ.mutationComplement b h₀ (c : ℂ)
local notation "U₁" => mutationComplement (Ψ) b h₁ (c : ℂ)
local notation "e" => Φ.mutationComplementIso b (c : ℂ) hv hp hn

private theorem distinguishedPointHom_mem_mutationComplement_of_character
    (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0)
    (σ : Φ.cones) (x : Spec (.of ℂ))
    (hσ : ∃ y ∈ σ.val, Φ.lattice.realCharacter m y ≠ 0) :
    Φ.distinguishedPointHom σ x ∈ Φ.mutationComplement b h (c : ℂ) := by
  classical
  obtain ⟨side, hs⟩ := Φ.exists_mutationChartCharacter_mem_dualSemigroup b σ (h σ)
  let q : dualSemigroup Φ.lattice σ.val := ⟨mutationChartCharacter b side, hs⟩
  let d := distinguishedPoint Φ.lattice (⊤ : σ.val.Face)
  let A := toMultiplicativeAlgEquiv ℂ ℂ (dualSemigroup Φ.lattice σ.val)
  have hd : d (MonoidAlgebra.single (ofAdd q) 1) = 0 := by
    obtain ⟨y, hy, hny⟩ := hσ
    rw [distinguishedPoint_apply_single, ite_eq_right]
    intro hzero
    have hz := hzero y hy
    dsimp only [q] at hz
    cases side <;> simp_all
  have hsingle (a : ℂ) : d (MonoidAlgebra.single (ofAdd q) a) = 0 := by
    calc
      _ = d (a • MonoidAlgebra.single (ofAdd q) 1) := by
        rw [MonoidAlgebra.smul_single', mul_one]
      _ = 0 := by rw [map_smul, hd, smul_zero]
  have hbin : d (A (Φ.mutationChartBinomial side (c : ℂ) q)) ≠ 0 := by
    rw [mutationChartBinomial_eq, map_add, AlgEquiv.commutes, toMultiplicativeAlgEquiv_single,
      map_add, AlgHom.commutes, hsingle, add_zero]
    cases side <;> simp
  rw [distinguishedPointHom_def,
    ← Φ.specMap_toMultiplicativeAlgEquiv_comp_additiveAffineToricChartι σ,
    ← Category.assoc, ← Spec.map_comp, Scheme.Hom.comp_apply]
  apply (Scheme.Hom.mem_preimage _).mp
  rw [Φ.additiveAffineToricChartι_preimage_mutationComplement b σ side hs (c : ℂ) h]
  refine (PrimeSpectrum.mem_basicOpen _ _).mpr fun hx ↦ hbin ?_
  let y : PrimeSpectrum ℂ := x
  have hy : d (A (Φ.mutationChartBinomial side (c : ℂ) q)) ∈ y.asIdeal := hx
  exact Ideal.mem_bot.mp ((Ideal.eq_bot_of_prime y.asIdeal) ▸ hy)

omit hv hp hn in
/-- Every boundary node of a regular rank-two fan lies off the pivot fiber, provided
the pivot is nonzero and its character has constant weak sign on each cone. -/
theorem distinguishedPointHom_mem_mutationComplement (hΦ : Φ.IsRegular) (hv : v ≠ 0)
    (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0)
    {σ : Φ.cones} {ρ τ : Φ.Ray} (hne : ρ ≠ τ) (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ)
    (x : Spec (.of ℂ)) :
    Φ.distinguishedPointHom σ x ∈ Φ.mutationComplement b h (c : ℂ) := by
  apply Φ.distinguishedPointHom_mem_mutationComplement_of_character b c h σ x
  by_contra! hzero
  have hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  obtain ⟨a, ha₀, ha₁⟩ := Φ.exists_basis_of_ray_ne_of_le
    ((isRegular_iff.mp hΦ) _ σ.property) hdim hne hρ hτ
  apply hv
  apply b.detDualEquiv.injective
  rw [map_zero]
  apply a.ext
  intro j
  refine Fin.cases ?_ (fun j ↦ Fin.eq_zero j ▸ ?_) j
  · rw [ha₀, LinearMap.zero_apply]
    simpa only [IsIntegralLattice.realCharacter_apply, LinearMap.toAddMonoidHom_coe,
      Int.cast_eq_zero] using
      hzero _ (hρ ρ.primitiveGenerator_mem)
  · rw [Fin.succ_zero_eq_one, ha₁, LinearMap.zero_apply]
    simpa only [IsIntegralLattice.realCharacter_apply, LinearMap.toAddMonoidHom_coe,
      Int.cast_eq_zero] using
      hzero _ (hτ τ.primitiveGenerator_mem)

/-- The mutation isomorphism on the pivot-fiber complement pulls each image ray divisor
back to its source ray divisor. At a node this identifies the branch on the specified ray. -/
theorem comap_rayBoundaryIdeal_mutationComplementIso (hΦ : Φ.IsRegular) (ρ : Φ.Ray) :
    ((Ψ).rayBoundaryIdeal ((Φ.isRegular_mutationFan_iff b hv hp hn).mpr hΦ) (r ρ)).comap
        ((e).hom ≫ (U₁).ι) =
      (Φ.rayBoundaryIdeal hΦ ρ).comap (U₀).ι := by
  let x : (U₀).toScheme := ⟨(Φ.rayBoundaryPoint hΦ ρ).val,
    Φ.rayBoundaryPoint_mem_mutationComplement b c hv h₀ hΦ ρ⟩
  have hx : (U₀).ι x = (Φ.rayBoundaryPoint hΦ ρ).val := Scheme.Opens.ι_apply _ _
  have hy : ((e).hom ≫ (U₁).ι) x =
      ((Ψ).rayBoundaryPoint ((Φ.isRegular_mutationFan_iff b hv hp hn).mpr hΦ) (r ρ)).val :=
    Φ.mutationComplementIso_hom_rayBoundaryPoint b c hv hp hn hΦ ρ
  rw [rayBoundaryIdeal_def, rayBoundaryIdeal_def, ← hx, ← hy,
    comap_vanishingIdeal_closure_singleton_apply _ x,
    comap_vanishingIdeal_closure_singleton_apply _ x]

include hv hp hn in
/-- On the complement of the pivot fiber, mutation sends the actual node where
two ray divisors meet to the node where the sheared ray divisors meet. -/
@[reassoc]
theorem mutationComplementIso_comp_distinguishedPointHom (hΦ : Φ.IsRegular)
    {σ : Φ.cones} {ρ τ : Φ.Ray} (hne : ρ ≠ τ) (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ)
    {p : Spec (.of ℂ) ⟶ (U₀).toScheme} (h : p ≫ (U₀).ι = Φ.distinguishedPointHom σ) :
    p ≫ (e).hom ≫ (U₁).ι = (Ψ).distinguishedPointHom (Φ.mutationFanConeEquiv b hv hp hn σ) := by
  let σ' := Φ.mutationFanConeEquiv b hv hp hn σ
  let hΨ := (Φ.isRegular_mutationFan_iff b hv hp hn).mpr hΦ
  have hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  have hρ' : (r ρ).toCone ≤ σ' := by
    rw [mutationFanRayEquiv_toCone]
    exact (Φ.mutationFanConeEquiv b hv hp hn).monotone hρ
  have hτ' : (r τ).toCone ≤ σ' := by
    rw [mutationFanRayEquiv_toCone]
    exact (Φ.mutationFanConeEquiv b hv hp hn).monotone hτ
  have hker : ((Ψ).distinguishedPointHom σ').ker.comap ((e).hom ≫ (U₁).ι) =
      (Φ.distinguishedPointHom σ).ker.comap (U₀).ι := by
    rw [distinguishedPointHom_def, distinguishedPointHom_def,
      ← (Ψ).sup_rayBoundaryIdeal_eq_ker_distinguishedPoint hΨ hdim
        ((r).injective.ne hne) σ' hρ' hτ',
      ← Φ.sup_rayBoundaryIdeal_eq_ker_distinguishedPoint hΦ hdim hne σ hρ hτ]
    rw [comap_sup, comap_sup, Φ.comap_rayBoundaryIdeal_mutationComplementIso b hv hp hn c hΦ ρ,
      Φ.comap_rayBoundaryIdeal_mutationComplementIso b hv hp hn c hΦ τ]
  let f := (e).hom ≫ (U₁).ι
  let q := (Ψ).distinguishedPointHom σ'
  have hle : q.ker ≤ (p ≫ f).ker := by
    rw [Scheme.Hom.ker_comp, le_map_iff_comap_le, hker, ← h, Scheme.Hom.ker_comp,
      comap_map_of_isOpenImmersion]
  have hq := (Ψ).isClosedImmersion_distinguishedPointHom σ'
  let l := IsClosedImmersion.lift q (p ≫ f) hle
  have hl : l ≫ q = p ≫ f := IsClosedImmersion.lift_fac _ _ _
  have hbase : (p ≫ f) ≫ (Ψ).algebraicRealizationStructureMap = 𝟙 _ := by
    simp only [f, Category.assoc]
    rw [mutationComplementIso_hom_comp_toBase, ← Category.assoc, h,
      distinguishedPointHom_comp_algebraicRealizationStructureMap]
  have hl' : l = 𝟙 _ := by
    simpa only [Category.assoc, q, distinguishedPointHom_comp_algebraicRealizationStructureMap,
      Category.comp_id] using (congrArg (· ≫ (Ψ).algebraicRealizationStructureMap) hl).trans hbase
  exact hl.symm.trans (by rw [hl', Category.id_comp])

end Complement

section PivotBlowup

variable {Φ}

variable (pivot : Φ.Ray)
  (hOpp : hull ℝ {i (-pivot.primitiveGenerator)} ∈ Φ.cones) (c : ℂˣ)

local notation "Sheared" => Φ.mutationFan b pivot.primitiveGenerator_ne_zero
  pivot.hull_primitiveGenerator_mem hOpp
local notation "coneEquiv" => Φ.mutationFanConeEquiv b pivot.primitiveGenerator_ne_zero
  pivot.hull_primitiveGenerator_mem hOpp
local notation "U" => Φ.mutationComplement b (Φ.detCharacter_nonneg_or_nonpos b
  pivot.primitiveGenerator_ne_zero pivot.hull_primitiveGenerator_mem hOpp) (c : ℂ)
local notation "I" => Ray.mutationSourceCenterIdeal b pivot c
local notation "I'" => Ray.mutationTargetCenterIdeal b pivot hOpp c

/-- The global pivot isomorphism takes the unique lift of a toric boundary node
to the lift of the node of the sheared cone. -/
theorem Ray.exists_lift_distinguishedPointHom_mutationBlowupIso (hΦ : Φ.IsRegular)
    {σ : Φ.cones} {ρ τ : Φ.Ray} (hne : ρ ≠ τ) (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ) :
    ∃ p : Spec (.of ℂ) ⟶ (I).blowup,
      (∀ q : Spec (.of ℂ) ⟶ (I).blowup, q ≫ (I).blowupToBase = Φ.distinguishedPointHom σ ↔ q = p) ∧
        p ≫ (pivot.mutationBlowupIso b hOpp c).hom ≫ (I').blowupToBase =
          (Sheared).distinguishedPointHom ((coneEquiv) σ) := by
  have hsubset : Set.range (Φ.distinguishedPointHom σ) ⊆ Set.range (U).ι := by
    rw [(U).range_ι]
    rintro _ ⟨x, rfl⟩
    exact Φ.distinguishedPointHom_mem_mutationComplement b c hΦ pivot.primitiveGenerator_ne_zero
      _ hne hρ hτ x
  let p := IsOpenImmersion.lift (U).ι (Φ.distinguishedPointHom σ) hsubset
  have hp₀ : p ≫ (U).ι = Φ.distinguishedPointHom σ := IsOpenImmersion.lift_fac _ _ _
  have hI := pivot.mutationSourceCenterIdeal_comap_complement b hOpp c
  let j := (I).blowupLift (U).ι (hI.symm ▸ isEffectiveCartier_top _)
  have hj : j ≫ (I).blowupToBase = (U).ι := blowupLift_blowupToBase _ _ _
  have hproj : (p ≫ j) ≫ (I).blowupToBase = Φ.distinguishedPointHom σ := by
    rw [Category.assoc, hj, hp₀]
  refine ⟨p ≫ j, ?_, ?_⟩
  · intro q
    refine ⟨fun hq ↦ ?_, fun hq ↦ hq.symm ▸ hproj⟩
    apply (I).blowup_hom_ext (hq.trans hproj.symm)
    rw [hq, ← hp₀, comap_comp, hI, comap_top]
    exact isEffectiveCartier_top _
  · rw [Category.assoc, Ray.mutationComplementBlowupι_comp_mutationBlowupIso_hom_assoc,
      blowupLift_blowupToBase]
    exact Φ.mutationComplementIso_comp_distinguishedPointHom b _ _ hOpp c hΦ hne hρ hτ hp₀

/-- The comparison of toric nodes persists after lifting the mutation isomorphism
through further blowups. The point on the source tower is any lift of the source node. -/
theorem Ray.mutationBlowupIso_lift_comp_distinguishedPointHom (hΦ : Φ.IsRegular)
    {σ : Φ.cones} {ρ τ : Φ.Ray} (hne : ρ ≠ τ) (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ)
    {X Y : Scheme} {n : ℕ} {T : BlowupTower (I).blowup n X}
    {T' : BlowupTower (I').blowup n Y} {g : X ≅ Y}
    (hg : IsLift (pivot.mutationBlowupIso b hOpp c) T T' g)
    {p : Spec (.of ℂ) ⟶ X}
    (hp : p ≫ T.toBase ≫ (I).blowupToBase = Φ.distinguishedPointHom σ) :
    p ≫ g.hom ≫ T'.toBase ≫ (I').blowupToBase =
      (Sheared).distinguishedPointHom ((coneEquiv) σ) := by
  obtain ⟨q, hq, himage⟩ :=
    pivot.exists_lift_distinguishedPointHom_mutationBlowupIso b hOpp c hΦ hne hρ hτ
  have heq : p ≫ T.toBase = q := (hq _).mp (by simpa only [Category.assoc] using hp)
  rw [hg.hom_toBase_assoc, ← Category.assoc p, heq, himage]

end PivotBlowup

end TauCeti.Toric.Fan

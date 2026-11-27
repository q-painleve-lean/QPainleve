/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Basic
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Isomorphism
public import QPainleve.Geometry.Toric.Fan.Boundary.Normalization
public import QPainleve.Geometry.Toric.Fan.Mutation.Boundary
public import QPainleve.Geometry.Toric.BaseChange.Point
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
open Scheme.IdealSheafData QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {K : Type} [Field K] {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (b : Basis (Fin 2) ℤ N) {v : N}
  (hv : v ≠ 0) (hp : hull ℝ {i v} ∈ Φ.cones) (hn : hull ℝ {i (-v)} ∈ Φ.cones)

local notation "Ψ" => Φ.mutationFan b hv hp hn
local notation "r" => Φ.mutationFanRayEquiv b hv hp hn
local notation "m" => (LinearMap.toAddMonoidHom (b.detDualEquiv v))
local notation "h₀" => Φ.detCharacter_nonneg_or_nonpos b hv hp hn
local notation "h₁" => Φ.mutationDetCharacter_nonneg_or_nonpos b hv hp hn

section Complement

variable (c : Kˣ)

local notation "U₀" => Φ.mutationComplement b h₀ (c : K)
local notation "U₁" => mutationComplement (Ψ) b h₁ (c : K)
local notation "e" => Φ.mutationComplementIso b (c : K) hv hp hn

private theorem distinguishedPointHom_mem_mutationComplement_of_character
    (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0)
    (σ : Φ.cones) (x : Spec (.of K))
    (hσ : ∃ y ∈ σ.val, Φ.lattice.realCharacter m y ≠ 0) :
    Φ.distinguishedSection (R := K) σ x ∈ Φ.mutationComplement b h (c : K) := by
  classical
  obtain ⟨side, hs⟩ := Φ.exists_mutationChartCharacter_mem_dualSemigroup b σ (h σ)
  let q : dualSemigroup Φ.lattice σ.val := ⟨mutationChartCharacter b side, hs⟩
  let d := facePointAlgebraHom Φ.lattice (⊤ : σ.val.Face) K
  have hsingle (a : K) : d (single q a) = 0 := by
    obtain ⟨y, hy, hny⟩ := hσ
    dsimp only [d]
    rw [facePointAlgebraHom_single, ite_eq_right]
    intro hzero
    have hz := hzero y hy
    dsimp only [q] at hz
    cases side <;> simp_all
  have hbin : d (Φ.mutationChartBinomial side (c : K) q) ≠ 0 := by
    rw [mutationChartBinomial_eq, map_add, AlgHom.commutes, hsingle, add_zero]
    cases side <;> simp
  rw [Φ.distinguishedSection_def (R := K), Scheme.Hom.comp_apply]
  apply (Scheme.Hom.mem_preimage _).mp
  rw [Φ.affineChartι_preimage_mutationComplement b σ side hs (c : K) h]
  refine (PrimeSpectrum.mem_basicOpen _ _).mpr fun hx ↦ hbin ?_
  let y : PrimeSpectrum K := x
  have hy : d (Φ.mutationChartBinomial side (c : K) q) ∈ y.asIdeal := hx
  exact Ideal.mem_bot.mp ((Ideal.eq_bot_of_prime y.asIdeal) ▸ hy)

omit hv hp hn in
/-- Every boundary node of a regular rank-two fan lies off the pivot fiber, provided
the pivot is nonzero and its character has constant weak sign on each cone. -/
theorem distinguishedPointHom_mem_mutationComplement (hΦ : Φ.IsRegular) (hv : v ≠ 0)
    (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0)
    {σ : Φ.cones} {ρ τ : Φ.Ray} (hne : ρ ≠ τ) (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ)
    (x : Spec (.of K)) :
    Φ.distinguishedSection (R := K) σ x ∈ Φ.mutationComplement b h (c : K) := by
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
    ((Ψ).rayDivisorIdeal K ((Φ.isRegular_mutationFan_iff b hv hp hn).mpr hΦ) (r ρ)).comap
        ((e).hom ≫ (U₁).ι) =
      (Φ.rayDivisorIdeal K hΦ ρ).comap (U₀).ι := by
  let x : (U₀).toScheme := ⟨(Φ.rayBoundaryChartPoint (R := K) hΦ ρ).val,
    Φ.rayBoundaryPoint_mem_mutationComplement b c hv h₀ hΦ ρ⟩
  have hx : (U₀).ι x = (Φ.rayBoundaryChartPoint (R := K) hΦ ρ).val := Scheme.Opens.ι_apply _ _
  have hy : ((e).hom ≫ (U₁).ι) x =
      ((Ψ).rayBoundaryChartPoint (R := K)
        ((Φ.isRegular_mutationFan_iff b hv hp hn).mpr hΦ) (r ρ)).val :=
    Φ.mutationComplementIso_hom_rayBoundaryPoint b c hv hp hn hΦ ρ
  rw [rayDivisorIdeal_def K, rayDivisorIdeal_def K, ← hx, ← hy,
    comap_vanishingIdeal_closure_singleton_apply _ x,
    comap_vanishingIdeal_closure_singleton_apply _ x]

include hv hp hn in
/-- On the complement of the pivot fiber, mutation sends the actual node where
two ray divisors meet to the node where the sheared ray divisors meet. -/
@[reassoc]
theorem mutationComplementIso_comp_distinguishedPointHom (hΦ : Φ.IsRegular)
    {σ : Φ.cones} {ρ τ : Φ.Ray} (hne : ρ ≠ τ) (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ)
    {p : Spec (.of K) ⟶ (U₀).toScheme} (h : p ≫ (U₀).ι = Φ.distinguishedSection (R := K) σ) :
    p ≫ (e).hom ≫ (U₁).ι =
      (Ψ).distinguishedSection (R := K) (Φ.mutationFanConeEquiv b hv hp hn σ) := by
  let σ' := Φ.mutationFanConeEquiv b hv hp hn σ
  let hΨ := (Φ.isRegular_mutationFan_iff b hv hp hn).mpr hΦ
  have hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  have hρ' : (r ρ).toCone ≤ σ' := by
    rw [mutationFanRayEquiv_toCone]
    exact (Φ.mutationFanConeEquiv b hv hp hn).monotone hρ
  have hτ' : (r τ).toCone ≤ σ' := by
    rw [mutationFanRayEquiv_toCone]
    exact (Φ.mutationFanConeEquiv b hv hp hn).monotone hτ
  have hker : ((Ψ).distinguishedSection (R := K) σ').ker.comap ((e).hom ≫ (U₁).ι) =
      (Φ.distinguishedSection (R := K) σ).ker.comap (U₀).ι := by
    rw [← (Ψ).sup_rayBoundaryIdeal_eq_ker_distinguishedPoint K hΨ hdim
        ((r).injective.ne hne) σ' hρ' hτ',
      ← Φ.sup_rayBoundaryIdeal_eq_ker_distinguishedPoint K hΦ hdim hne σ hρ hτ]
    rw [comap_sup, comap_sup, Φ.comap_rayBoundaryIdeal_mutationComplementIso b hv hp hn c hΦ ρ,
      Φ.comap_rayBoundaryIdeal_mutationComplementIso b hv hp hn c hΦ τ]
  let f := (e).hom ≫ (U₁).ι
  let q := (Ψ).distinguishedSection (R := K) σ'
  have hle : q.ker ≤ (p ≫ f).ker := by
    rw [Scheme.Hom.ker_comp, le_map_iff_comap_le, hker, ← h, Scheme.Hom.ker_comp,
      comap_map_of_isOpenImmersion]
  have hq := (Ψ).isClosedImmersion_distinguishedSection (R := K) σ'
  let l := IsClosedImmersion.lift q (p ≫ f) hle
  have hl : l ≫ q = p ≫ f := IsClosedImmersion.lift_fac _ _ _
  have hbase : (p ≫ f) ≫ (Ψ).finiteFanSchemeToSpec K = 𝟙 _ := by
    simp only [f, Category.assoc]
    rw [mutationComplementIso_hom_comp_toBase, ← Category.assoc, h,
      distinguishedSection_comp_finiteFanSchemeToSpec]
  have hl' : l = 𝟙 _ := by
    simpa only [Category.assoc, q, distinguishedSection_comp_finiteFanSchemeToSpec,
      Category.comp_id] using (congrArg (· ≫ (Ψ).finiteFanSchemeToSpec K) hl).trans hbase
  exact hl.symm.trans (by rw [hl', Category.id_comp])

/-- The pivot-fiber complement contains the distinguished point of every two-ray
cone. Mutation takes it to the distinguished point of the sheared two-ray cone. -/
theorem mutationComplementIso_apply_distinguishedPointHom (hΦ : Φ.IsRegular)
    {σ : Φ.cones} (hσ : Nat.card (ToricRay σ.val) = 2) (x : Spec (.of K)) :
    let σ' := Φ.mutationFanConeEquiv b hv hp hn σ
    ∃ hx : Φ.distinguishedSection (R := K) σ x ∈ U₀,
      Nat.card (ToricRay σ'.val) = 2 ∧
        (U₁).ι ((e).hom ⟨Φ.distinguishedSection (R := K) σ x, hx⟩) =
          (Ψ).distinguishedSection (R := K) σ' x := by
  intro σ'
  obtain ⟨u, w, hu, hw, hdet⟩ := Φ.exists_ray_pair_le_det_eq_one b
    ((Fan.isRegular_iff.mp hΦ) _ σ.property) hσ
  have hne : u ≠ w := by
    rintro rfl
    exact zero_ne_one ((b.detDualEquiv_self u.primitiveGenerator).symm.trans hdet)
  have hmem (z : Spec (.of K)) : Φ.distinguishedSection (R := K) σ z ∈ U₀ :=
    Φ.distinguishedPointHom_mem_mutationComplement b c hΦ hv h₀ hne hu hw z
  have hsubset : Set.range (Φ.distinguishedSection (R := K) σ) ⊆ Set.range (U₀).ι := by
    rw [(U₀).range_ι]
    rintro _ ⟨z, rfl⟩
    exact hmem z
  let f := IsOpenImmersion.lift (U₀).ι (Φ.distinguishedSection (R := K) σ) hsubset
  have hf : f ≫ (U₀).ι = Φ.distinguishedSection (R := K) σ := IsOpenImmersion.lift_fac _ _ _
  have himage := Φ.mutationComplementIso_comp_distinguishedPointHom b hv hp hn c hΦ hne hu hw hf
  have hx : (⟨Φ.distinguishedSection (R := K) σ x, hmem x⟩ : (U₀).toScheme) = f x :=
    Subtype.ext (congrArg (fun g : Spec (.of K) ⟶ (Φ.finiteFanScheme K) ↦ g x) hf).symm
  have hle {a : Φ.Ray} (ha : a.toCone ≤ σ) : (r a).toCone ≤ σ' := by
    rw [mutationFanRayEquiv_toCone, OrderIso.le_iff_le]
    exact ha
  have hΨ := (Φ.isRegular_mutationFan_iff b hv hp hn).mpr hΦ
  have hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  refine ⟨hmem x, (Ψ).card_toricRay_eq_two_of_ray_ne_of_le hΨ hdim ((r).injective.ne hne)
    (hle hu) (hle hw), ?_⟩
  rw [hx, ← Scheme.Hom.comp_apply (e).hom _, ← Scheme.Hom.comp_apply f _, himage]

end Complement

section PivotBlowup

variable {Φ}

variable (pivot : Φ.Ray)
  (hOpp : hull ℝ {i (-pivot.primitiveGenerator)} ∈ Φ.cones) (c : Kˣ)

local notation "Sheared" => Φ.mutationFan b pivot.primitiveGenerator_ne_zero
  pivot.hull_primitiveGenerator_mem hOpp
local notation "coneEquiv" => Φ.mutationFanConeEquiv b pivot.primitiveGenerator_ne_zero
  pivot.hull_primitiveGenerator_mem hOpp
local notation "U" => Φ.mutationComplement b (Φ.detCharacter_nonneg_or_nonpos b
  pivot.primitiveGenerator_ne_zero pivot.hull_primitiveGenerator_mem hOpp) (c : K)
local notation "I" => Ray.mutationSourceCenterIdeal b pivot c
local notation "I'" => Ray.mutationTargetCenterIdeal b pivot hOpp c

/-- The global pivot isomorphism takes the unique lift of a toric boundary node
to the lift of the node of the sheared cone. -/
theorem Ray.exists_lift_distinguishedPointHom_mutationBlowupIso (hΦ : Φ.IsRegular)
    {σ : Φ.cones} {ρ τ : Φ.Ray} (hne : ρ ≠ τ) (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ) :
    ∃ p : Spec (.of K) ⟶ (I).blowup,
      (∀ q : Spec (.of K) ⟶ (I).blowup,
        q ≫ (I).blowupToBase = Φ.distinguishedSection (R := K) σ ↔ q = p) ∧
        p ≫ (pivot.mutationBlowupIso b hOpp c).hom ≫ (I').blowupToBase =
          (Sheared).distinguishedSection (R := K) ((coneEquiv) σ) := by
  have hsubset : Set.range (Φ.distinguishedSection (R := K) σ) ⊆ Set.range (U).ι := by
    rw [(U).range_ι]
    rintro _ ⟨x, rfl⟩
    exact Φ.distinguishedPointHom_mem_mutationComplement b c hΦ pivot.primitiveGenerator_ne_zero
      _ hne hρ hτ x
  let p := IsOpenImmersion.lift (U).ι (Φ.distinguishedSection (R := K) σ) hsubset
  have hp₀ : p ≫ (U).ι = Φ.distinguishedSection (R := K) σ := IsOpenImmersion.lift_fac _ _ _
  have hI := pivot.mutationSourceCenterIdeal_comap_complement b hOpp c
  let j := (I).blowupLift (U).ι (hI.symm ▸ isEffectiveCartier_top _)
  have hj : j ≫ (I).blowupToBase = (U).ι := blowupLift_blowupToBase _ _ _
  have hproj : (p ≫ j) ≫ (I).blowupToBase = Φ.distinguishedSection (R := K) σ := by
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
    {p : Spec (.of K) ⟶ X}
    (hp : p ≫ T.toBase ≫ (I).blowupToBase = Φ.distinguishedSection (R := K) σ) :
    p ≫ g.hom ≫ T'.toBase ≫ (I').blowupToBase =
      (Sheared).distinguishedSection (R := K) ((coneEquiv) σ) := by
  obtain ⟨q, hq, himage⟩ :=
    pivot.exists_lift_distinguishedPointHom_mutationBlowupIso b hOpp c hΦ hne hρ hτ
  have heq : p ≫ T.toBase = q := (hq _).mp (by simpa only [Category.assoc] using hp)
  rw [hg.hom_toBase_assoc, ← Category.assoc p, heq, himage]

section Branches

variable (hΦ : Φ.IsRegular)
local notation "hΦ₀" => Nonempty.intro (Ray.toCone Φ pivot)
local notation "hΨ₀" => Nonempty.intro ((coneEquiv)
  (Subtype.mk _ (Ray.hull_primitiveGenerator_mem pivot)))
local notation "D₀" => Φ.toricBoundaryIdeal K hΦ₀
local notation "D₁" => toricBoundaryIdeal K (Sheared) hΨ₀
local notation "C₀" => Scheme.IdealSheafData.subscheme (D₀)
local notation "C₁" => Scheme.IdealSheafData.subscheme (D₁)
local notation "E" => Ray.mutationBoundaryIso b pivot hOpp c hΦ
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b
  (Ray.primitiveGenerator_ne_zero pivot) (Ray.hull_primitiveGenerator_mem pivot) hOpp) hΦ
local notation "s" => Φ.mutationFanRayEquiv b (Ray.primitiveGenerator_ne_zero pivot)
  (Ray.hull_primitiveGenerator_mem pivot) hOpp

include hΦ in
/-- The isomorphism of the strict boundaries maps each distinguished node to the
distinguished node of the sheared cone. -/
@[reassoc]
theorem Ray.mutationBoundaryIso_comp_distinguishedPointHom
    {σ : Φ.cones} {ρ τ : Φ.Ray} (hne : ρ ≠ τ) (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ)
    {p : Spec (.of K) ⟶ C₀} (hp : p ≫ (D₀).subschemeι = Φ.distinguishedSection (R := K) σ) :
    p ≫ (E).hom ≫ (D₁).subschemeι = (Sheared).distinguishedSection (R := K) ((coneEquiv) σ) := by
  obtain ⟨q, hq, hq'⟩ :=
    pivot.exists_lift_distinguishedPointHom_mutationBlowupIso b hOpp c hΦ hne hρ hτ
  have hl : p ≫ pivot.mutationSourceBoundaryι b c = q :=
    (hq _).mp (by simpa only [Category.assoc, Ray.mutationSourceBoundaryι_blowupToBase] using hp)
  rw [← Ray.mutationTargetBoundaryι_blowupToBase b pivot hOpp c,
    Ray.mutationBoundaryIso_hom_comp_boundaryι_assoc, ← Category.assoc p, hl]
  exact hq'

variable [hN₀ : Nonempty Φ.cones]
  [hN₁ : Nonempty (Φ.mutationFan b pivot.primitiveGenerator_ne_zero
    pivot.hull_primitiveGenerator_mem hOpp).cones]

local notation "ν[" C "]" => Scheme.IdealSheafData.blowupToBase (Scheme.singularLocus K C)
local notation "j[" C "]" => Scheme.branchSchemeToBlowup K C

private theorem image_rayComponent_mutationBoundaryIso (u : Φ.Ray) :
    (E).hom '' Set.range (u.boundaryComponentι K hΦ) =
      Set.range ((s u).boundaryComponentι K (hΨ)) := by
  let f := u.boundaryComponentι K hΦ
  let g := (s u).boundaryComponentι K (hΨ)
  have hk : g.ker.comap (E).hom = f.ker :=
    pivot.comap_ker_boundaryComponentι_mutationBoundaryIso b hOpp c hΦ u
  have heq : (E).hom ⁻¹' Set.range g = Set.range f := by
    simpa only [support_comap, TopologicalSpace.Closeds.coe_preimage, Scheme.Hom.support_ker,
      f.isClosedEmbedding.isClosed_range.closure_eq, g.isClosedEmbedding.isClosed_range.closure_eq]
      using congrArg (fun K : (C₀).IdealSheafData ↦ (K.support : Set C₀)) hk
  have he : Function.Surjective (E).hom := by
    simpa only [Scheme.coe_homeoOfIso] using (Scheme.homeoOfIso E).surjective
  exact (congrArg (fun Z ↦ (E).hom '' Z) heq.symm).trans (Set.image_preimage_eq _ he)

variable [PrestableFamily ((Φ.toricBoundaryIdeal K hN₀).subscheme ↘ Spec (.of K))]
  [PrestableFamily (((Φ.mutationFan b pivot.primitiveGenerator_ne_zero
    pivot.hull_primitiveGenerator_mem hOpp).toricBoundaryIdeal K hN₁).subscheme ↘ Spec (.of K))]

/-- On the normalization, mutation maps the entire component of an original ray
onto the component of the sheared ray. -/
theorem Ray.image_boundaryNormalizationComponent_mutationBoundaryIso (u : Φ.Ray) :
    ((E).singularLocusBlowupIso (R := K)).hom ''
      (Φ.boundaryNormalizationComponentEquiv K hΦ u : Set (Scheme.singularLocus K C₀).blowup) =
      ((Sheared).boundaryNormalizationComponentEquiv K (hΨ) (s u) :
        Set (Scheme.singularLocus K C₁).blowup) := by
  let H := Scheme.homeoOfIso ((E).singularLocusBlowupIso (R := K))
  let A := Φ.boundaryNormalizationComponentEquiv K hΦ u
  let B := (Sheared).boundaryNormalizationComponentEquiv K (hΨ) (s u)
  have hW := image_mem_irreducibleComponents_of_isPreirreducible_fiber H H.continuous H.isOpenMap
    (fun _ ↦ (Set.subsingleton_singleton.preimage H.injective).isPreirreducible)
    H.surjective A.property
  let W := (⟨H '' (A : Set _), hW⟩ : irreducibleComponents _)
  have hcomp (x : (Scheme.singularLocus K C₀).blowup) :
      ν[C₁] (H x) = (E).hom (ν[C₀] x) := by
    simpa only [Scheme.coe_homeoOfIso, Scheme.Hom.comp_apply, H] using
      congrArg (fun f : _ ⟶ C₁ ↦ f x) ((E).singularLocusBlowupIso_hom_blowupToBase (R := K))
  have h : Set.range (((C₁).blowupComponent (K := K) W).ι ≫ ν[C₁]) =
      Set.range (((C₁).blowupComponent (K := K) B).ι ≫ ν[C₁]) := by
    calc
      _ = ν[C₁] '' (H '' (A : Set _)) := by
        simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
          Scheme.coe_blowupComponent]
        rfl
      _ = (E).hom '' (ν[C₀] '' (A : Set _)) := by
        rw [Set.image_image, Set.image_image]
        exact Set.image_congr (fun x _ ↦ hcomp x)
      _ = (E).hom '' Set.range (u.boundaryComponentι K hΦ) := by
        rw [← Φ.range_boundaryNormalizationComponentEquiv K hΦ u]
        simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
          Scheme.coe_blowupComponent, A]
      _ = Set.range ((s u).boundaryComponentι K (hΨ)) :=
        image_rayComponent_mutationBoundaryIso b pivot hOpp c hΦ u
      _ = _ := ((Sheared).range_boundaryNormalizationComponentEquiv K (hΨ) (s u)).symm
  exact congrArg Subtype.val ((C₁).eq_of_range_blowupComponent_subset (k := K) h.le)

/-- An actual branch over a distinguished node, on a given normalized ray component,
maps to the branch over the sheared node on the corresponding component. For two
adjacent rays the determinant comparison preserves their ordering. -/
theorem Ray.mutationBoundaryIso_maps_branch
    {σ : Φ.cones} {ρ τ : Φ.Ray} (hne : ρ ≠ τ) (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ)
    (u : Φ.Ray) (q : Spec (.of K) ⟶ (C₀).branchScheme K)
    (hq : q ≫ j[C₀] ≫ ν[C₀] ≫ (D₀).subschemeι = Φ.distinguishedSection (R := K) σ) :
    let q' := q ≫ ((E).branchSchemeIso (R := K)).hom
    (q' ≫ j[C₁] ≫ ν[C₁] ≫ (D₁).subschemeι =
      (Sheared).distinguishedSection (R := K) ((coneEquiv) σ)) ∧
      ∀ x : Spec (.of K),
        j[C₀] (q x) ∈
          (Φ.boundaryNormalizationComponentEquiv K hΦ u : Set (Scheme.singularLocus K C₀).blowup) →
        j[C₁] (q' x) ∈ ((Sheared).boundaryNormalizationComponentEquiv K (hΨ) (s u) :
          Set (Scheme.singularLocus K C₁).blowup) := by
  dsimp only
  constructor
  · simp only [Category.assoc, Iso.branchSchemeIso_hom_branchSchemeToBlowup_assoc,
      Iso.singularLocusBlowupIso_hom_blowupToBase_assoc]
    exact pivot.mutationBoundaryIso_comp_distinguishedPointHom b hOpp c hΦ hne hρ hτ
      (p := q ≫ j[C₀] ≫ ν[C₀]) (by simpa only [Category.assoc] using hq)
  · intro x hx
    rw [← Scheme.Hom.comp_apply, Category.assoc, Iso.branchSchemeIso_hom_branchSchemeToBlowup,
      ← Category.assoc, Scheme.Hom.comp_apply,
      ← pivot.image_boundaryNormalizationComponent_mutationBoundaryIso b hOpp c hΦ u]
    exact ⟨_, hx, by rw [Scheme.Hom.comp_apply]⟩

/-- Mutation identifies the two branch sections selected by corresponding node and
ray labels. The labels specify the branch itself on the normalization. -/
theorem Ray.mutationBoundaryIso_branchSchemeIso_apply
    {σ : Φ.cones} {ρ τ : Φ.Ray} (hne : ρ ≠ τ) (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ)
    (u : Φ.Ray) (q : Spec (.of K) ⟶ (C₀).branchScheme K)
    (q' : Spec (.of K) ⟶ (C₁).branchScheme K)
    (hq : q ≫ j[C₀] ≫ ν[C₀] ≫ (D₀).subschemeι = Φ.distinguishedSection (R := K) σ)
    (hq' : q' ≫ j[C₁] ≫ ν[C₁] ≫ (D₁).subschemeι =
      (Sheared).distinguishedSection (R := K) ((coneEquiv) σ))
    (x : Spec (.of K))
    (hu : j[C₀] (q x) ∈
      (Φ.boundaryNormalizationComponentEquiv K hΦ u : Set (Scheme.singularLocus K C₀).blowup))
    (hu' : j[C₁] (q' x) ∈ ((Sheared).boundaryNormalizationComponentEquiv K (hΨ) (s u) :
      Set (Scheme.singularLocus K C₁).blowup)) :
    ((E).branchSchemeIso (R := K)).hom (q x) = q' x := by
  obtain ⟨hnode, hray⟩ := pivot.mutationBoundaryIso_maps_branch b hOpp c hΦ hne hρ hτ u q hq
  have hj : IsClosedImmersion (j[C₁]) :=
    MorphismProperty.of_isPullback ((C₁).isPullback_branchScheme K) inferInstance
  apply (j[C₁]).injective
  apply (s u).injOn_blowupToBase_boundaryNormalizationComponent K (hΨ)
  · simpa only [Scheme.Hom.comp_apply] using hray x hu
  · exact hu'
  · apply (D₁).subschemeι.injective
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun f : Spec (.of K) ⟶ ((Sheared).finiteFanScheme K) ↦ f x) (hnode.trans hq'.symm)

end Branches

end PivotBlowup

end TauCeti.Toric.Fan

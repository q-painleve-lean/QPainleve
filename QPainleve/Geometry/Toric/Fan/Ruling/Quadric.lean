/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Equiv
public import QPainleve.Geometry.Toric.Fan.Ruling.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import TauCeti.Geometry.Toric.Algebraic.Fan.Product.Basic

import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
import QPainleve.Geometry.Toric.Fan.CyclicOrder
import QPainleve.Geometry.Toric.Fan.Equiv
import QPainleve.Geometry.Toric.Fan.HalfPlane
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Segre
import TauCeti.Geometry.Toric.Algebraic.Fan.Product.Isomorphism

/-!
# The ruling exchange of the toric quadric

On the Hirzebruch fan of index zero, exchanging the two lattice basis vectors
gives a toric involution that preserves the reduced boundary. The same basis
identifies the fan with the product of two projective-line fans, so its
realization admits the Segre embedding.

The ruling exchange is the toric change of model used in Lutz's appendix to
Hacking and Keating, [*Homological mirror symmetry for log Calabi–Yau surfaces*,
proof of Theorem 8.4](https://arxiv.org/abs/2005.05010v3).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Module PointedCone

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

local notation "u" => Equiv.trans (RingEquiv.toEquiv (RingEquiv.symm (ZMod.finEquiv 4))) r
local notation "p" => (Equiv.subLeft (1 : ZMod 4))
local notation "b'" => b.reindex (Equiv.swap 0 1)
local notation "f" => b.equiv b (Equiv.swap 0 1)

include hr in
/-- The two rays in the second basis direction lie in the kernel of the
first coordinate character on the toric quadric. -/
theorem quadric_transverse_ruling_rays :
    hull ℝ {i (b 1)} ∈ Φ.cones ∧ hull ℝ {-i (b 1)} ∈ Φ.cones := by
  have h₁ : (r 1).primitiveGenerator = b 1 := congrFun hr 1
  have h₃ : (r 3).primitiveGenerator = -b 1 := by simpa using congrFun hr (3 : Fin 4)
  exact ⟨h₁ ▸ (r 1).hull_primitiveGenerator_mem, by
    simpa only [h₃, map_neg] using (r 3).hull_primitiveGenerator_mem⟩

include hr in
/-- On a toric quadric the first basis character defines the ruling transverse to
the fibers in the first basis direction. The character has constant weak sign on each cone. -/
theorem nonneg_or_nonpos_quadric_transverse_character (σ : Φ.cones) :
    (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter (b.coord 0).toAddMonoidHom x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter (b.coord 0).toAddMonoidHom x ≤ 0 := by
  obtain ⟨hpos, hneg⟩ := quadric_transverse_ruling_rays b r hr
  have hrev : (0 : Fin 2).rev = 1 := by decide
  simpa only [IsIntegralLattice.realCharacter_coord, Basis.coord_apply] using
    Φ.nonneg_or_nonpos_basis_repr_on_cone b 0 σ
      (fun _ ↦ by simpa only [hrev] using hpos)
      (fun _ ↦ by simpa only [hrev, map_neg] using hneg)

include hr in
private theorem quadric_rayGenerator (j : ZMod 4) :
    ((u) j).primitiveGenerator = ![b 0, b 1, -b 0, -b 1] ((ZMod.finEquiv 4).symm j) := by
  simpa only [Equiv.trans_apply, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
    zero_smul, zero_sub] using congrFun hr ((ZMod.finEquiv 4).symm j)

include hr in
private theorem quadric_det (j k : ZMod 4) :
    b.detDualEquiv ((u) j).primitiveGenerator ((u) k).primitiveGenerator =
      if k = j + 1 then 1 else if k = j - 1 then -1 else 0 := by
  obtain ⟨j, rfl⟩ := (ZMod.finEquiv 4).surjective j
  obtain ⟨k, rfl⟩ := (ZMod.finEquiv 4).surjective k
  simp only [quadric_rayGenerator b r hr, RingEquiv.symm_apply_apply,
    ← map_one (ZMod.finEquiv 4), ← map_add, ← map_sub, (ZMod.finEquiv 4).injective.eq_iff]
  let d : Matrix (Fin 4) (Fin 4) ℤ := !![0, 1, 0, -1; -1, 0, 1, 0; 0, -1, 0, 1; 1, 0, -1, 0]
  have hd (j k : Fin 4) : d j k = if k = j + 1 then 1 else if k = j - 1 then -1 else 0 := by
    fin_cases j <;> fin_cases k <;> decide
  rw [← hd j k]
  have hswap := b.detDualEquiv_swap (b 1) (b 0)
  rw [b.detDualEquiv_apply_basis_zero_one] at hswap
  fin_cases j <;> fin_cases k <;>
    norm_num [d, b.detDualEquiv_self,
      b.detDualEquiv_apply_basis_zero_one, hswap, -Basis.detDualEquiv_apply]

include hΦ hc hr in
private theorem quadric_cyclicRays (j : ZMod 4) :
    b.detDualEquiv ((u) j).primitiveGenerator ((u) (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, ((u) j).toCone ≤ σ ∧ ((u) (j + 1)).toCone ≤ σ := by
  refine ⟨by rw [quadric_det b r hr, ite_eq_left rfl], ?_⟩
  obtain ⟨prev, next, -, hnext, hn⟩ := Φ.exists_ray_neighbors b hΦ hc ((u) j)
  obtain ⟨k, rfl⟩ := (u).surjective next
  rw [quadric_det b r hr] at hnext
  split at hnext
  · rename_i hk
    subst k
    exact ((hn _).mpr (Or.inr rfl)).2
  · split at hnext <;> omega

local notation "P" => Fan.projectiveSpace (Pi.basisFun ℤ (Fin 1)) (isIntegralLattice_intCast 1)
local notation "PP" => Fan.prod P P
local notation "i₁" => AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin 1)
local notation "W" => (Fin 1 → ℝ)
local notation "Z₁" => (Fin 1 → ℤ)
local notation "coord₁" => LinearEquiv.funUnique (Fin 1) ℤ ℤ
local notation "d" => LinearEquiv.toAddEquiv (LinearEquiv.trans (Basis.equivFun b)
  (LinearEquiv.trans (LinearEquiv.finTwoArrow ℤ ℤ)
    (LinearEquiv.prodCongr (LinearEquiv.symm coord₁) (LinearEquiv.symm coord₁))))
local notation "coordℝ" => Φ.lattice.extendEquiv (Fan.lattice PP) d
local notation "F" => PointedCone.map (LinearEquiv.toLinearMap coordℝ)

private theorem quadric_coordinates_basis :
    d (b 0) = ((1 : Z₁), 0) ∧ d (b 1) = (0, (1 : Z₁)) := by
  have hz (j : Fin 2) : b.equivFun (b j) = Pi.single j 1 := by
    ext k
    simp [Pi.single_apply, eq_comm]
  have h1 : (AddEquiv.funUnique (Fin 1) ℤ).symm 1 = 1 := rfl
  constructor <;> simp [LinearEquiv.finTwoArrow, finTwoArrowEquiv, hz, LinearEquiv.funUnique, h1]

local notation "a" => affineRayCone
local notation "z" => negativeRayCone
local notation "rayCones" => (![Submodule.prod a ⊥, Submodule.prod ⊥ a, Submodule.prod z ⊥,
  Submodule.prod ⊥ z] : Fin 4 → PointedCone ℝ (W × W))

include hr in
private theorem map_quadric_ray (j : Fin 4) :
    F (r j).toCone.val = rayCones j := by
  rw [Ray.toCone_eq_hull_primitiveGenerator, PointedCone.map, Submodule.map_span,
    Set.image_singleton]
  -- The image of the single generator is evaluated by the real extension of the lattice map.
  have he : (↑(coordℝ).toLinearMap : V →ₗ[Nonneg ℝ] W × W) (i (r j).primitiveGenerator) =
      (AddMonoidHom.prodMap i₁ i₁) (d (r j).primitiveGenerator) :=
    Φ.lattice.extendEquiv_apply_lattice (PP).lattice d _
  rw [he, congrFun hr j]
  obtain ⟨h0, h1⟩ := quadric_coordinates_basis b
  have h2 : d (-b 0) = (-(1 : Z₁), 0) := by rw [map_neg, h0, Prod.neg_mk, neg_zero]
  have h3 : d (-b 1) = (0, -(1 : Z₁)) := by rw [map_neg, h1, Prod.neg_mk, neg_zero]
  have hull_axis_left (x : W) : hull ℝ {(x, (0 : W))} = (hull ℝ {x}).prod ⊥ := by
    rw [← Submodule.map_inl, Submodule.map_span, Set.image_singleton]
    rfl
  have hull_axis_right (x : W) :
      hull ℝ {((0 : W), x)} = (⊥ : PointedCone ℝ W).prod (hull ℝ {x}) := by
    rw [← Submodule.map_inr, Submodule.map_span, Set.image_singleton]
    rfl
  fin_cases j <;> simp [h0, h1, h2, h3, hull_axis_left, hull_axis_right, affineRayCone_def,
    negativeRayCone_def, intCast_finOne_one]

private theorem quadric_axis_mem_product_cones (j : Fin 4) : rayCones j ∈ (PP).cones := by
  rw [Fan.mem_prod_cones]
  simp only [projectiveSpace_finOne_eq_projectiveLineFan]
  have h0 := projectiveLineFan.bot_mem affineRayCone_mem_projectiveLineFan
  have ha := affineRayCone_mem_projectiveLineFan
  have hz := negativeRayCone_mem_projectiveLineFan
  fin_cases j
  · exact ⟨a, ha, ⊥, h0, rfl⟩
  · exact ⟨⊥, h0, a, ha, rfl⟩
  · exact ⟨z, hz, ⊥, h0, rfl⟩
  · exact ⟨⊥, h0, z, hz, rfl⟩

private theorem quadric_adjacent_mem_product_cones (j : Fin 4) :
    rayCones j ⊔ rayCones (j + 1) ∈ (PP).cones := by
  have ha := affineRayCone_mem_projectiveLineFan
  have hz := negativeRayCone_mem_projectiveLineFan
  have hprod (A B : PointedCone ℝ W) :
      A.prod (⊥ : PointedCone ℝ W) ⊔ (⊥ : PointedCone ℝ W).prod B = A.prod B := by
    rw [LinearMap.prod_eq_sup_map A B, Submodule.map_inl, Submodule.map_inr]
  rw [Fan.mem_prod_cones, projectiveSpace_finOne_eq_projectiveLineFan]
  fin_cases j
  · exact ⟨a, ha, a, ha, hprod a a⟩
  · exact ⟨z, hz, a, ha, (sup_comm _ _).trans (hprod z a)⟩
  · exact ⟨z, hz, z, hz, hprod z z⟩
  · exact ⟨a, ha, z, hz, (sup_comm _ _).trans (hprod a z)⟩

include hΦ hc hr in
/-- In the specified lattice coordinates, the toric quadric fan is the product
of two projective-line fans. -/
def quadricFanEquivProduct : FanEquiv Φ PP := by
  let A := Φ.mapEquiv (PP).lattice d
  have hA : A.cones ⊆ (PP).cones := by
    rw [mapEquiv_cones]
    rintro _ ⟨σ, hσ, rfl⟩
    rcases (mem_cones_iff_of_cyclicRays b hΦ hc u (quadric_cyclicRays b hΦ hc r hr)).mp hσ with
      rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [PointedCone.map, Submodule.map_bot]
      exact (PP).bot_mem (quadric_axis_mem_product_cones (0 : Fin 4))
    · simp only [Equiv.trans_apply]
      rw [map_quadric_ray b r hr]
      exact quadric_axis_mem_product_cones _
    · obtain ⟨k, rfl⟩ := (ZMod.finEquiv 4).surjective j
      simp only [← map_one (ZMod.finEquiv 4), ← map_add, Equiv.trans_apply,
        RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, RingEquiv.symm_apply_apply]
      have hmap (A B : PointedCone ℝ V) : F (A ⊔ B) = F A ⊔ F B := Submodule.map_sup ..
      rw [hmap, map_quadric_ray b r hr, map_quadric_ray b r hr]
      exact quadric_adjacent_mem_product_cones k
  have hcones := A.cones_eq_of_isComplete_of_subset (hc.mapEquiv _ _) hA
  refine ⟨d, coordℝ, Φ.lattice.extendEquiv_apply_lattice (PP).lattice d, fun σ ↦ ?_⟩
  rw [← hcones, mapEquiv_cones]
  constructor
  · rintro ⟨τ, hτ, he⟩
    have hinj : Function.Injective F := Submodule.map_injective_of_injective (coordℝ).injective
    exact hinj he ▸ hτ
  · exact Set.mem_image_of_mem F

include hΦ hc hr in
/-- The lattice map to the product fan is the pair of coordinates in the given basis. -/
@[simp]
theorem quadricFanEquivProduct_latticeEquiv_apply (x : N) :
    (Φ.quadricFanEquivProduct b hΦ hc r hr).latticeEquiv x =
      (fun _ ↦ b.coord 0 x, fun _ ↦ b.coord 1 x) := (rfl)

attribute [local instance] MvPolynomial.gradedAlgebra

open TauCeti.SymmetricAlgebra (homogeneousSubmodule)

local notation "J" => Fin 2
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "s" => Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule J ℂ)
local notation "lineIso" => projectiveLineToricIso ≪≫
  Iso.symm (Basis.polynomialProjIso (Pi.basisFun ℂ J))

include hΦ hc hr in
/-- The algebraic realization of the toric quadric is projective over the
coefficient field, via the Segre embedding of the product of projective lines. -/
theorem isProjectiveOver_quadric : Φ.algebraicRealization.IsProjectiveOver ℂ := by
  let e := (Φ.quadricFanEquivProduct b hΦ hc r hr).toFanHom
  have ho : (lineIso).hom ≫ s = (P).algebraicRealizationStructureMap := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← (Pi.basisFun ℂ J).polynomialProjIso_hom_over, Iso.inv_hom_id_assoc,
      ← TauCeti.SymmetricAlgebra.over_eq_projToSpec, comp_over, algebraicRealization_over]
  have hpb := (P).isPullback_fst_snd_algebraicMap P
  have ho' : (lineIso).inv ≫ (P).algebraicRealizationStructureMap = s ≫ (Iso.refl S).hom := by
    rw [← ho, Iso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id]
  let g₀ := e.algebraicMap ≫ (FanHom.fst P P).algebraicMap ≫ (lineIso).hom
  let g₁ := e.algebraicMap ≫ (FanHom.snd P P).algebraicMap ≫ (lineIso).hom
  have hp : IsPullback g₀ g₁ s s :=
    hpb.of_iso' (asIso e.algebraicMap) (lineIso).symm (lineIso).symm (Iso.refl S)
      (by simp [g₀]) (by simp [g₁]) ho' ho'
  let g := hp.isoPullback.hom ≫ Proj.segre (σ := J) (τ := J) ℂ ≫
    (Pi.basisFun ℂ (J × J)).polynomialProjIso.hom
  have : g.IsOver S := ⟨by
    simp only [g, Category.assoc, TauCeti.SymmetricAlgebra.over_eq_projToSpec,
      Basis.polynomialProjIso_hom_over, Proj.segre_toSpecCoeff,
      IsPullback.isoPullback_hom_fst_assoc, g₀, Category.assoc]
    rw [ho, FanHom.algebraicMap_comp_algebraicRealizationStructureMap,
      FanHom.algebraicMap_comp_algebraicRealizationStructureMap, algebraicRealization_over]⟩
  exact Scheme.IsProjectiveOver.of_isClosedImmersion ℂ g

include hΦ hc hr in
private theorem quadric_cyclicRays_swap (j : ZMod 4) :
    (b').detDualEquiv (((p).trans (u)) j).primitiveGenerator
      (((p).trans (u)) (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (((p).trans (u)) j).toCone ≤ σ ∧ (((p).trans (u)) (j + 1)).toCone ≤ σ := by
  have hstep : p (j + 1) + 1 = p j := by simp [Equiv.subLeft_apply, sub_eq_add_neg, add_comm]
  obtain ⟨hd, σ, h₀, h₁⟩ := quadric_cyclicRays b hΦ hc r hr (p (j + 1))
  rw [hstep] at hd h₁
  refine ⟨?_, σ, h₁, h₀⟩
  simp only [Equiv.trans_apply] at hd ⊢
  rw [Basis.detDualEquiv_reindex_swap, LinearMap.neg_apply, b.detDualEquiv_swap, hd, neg_neg]

include hr in
private theorem quadric_swap_generator (j : ZMod 4) :
    (f).toAddEquiv (((u) j).primitiveGenerator) = (((p).trans (u)) j).primitiveGenerator := by
  obtain ⟨j, rfl⟩ := (ZMod.finEquiv 4).surjective j
  simp only [Equiv.trans_apply ((p)) (u), quadric_rayGenerator b r hr, Equiv.subLeft_apply,
    map_sub, map_one, RingEquiv.symm_apply_apply]
  have hp (j : Fin 4) : 1 - j = (![1, 0, 3, 2] : Fin 4 → Fin 4) j := by
    fin_cases j <;> decide
  rw [hp j]
  fin_cases j <;> norm_num [LinearEquiv.coe_toAddEquiv, Basis.equiv_apply]

include hΦ hc hr in
/-- Exchanging the basis directions of a regular complete Hirzebruch fan of index
zero is a fan automorphism. -/
def quadricRulingExchange : FanEquiv Φ Φ :=
  fanEquivOfCyclicRays b (b') hΦ hΦ hc hc (u) ((p).trans (u))
    (quadric_cyclicRays b hΦ hc r hr) (quadric_cyclicRays_swap b hΦ hc r hr)
    (f).toAddEquiv (quadric_swap_generator b r hr)

local notation "E" => quadricRulingExchange b hΦ hc r hr
local notation "τ" => FanHom.algebraicMap (FanEquiv.toFanHom (E))

/-- The ruling exchange acts on the lattice by transposing the two basis directions. -/
@[simp]
theorem quadricRulingExchange_latticeEquiv : (E).latticeEquiv = (f).toAddEquiv :=
  fanEquivOfCyclicRays_latticeEquiv ..

/-- The ruling exchange is its own inverse as a fan equivalence. -/
@[simp]
theorem quadricRulingExchange_symm : (E).symm = E := by
  apply FanEquiv.ext
  rw [FanEquiv.symm_latticeEquiv, quadricRulingExchange_latticeEquiv]
  have he : (f).symm.toLinearMap = (f).toLinearMap := by
    apply b.ext
    intro j
    simp [Basis.equiv_symm, Basis.equiv_apply]
  exact AddEquiv.ext fun x ↦ by
    have hx := DFunLike.congr_fun he x
    exact hx

/-- The algebraic ruling exchange is an involution. -/
@[reassoc (attr := simp)]
theorem quadricRulingExchange_algebraicMap_comp : τ ≫ τ = 𝟙 Φ.algebraicRealization := by
  simpa only [quadricRulingExchange_symm] using (E).algebraicMap_comp_symm

variable [Nonempty Φ.cones]

/-- The ruling exchange preserves the reduced toric boundary as a closed subscheme. -/
@[simp]
theorem comap_boundaryIdeal_quadricRulingExchange :
    (Φ.boundaryIdeal inferInstance).comap τ = Φ.boundaryIdeal inferInstance :=
  (E).comap_boundaryIdeal_algebraicMap _ _

omit [Nonempty Φ.cones] in
/-- On the cyclic ray indices, the ruling exchange reverses the cycle and sends
index zero to index one. -/
@[simp]
theorem quadricRulingExchange_rayEquiv (j : Fin 4) :
    (E).rayEquiv (r j) = r (1 - j) := by
  apply Ray.primitiveGenerator_injective
  rw [FanEquiv.primitiveGenerator_rayEquiv, quadricRulingExchange_latticeEquiv]
  have h := quadric_swap_generator b r hr ((ZMod.finEquiv 4) j)
  simpa only [Equiv.trans_apply, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
    RingEquiv.symm_apply_apply, Equiv.subLeft_apply, ← map_one (ZMod.finEquiv 4),
    ← map_sub] using h

end TauCeti.Toric.Fan

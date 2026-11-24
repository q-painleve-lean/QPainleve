/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.Ruling.Basic
public import TauCeti.Geometry.Toric.Algebraic.Fan.Equiv
public import TauCeti.Geometry.Toric.Algebraic.Fan.Product.Basic

import QPainleve.Geometry.Toric.Fan.Hirzebruch.Corner
import QPainleve.Geometry.Toric.Fan.Scheme
import QPainleve.Geometry.Toric.Lattice
import Mathlib.LinearAlgebra.Transvection.Basic
import TauCeti.Data.Fin.Rev
import TauCeti.Geometry.Toric.Algebraic.Fan.Product.Isomorphism
import TauCeti.Geometry.Toric.Algebraic.Fan.SubfanScheme

/-!
# Affine trivializations of Hirzebruch rulings

Over each affine chart of the toric projective line, the ruling of a Hirzebruch
fan is a product with a projective line. The first affine chart uses the given
lattice basis. On the other chart an integral shear takes the other transverse
ray to the axis, keeping the base character unchanged. This determines the monomial change of
coordinates used to compare Hirzebruch surfaces with split projective bundles.

The scheme comparisons use Tau Ceti's
`FanHom.isPullback_preimageSubfan_algebraicMap` and
`Fan.isPullback_fst_snd_algebraicMap`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Module PointedCone
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric.Fan

private abbrev lineFan := Fan.projectiveSpace (Pi.basisFun ℤ (Fin 1)) (isIntegralLattice_intCast 1)

private abbrev baseRay (k : Fin 2) : PointedCone ℝ (Fin 1 → ℝ) :=
  if k = 0 then affineRayCone else negativeRayCone

private theorem baseRay_mem (k : Fin 2) : baseRay k ∈ lineFan.cones := by
  rw [lineFan, projectiveSpace_finOne_eq_projectiveLineFan]
  fin_cases k
  · exact affineRayCone_mem_projectiveLineFan
  · exact negativeRayCone_mem_projectiveLineFan

private abbrev chartFaces (k : Fin 2) : Set (PointedCone ℝ (Fin 1 → ℝ)) :=
  {τ | τ.IsFaceOf (baseRay k)}

private theorem chartFaces_subset (k : Fin 2) : chartFaces k ⊆ lineFan.cones :=
  lineFan.isFaceOf_subset_cones (baseRay_mem k)

private theorem chartFaces_closed (k : Fin 2) ⦃σ τ⦄
    (hσ : σ ∈ chartFaces k) (hτ : τ.IsFaceOf σ) : τ ∈ chartFaces k :=
  hτ.trans hσ

/-- The subfan of the projective line on the positive ray for index zero and on
the negative ray for index one. -/
@[implicit_reducible]
def projectiveLineAffineFan (k : Fin 2) :=
  lineFan.subfan (chartFaces k) (chartFaces_subset k) (chartFaces_closed k)

/-- The cones of the affine chart are the faces of its chosen ray. -/
theorem mem_projectiveLineAffineFan_cones {k : Fin 2} {σ : PointedCone ℝ (Fin 1 → ℝ)} :
    σ ∈ (projectiveLineAffineFan k).cones ↔
      σ.IsFaceOf (if k = 0 then affineRayCone else negativeRayCone) := by
  rw [projectiveLineAffineFan, Fan.subfan_cones]
  rfl

private abbrev chartInclusion (k : Fin 2) : FanHom (projectiveLineAffineFan k) lineFan :=
  lineFan.subfanInclusion (chartFaces k) (chartFaces_subset k) (chartFaces_closed k)

/-- The inclusion of the affine toric chart into the projective line. -/
def projectiveLineAffineFanι (k : Fin 2) :
    (projectiveLineAffineFan k).algebraicRealization ⟶ projectiveLine ℂ :=
  (chartInclusion k).algebraicMap ≫ projectiveLineToricIso.hom

instance (k : Fin 2) : IsOpenImmersion (projectiveLineAffineFanι k) := by
  rw [projectiveLineAffineFanι]
  let : IsOpenImmersion (chartInclusion k).algebraicMap :=
    lineFan.isOpenImmersion_subfanInclusion_algebraicMap (chartFaces k)
      (chartFaces_subset k) (chartFaces_closed k)
  infer_instance

instance (k : Fin 2) : IsAffine (projectiveLineAffineFan k).algebraicRealization := by
  let U := projectiveLineAffineFan k
  let σ : U.cones := ⟨baseRay k, mem_projectiveLineAffineFan_cones.mpr (.refl _)⟩
  have : IsIso (U.affineToricChartι σ) :=
    U.isIso_affineToricChartι_of_forall_le (σ := σ) fun τ ↦
      (mem_projectiveLineAffineFan_cones.mp τ.property).le
  exact IsAffine.of_isIso (inv (U.affineToricChartι σ))

/-- Each point of the projective line belongs to one of the two affine toric charts. -/
theorem exists_projectiveLineAffineFanι_apply_eq (x : projectiveLine ℂ) :
    ∃ (k : Fin 2) (y : (projectiveLineAffineFan k).algebraicRealization),
      projectiveLineAffineFanι k y = x := by
  obtain ⟨σ, y, hy⟩ :=
    lineFan.exists_affineToricChartι_apply_eq (projectiveLineToricIso.inv x)
  have hσ : ∃ k : Fin 2, σ.val ∈ (projectiveLineAffineFan k).cones := by
    have hs := σ.property
    simp only [lineFan, projectiveSpace_finOne_eq_projectiveLineFan,
      mem_projectiveLineFan_cones] at hs
    rcases hs with h | h | h
    · exact ⟨0, mem_projectiveLineAffineFan_cones.mpr
        (h ▸ isRegularCone_affineRayCone.toIsToricCone.salient.bot_isFaceOf)⟩
    · exact ⟨0, mem_projectiveLineAffineFan_cones.mpr (h ▸ .refl _)⟩
    · exact ⟨1, mem_projectiveLineAffineFan_cones.mpr (h ▸ .refl _)⟩
  obtain ⟨k, hk⟩ := hσ
  let τ : (projectiveLineAffineFan k).cones := ⟨σ.val, hk⟩
  have hτ : (projectiveLineAffineFan k).affineToricChartι τ ≫
      (chartInclusion k).algebraicMap = lineFan.affineToricChartι σ :=
    affineToricChartι_comp_subfanInclusion_algebraicMap lineFan
      (chartFaces k) (chartFaces_subset k) (chartFaces_closed k) τ
  refine ⟨k, (projectiveLineAffineFan k).affineToricChartι τ y, ?_⟩
  rw [← Scheme.Hom.comp_apply, projectiveLineAffineFanι, ← Category.assoc, hτ,
    Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  rfl

local notation "Z₁" => Fin 1 → ℤ
local notation "W" => Fin 1 → ℝ
local notation "i₁" => AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin 1)
local notation "S" => Spec (CommRingCat.of ℂ)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (e : ℤ)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

private abbrev rulingFanHom :=
  Φ.characterFanHom (b.coord 1).toAddMonoidHom
    (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)

/-- The open subfan of a Hirzebruch surface over the indicated affine chart of its ruling. -/
@[implicit_reducible]
def hirzebruchRulingAffineFan (k : Fin 2) :=
  (rulingFanHom b e r hr).preimageSubfan (chartFaces k) (chartFaces_closed k)

/-- The fan map obtained by restricting the ruling to an affine chart of its base. -/
def hirzebruchRulingAffineFanProjection (k : Fin 2) :
    FanHom (hirzebruchRulingAffineFan b e r hr k) (projectiveLineAffineFan k) :=
  (rulingFanHom b e r hr).restrictToPreimage (chartFaces k) (chartFaces_subset k)
    (chartFaces_closed k)

/-- The inclusion of an affine ruling subfan into the Hirzebruch fan. -/
def hirzebruchRulingAffineFanInclusion (k : Fin 2) :
    FanHom (hirzebruchRulingAffineFan b e r hr k) Φ :=
  Φ.subfanInclusion _ ((rulingFanHom b e r hr).preimageCones_subset (chartFaces k))
    ((rulingFanHom b e r hr).preimageCones_closedUnderFaces (chartFaces k) (chartFaces_closed k))

/-- The affine ruling projection has the same character as the original ruling. -/
@[simp]
theorem hirzebruchRulingAffineFanProjection_latticeMap (k : Fin 2) (x : N) (j : Fin 1) :
    (hirzebruchRulingAffineFanProjection b e r hr k).latticeMap x j = b.coord 1 x := by
  rw [hirzebruchRulingAffineFanProjection, FanHom.restrictToPreimage_latticeMap,
    characterFanHom_latticeMap]
  rfl

/-- Including the affine chart leaves the lattice point unchanged. -/
@[simp]
theorem hirzebruchRulingAffineFanInclusion_latticeMap (k : Fin 2) (x : N) :
    (hirzebruchRulingAffineFanInclusion b e r hr k).latticeMap x = x := by
  rw [hirzebruchRulingAffineFanInclusion, subfanInclusion_latticeMap]
  rfl

private abbrev productFan (k : Fin 2) := lineFan.prod (projectiveLineAffineFan k)

private abbrev shearParameter (k : Fin 2) (e : ℤ) := if k = 0 then 0 else e

local notation "P" => LinearEquiv.funUnique (Fin 1) ℤ ℤ

private def chartCoordinates (k : Fin 2) : N ≃+ (Z₁ × Z₁) :=
  let shear := LinearEquiv.transvection (f := shearParameter k e • b.coord 1) (v := b 0)
    (by fin_cases k <;> simp [shearParameter, Basis.coord_apply])
  let pair := (LinearEquiv.finTwoArrow ℤ ℤ).trans
    (LinearEquiv.prodCongr (LinearEquiv.symm P) (LinearEquiv.symm P))
  (shear.trans (b.equivFun.trans pair)).toAddEquiv

private theorem chartCoordinates_apply (k : Fin 2) (x : N) :
    chartCoordinates b e k x =
      (fun _ ↦ b.coord 0 x + shearParameter k e * b.coord 1 x, fun _ ↦ b.coord 1 x) := by
  fin_cases k <;> ext j <;> simp [chartCoordinates, LinearMap.transvection.apply,
    Basis.equivFun_apply, Basis.coord_apply, LinearEquiv.finTwoArrow, finTwoArrowEquiv,
    LinearEquiv.funUnique, add_comm]

private abbrev chartRealCoordinates (Φ : Fan i) (k : Fin 2) :=
  Φ.lattice.extendEquiv (productFan k).lattice (chartCoordinates b e k)

local notation "L[" k "]" => chartRealCoordinates b e Φ k
local notation "F[" k "]" => PointedCone.map (LinearEquiv.toLinearMap (L[k]))

private abbrev fiberRay (k : Fin 2) : Fin 4 := ![1, 3] k

/-- A cone belongs to the affine ruling chart exactly when its image lies in
the selected base ray. -/
theorem mem_hirzebruchRulingAffineFan_cones_iff (k : Fin 2) {σ : PointedCone ℝ V} :
    σ ∈ (hirzebruchRulingAffineFan b e r hr k).cones ↔
      σ ∈ Φ.cones ∧ σ.map (Φ.characterFanHom (b.coord 1).toAddMonoidHom
        (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)).realMap ≤
          (if k = 0 then affineRayCone else negativeRayCone) := by
  let f := rulingFanHom b e r hr
  rw [hirzebruchRulingAffineFan, Fan.subfan_cones]
  constructor
  · intro h
    have hσ := f.preimageCones_subset (chartFaces k) h
    have hf : (f.leastCone hσ).IsFaceOf (baseRay k) := (f.mem_preimageCones_iff _ hσ).mp h
    exact ⟨hσ, (f.map_le_leastCone hσ).trans hf.le⟩
  · rintro ⟨hσ, hs⟩
    exact (f.mem_preimageCones_iff _ hσ).mpr
      (lineFan.isFaceOf_of_le (baseRay_mem k) (f.leastCone_mem hσ)
        (f.leastCone_le hσ (baseRay_mem k) hs))

include hr in
private theorem fiberRay_mem_chart_iff (k l : Fin 2) :
    (r (fiberRay l)).toCone.val ∈ (hirzebruchRulingAffineFan b e r hr k).cones ↔ l = k := by
  rw [mem_hirzebruchRulingAffineFan_cones_iff, and_iff_right (r (fiberRay l)).toCone.property,
    Ray.toCone_eq_hull_primitiveGenerator, PointedCone.map, Submodule.map_span,
    Set.image_singleton, Submodule.span_singleton_le_iff_mem]
  fin_cases k <;> fin_cases l <;>
    norm_num [baseRay, fiberRay, mem_affineRayCone_iff, mem_negativeRayCone_iff,
      characterFanHom_realMap, IsIntegralLattice.realCharacter_apply, congrFun hr,
      Basis.coord_apply]

private theorem mem_rulingSubfan_of_le (k : Fin 2) {σ τ : Φ.cones}
    (hσ : σ.val ∈ (hirzebruchRulingAffineFan b e r hr k).cones) (h : τ ≤ σ) :
    τ.val ∈ (hirzebruchRulingAffineFan b e r hr k).cones := by
  rw [mem_hirzebruchRulingAffineFan_cones_iff] at hσ ⊢
  exact ⟨τ.property, (Submodule.map_mono h).trans hσ.2⟩

private abbrev sectionRay (j : Fin 2) : Fin 4 := ![0, 2] j

private abbrev corner (j k : Fin 2) : PointedCone ℝ V :=
  (r (sectionRay j)).toCone.val ⊔ (r (fiberRay k)).toCone.val

include hr in
private theorem corner_mem (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (j k : Fin 2) :
    corner r j k ∈ Φ.cones := by
  obtain ⟨σ, hs, hf⟩ := exists_cone_of_hirzebruch_section_fiber b e r hr hΦ hc j k
  have hne : r (sectionRay j) ≠ r (fiberRay k) := by
    apply r.injective.ne
    fin_cases j <;> fin_cases k <;> decide
  have hd : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  rw [corner, ← Φ.cone_eq_sup_of_ray_ne_of_le hΦ hd hne hs hf]
  exact σ.property

include hr in
private theorem corner_mem_rulingSubfan (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (j k : Fin 2) :
    corner r j k ∈ (hirzebruchRulingAffineFan b e r hr k).cones := by
  rw [mem_hirzebruchRulingAffineFan_cones_iff]
  refine ⟨corner_mem b e r hr hΦ hc j k, ?_⟩
  rw [corner, PointedCone.map, Submodule.map_sup, sup_le_iff]
  refine ⟨?_, ((mem_hirzebruchRulingAffineFan_cones_iff b e r hr k).mp
    ((fiberRay_mem_chart_iff b e r hr k k).mpr rfl)).2⟩
  rw [Ray.toCone_eq_hull_primitiveGenerator, Submodule.map_span,
    Set.image_singleton, Submodule.span_singleton_le_iff_mem]
  have hz : (rulingFanHom b e r hr).realMap (i (r (sectionRay j)).primitiveGenerator) = 0 := by
    ext l
    fin_cases j <;>
      simp [sectionRay, characterFanHom_realMap, IsIntegralLattice.realCharacter_apply,
        congrFun hr, Basis.coord_apply]
  simpa only [LinearMap.coe_restrictScalars, hz] using (zero_mem (baseRay k))

include hr in
private theorem le_corner_of_mem_rulingSubfan
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (k : Fin 2) {σ : Φ.cones}
    (hσ : σ.val ∈ (hirzebruchRulingAffineFan b e r hr k).cones) :
    ∃ j : Fin 2, σ.val ≤ corner r j k := by
  have hs : ¬ ((r 0).toCone ≤ σ ∧ (r 2).toCone ≤ σ) := by
    rintro ⟨h₀, h₂⟩
    have hx := h₀ (r 0).primitiveGenerator_mem
    have hy := h₂ (r 2).primitiveGenerator_mem
    have hx' : i (b 0) ∈ σ.val := by simpa [congrFun hr 0] using hx
    have hy' : - i (b 0) ∈ σ.val := by simpa [congrFun hr 2] using hy
    exact (Φ.isToricCone σ.property).salient (i (b 0)) hx'
      (fun hz ↦ b.ne_zero 0 (Φ.lattice.injective (hz.trans (map_zero i).symm))) hy'
  have aux {j : Fin 2} (hj : ¬ (r (sectionRay j.rev)).toCone ≤ σ) :
      σ.val ≤ corner r j k := by
    apply Φ.le_iff_forall_ray_le (sigma := σ)
      (tau := ⟨corner r j k, corner_mem b e r hr hΦ hc j k⟩) |>.mpr
    intro ρ hρ
    obtain ⟨l, rfl⟩ := r.surjective ρ
    have hcases : (∃ a : Fin 2, l = sectionRay a) ∨ ∃ a : Fin 2, l = fiberRay a := by
      fin_cases l
      · exact Or.inl ⟨0, rfl⟩
      · exact Or.inr ⟨0, rfl⟩
      · exact Or.inl ⟨1, rfl⟩
      · exact Or.inr ⟨1, rfl⟩
    rcases hcases with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rcases Fin.fin_two_eq_or_eq_rev j a with h | ha
      · subst a
        exact le_sup_left (a := (r (sectionRay j)).toCone.val)
          (b := (r (fiberRay k)).toCone.val)
      · exact (hj (by simpa only [ha] using hρ)).elim
    · have ha := (fiberRay_mem_chart_iff b e r hr k a).mp
        (mem_rulingSubfan_of_le b e r hr k hσ hρ)
      rw [ha]
      exact le_sup_right (a := (r (sectionRay j)).toCone.val)
        (b := (r (fiberRay k)).toCone.val)
  by_cases h₀ : (r 0).toCone ≤ σ
  · exact ⟨0, aux (j := 0) (fun h₂ ↦ hs ⟨h₀, h₂⟩)⟩
  · exact ⟨1, aux (j := 1) h₀⟩

private theorem map_chart_hull (k : Fin 2) (v : N) :
    F[k] (hull ℝ {i v}) =
      hull ℝ {AddMonoidHom.prodMap i₁ i₁ (chartCoordinates b e k v)} := by
  rw [PointedCone.map, Submodule.map_span, Set.image_singleton]
  congr 2
  exact Φ.lattice.extendEquiv_apply_lattice (productFan k).lattice (chartCoordinates b e k) v

include hr in
private theorem map_sectionRay (j k : Fin 2) :
    F[k] (r (sectionRay j)).toCone.val = (baseRay j).prod (⊥ : PointedCone ℝ W) := by
  rw [Ray.toCone_eq_hull_primitiveGenerator, map_chart_hull b e k]
  have hL (x : W) : hull ℝ {(x, (0 : W))} = (hull ℝ {x}).prod (⊥ : PointedCone ℝ W) := by
    rw [← Submodule.map_inl, Submodule.map_span, Set.image_singleton]
    rfl
  fin_cases j
  · simpa [sectionRay, chartCoordinates_apply, congrFun hr, Basis.coord_apply, baseRay,
      AddMonoidHom.compLeft, Function.comp_def, affineRayCone_def, Pi.one_def, Pi.zero_def]
      using hL 1
  · simpa [sectionRay, chartCoordinates_apply, congrFun hr, Basis.coord_apply, baseRay,
      AddMonoidHom.compLeft, Function.comp_def, negativeRayCone_def, Pi.one_def, Pi.zero_def,
      Pi.neg_def] using hL (-1)

include hr in
private theorem map_fiberRay (k : Fin 2) :
    F[k] (r (fiberRay k)).toCone.val = (⊥ : PointedCone ℝ W).prod (baseRay k) := by
  rw [Ray.toCone_eq_hull_primitiveGenerator, map_chart_hull b e k]
  have hR (x : W) : hull ℝ {((0 : W), x)} = (⊥ : PointedCone ℝ W).prod (hull ℝ {x}) := by
    rw [← Submodule.map_inr, Submodule.map_span, Set.image_singleton]
    rfl
  fin_cases k
  · simpa [fiberRay, chartCoordinates_apply, congrFun hr, Basis.coord_apply, baseRay,
      shearParameter, AddMonoidHom.compLeft, Function.comp_def, affineRayCone_def, Pi.one_def,
      Pi.zero_def] using hR 1
  · simpa [fiberRay, chartCoordinates_apply, congrFun hr, Basis.coord_apply, baseRay,
      shearParameter, AddMonoidHom.compLeft, Function.comp_def, negativeRayCone_def, Pi.one_def,
      Pi.zero_def, Pi.neg_def] using hR (-1)

include hr in
private theorem map_corner (j k : Fin 2) :
    F[k] (corner r j k) = (baseRay j).prod (baseRay k) := by
  have hmap (σ τ : PointedCone ℝ V) : F[k] (σ ⊔ τ) = F[k] σ ⊔ F[k] τ :=
    Submodule.map_sup ..
  rw [corner, hmap, map_sectionRay b e r hr, map_fiberRay b e r hr,
    LinearMap.prod_eq_sup_map (baseRay j) (baseRay k), Submodule.map_inl, Submodule.map_inr]

private theorem productCorner_mem (j k : Fin 2) :
    (baseRay j).prod (baseRay k) ∈ (productFan k).cones :=
  (Fan.mem_prod_cones ..).mpr ⟨_, baseRay_mem j, _, PointedCone.IsFaceOf.refl _, rfl⟩

private theorem le_productCorner_of_mem (k : Fin 2) {σ : PointedCone ℝ (W × W)}
    (hσ : σ ∈ (productFan k).cones) :
    ∃ j : Fin 2, σ ≤ (baseRay j).prod (baseRay k) := by
  obtain ⟨a, ha, c, hc, rfl⟩ := (Fan.mem_prod_cones ..).mp hσ
  rw [lineFan, projectiveSpace_finOne_eq_projectiveLineFan, mem_projectiveLineFan_cones] at ha
  have hck : c.IsFaceOf (baseRay k) := by
    simpa only [projectiveLineAffineFan, Fan.subfan_cones, chartFaces, Set.mem_ofPred_eq] using hc
  rcases ha with rfl | rfl | rfl
  · exact ⟨0, Submodule.prod_mono bot_le hck.le⟩
  · exact ⟨0, Submodule.prod_mono le_rfl hck.le⟩
  · exact ⟨1, Submodule.prod_mono le_rfl hck.le⟩

include hr in
/-- The affine ruling chart is the product fan in the integral coordinates
adapted to the section and the fiber over that chart. -/
def hirzebruchRulingAffineFanEquiv (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (k : Fin 2) :
    FanEquiv (hirzebruchRulingAffineFan b e r hr k)
      ((Fan.projectiveSpace (Pi.basisFun ℤ (Fin 1)) (isIntegralLattice_intCast 1)).prod
        (projectiveLineAffineFan k)) where
  latticeEquiv := chartCoordinates b e k
  realEquiv := L[k]
  map_lattice := Φ.lattice.extendEquiv_apply_lattice (productFan k).lattice _
  map_mem σ := by
    let U := hirzebruchRulingAffineFan b e r hr k
    let Wk := productFan k
    constructor
    · intro hσ
      obtain ⟨j, hj⟩ := le_productCorner_of_mem k hσ
      have hface := Wk.isFaceOf_of_le (productCorner_mem j k) hσ hj
      rw [← map_corner b e r hr j k] at hface
      exact U.mem_of_isFaceOf (corner_mem_rulingSubfan b e r hr hΦ hc j k)
        (hface.of_map_injective (L[k]).injective)
    · intro hσ
      have hσΦ := ((mem_hirzebruchRulingAffineFan_cones_iff b e r hr k).mp hσ).1
      obtain ⟨j, hj⟩ := le_corner_of_mem_rulingSubfan b e r hr hΦ hc k
        (σ := ⟨σ, hσΦ⟩) hσ
      have hface := U.isFaceOf_of_le (corner_mem_rulingSubfan b e r hr hΦ hc j k) hσ hj
      apply Wk.mem_of_isFaceOf (productCorner_mem j k)
      rw [← map_corner b e r hr j k]
      exact hface.map _ (L[k]).injective

include hr in
private theorem snd_comp_hirzebruchRulingAffineFanEquiv (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (k : Fin 2) :
    (FanHom.snd lineFan (projectiveLineAffineFan k)).comp
      (hirzebruchRulingAffineFanEquiv b e r hr hΦ hc k).toFanHom =
      hirzebruchRulingAffineFanProjection b e r hr k := by
  apply FanHom.ext
  ext x j
  simp [hirzebruchRulingAffineFanEquiv, chartCoordinates_apply]

include hr in
/-- The chart of index zero uses the original fiber coordinate. On the chart
of index one the lattice coordinate is sheared by the Hirzebruch parameter. -/
theorem hirzebruchRulingAffineFanEquiv_latticeEquiv_apply
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (k : Fin 2) (x : N) :
    (hirzebruchRulingAffineFanEquiv b e r hr hΦ hc k).latticeEquiv x =
      (fun _ ↦ b.coord 0 x + (if k = 0 then 0 else e) * b.coord 1 x,
        fun _ ↦ b.coord 1 x) :=
  chartCoordinates_apply b e k x

include hr in
/-- From the positive chart to the negative chart the fiber coordinate changes
by adding the Hirzebruch parameter times the base coordinate. On characters
this gives the change of fiber monomial from `u` to `u * t ^ e`. -/
theorem hirzebruchRulingAffineFanEquiv_latticeEquiv_transition
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (x : N) :
    (hirzebruchRulingAffineFanEquiv b e r hr hΦ hc 1).latticeEquiv x =
      let x₀ := (hirzebruchRulingAffineFanEquiv b e r hr hΦ hc 0).latticeEquiv x
      (x₀.1 + e • x₀.2, x₀.2) := by
  ext j <;> simp [hirzebruchRulingAffineFanEquiv_latticeEquiv_apply]

local notation "g" => Fan.characterRuling Φ (LinearMap.toAddMonoidHom (Basis.coord b 1))
  (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)

include hr in
/-- The toric scheme of an affine ruling subfan is the scheme-theoretic
preimage of the corresponding affine chart. -/
theorem isPullback_hirzebruchRulingAffineFan (k : Fin 2) :
    IsPullback (hirzebruchRulingAffineFanInclusion b e r hr k).algebraicMap
      (hirzebruchRulingAffineFanProjection b e r hr k).algebraicMap
      g (projectiveLineAffineFanι k) := by
  have hbase : IsPullback (chartInclusion k).algebraicMap (𝟙 _)
      projectiveLineToricIso.hom (projectiveLineAffineFanι k) :=
    IsPullback.of_vert_isIso ⟨by rw [Category.id_comp, projectiveLineAffineFanι]⟩
  have hpre : IsPullback (hirzebruchRulingAffineFanInclusion b e r hr k).algebraicMap
      (hirzebruchRulingAffineFanProjection b e r hr k).algebraicMap
      (rulingFanHom b e r hr).algebraicMap
      (chartInclusion k).algebraicMap :=
    (rulingFanHom b e r hr).isPullback_preimageSubfan_algebraicMap
      (chartFaces k) (chartFaces_subset k) (chartFaces_closed k)
  simpa only [Category.comp_id, characterRuling_def] using hpre.paste_vert hbase

include hr in
private theorem isPullback_rulingProduct (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (k : Fin 2) :
    IsPullback
      ((hirzebruchRulingAffineFanEquiv b e r hr hΦ hc k).toFanHom.algebraicMap ≫
        (FanHom.fst lineFan (projectiveLineAffineFan k)).algebraicMap ≫
        projectiveLineToricIso.hom)
      (hirzebruchRulingAffineFanProjection b e r hr k).algebraicMap
      (projectiveLine ℂ ↘ S) (projectiveLineAffineFan k).algebraicRealizationStructureMap := by
  refine (lineFan.isPullback_fst_snd_algebraicMap (projectiveLineAffineFan k)).of_iso'
    (asIso (hirzebruchRulingAffineFanEquiv b e r hr hΦ hc k).toFanHom.algebraicMap)
    projectiveLineToricIso.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [Category.assoc]
  · simpa only [asIso_hom, Iso.refl_hom, Category.comp_id, ← FanHom.algebraicMap_comp]
      using congrArg FanHom.algebraicMap (snd_comp_hirzebruchRulingAffineFanEquiv
        b e r hr hΦ hc k)
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom,
      ← cancel_epi projectiveLineToricIso.hom, Iso.hom_inv_id_assoc,
      ← Fan.algebraicRealization_over, CategoryTheory.comp_over]
  · simp

include hr in
/-- Over either affine toric chart of the base, a complete regular Hirzebruch
surface is the product of that chart with the projective line. -/
def hirzebruchRulingAffineIso (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (k : Fin 2) :
    pullback g (projectiveLineAffineFanι k) ≅
      pullback (projectiveLine ℂ ↘ S)
        (projectiveLineAffineFan k).algebraicRealizationStructureMap :=
  (isPullback_hirzebruchRulingAffineFan b e r hr k).isoPullback.symm ≪≫
    (isPullback_rulingProduct b e r hr hΦ hc k).isoPullback

include hr in
/-- The product trivialization is an isomorphism over the given affine base chart. -/
@[reassoc (attr := simp)]
theorem hirzebruchRulingAffineIso_hom_snd (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (k : Fin 2) :
    (hirzebruchRulingAffineIso b e r hr hΦ hc k).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  simp only [hirzebruchRulingAffineIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    IsPullback.isoPullback_hom_snd]
  exact (isPullback_hirzebruchRulingAffineFan b e r hr k).isoPullback_inv_snd

include hr in
/-- The fiber projection of the scheme trivialization is induced by the
first coordinate of the affine fan equivalence. -/
@[reassoc]
theorem hirzebruchRulingAffineIso_hom_fst (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (k : Fin 2) :
    (isPullback_hirzebruchRulingAffineFan b e r hr k).isoPullback.hom ≫
      (hirzebruchRulingAffineIso b e r hr hΦ hc k).hom ≫ pullback.fst _ _ =
      (hirzebruchRulingAffineFanEquiv b e r hr hΦ hc k).toFanHom.algebraicMap ≫
        (FanHom.fst (Fan.projectiveSpace (Pi.basisFun ℤ (Fin 1)) (isIntegralLattice_intCast 1))
          (projectiveLineAffineFan k)).algebraicMap ≫ projectiveLineToricIso.hom := by
  simp only [hirzebruchRulingAffineIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc, IsPullback.isoPullback_hom_fst]

end TauCeti.Toric.Fan

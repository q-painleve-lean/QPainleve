/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter
public import QPainleve.Geometry.Toric.Fan.Boundary.Ideal
public import QPainleve.Geometry.Toric.Fan.Subdivision.FunctionField
public import TauCeti.AlgebraicGeometry.Blowup.StrictTransform

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Reduced
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import QPainleve.AlgebraicGeometry.Morphisms.Pullback.IsoLocus
import QPainleve.AlgebraicGeometry.Scheme.FunctionField
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order
import TauCeti.RingTheory.LocalRing.Basic

/-!
# The boundary under a fan subdivision

The inverse image of the dense torus under a subdivision is the dense torus.
Consequently the reduced inverse image of the toric boundary is the toric
boundary of the subdividing fan. Every old ray survives and its affine chart is unchanged.
For subdivisions realized as blowups, the surviving ray divisors give the strict transforms.
In particular, each binomial center on the old boundary pulls back to the center with
the same primitive orbit character and parameter.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.IsSubdivision

universe u

section Boundary

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} (h : Φ.IsSubdivision Ψ)
  (hΦ : Nonempty Φ.cones) (hΨ : Nonempty Ψ.cones)

/-- The reduced inverse image of the toric boundary is the boundary of the subdivision. -/
theorem radical_comap_boundaryIdeal :
    ((Ψ.boundaryIdeal hΨ).comap h.toFanHom.algebraicMap).radical = Φ.boundaryIdeal hΦ := by
  rw [← vanishingIdeal_support, Φ.boundaryIdeal_def]
  congr 1
  apply SetLike.coe_injective
  rw [support_comap, Closeds.coe_preimage, Ψ.support_boundaryIdeal,
    Set.preimage_compl, h.preimage_range_denseTorusι hΦ hΨ]
  rfl

/-- An isomorphism over a subdivision morphism identifies the reduced inverse image
of the original boundary with the boundary of the subdivision. -/
theorem radical_comap_boundaryIdeal_of_iso {Y : Scheme.{u}}
    (f : Y ⟶ Ψ.algebraicRealization) (e : Φ.algebraicRealization ≅ Y)
    (he : e.hom ≫ f = h.toFanHom.algebraicMap) :
    (((Ψ.boundaryIdeal hΨ).comap f).radical).comap e.hom = Φ.boundaryIdeal hΦ := by
  rw [← radical_comap_of_isOpenImmersion, ← comap_comp, he, h.radical_comap_boundaryIdeal hΦ hΨ]

/-- The subdivision morphism restricted to the reduced toric boundaries. -/
noncomputable def boundaryMap :
    (Φ.boundaryIdeal hΦ).subscheme ⟶ (Ψ.boundaryIdeal hΨ).subscheme :=
  subschemeMap _ _ h.toFanHom.algebraicMap (le_map_iff_comap_le.mpr
    ((le_radical _).trans_eq (h.radical_comap_boundaryIdeal hΦ hΨ)))

/-- The boundary map commutes with the ambient toric morphism. -/
@[reassoc (attr := simp)]
theorem boundaryMap_comp_subschemeι :
    (h.boundaryMap hΦ hΨ) ≫ (Ψ.boundaryIdeal hΨ).subschemeι =
      (Φ.boundaryIdeal hΦ).subschemeι ≫ h.toFanHom.algebraicMap :=
  subschemeMap_subschemeι _ _ _ _

end Boundary

section RayPoints

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} (h : Φ.IsSubdivision Ψ)

/-- Under subdivision the generic point of an old ray maps to the original generic point. -/
theorem algebraicMap_rayBoundaryPoint_liftRay (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (ρ : Ψ.Ray) :
    h.toFanHom.algebraicMap (Φ.rayBoundaryPoint hΦ (h.liftRay ρ)).val =
      (Ψ.rayBoundaryPoint hΨ ρ).val := by
  have hchart : Φ.affineToricChartι (h.liftRay ρ).toCone ≫ h.toFanHom.algebraicMap =
      Ψ.affineToricChartι ρ.toCone :=
    h.affineToricChartι_comp_algebraicMap (h.ray_mem ρ) ρ.toCone.property
  rw [Fan.coe_rayBoundaryPoint, ← Scheme.Hom.comp_apply, hchart, Fan.coe_rayBoundaryPoint,
    h.liftRay_toToricRay]
  rfl

/-- When a subdivision is identified with a blowup, the strict transform of an old
ray divisor whose generic point lies outside the center is the lifted ray divisor. -/
theorem comap_ker_blowupMap_rayBoundaryIdeal (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    {I : Ψ.algebraicRealization.IdealSheafData} (e : Φ.algebraicRealization ≅ I.blowup)
    (he : e.hom ≫ I.blowupToBase = h.toFanHom.algebraicMap) (ρ : Ψ.Ray)
    (hρ : (Ψ.rayBoundaryPoint hΨ ρ).val ∉ (I.support : Set Ψ.algebraicRealization)) :
    (I.blowupMap (Ψ.rayBoundaryIdeal hΨ ρ).subschemeι).ker.comap e.hom =
      Φ.rayBoundaryIdeal hΦ (h.liftRay ρ) := by
  let x := (Φ.rayBoundaryPoint hΦ (h.liftRay ρ)).val
  have hx : I.blowupToBase (e.hom x) = (Ψ.rayBoundaryPoint hΨ ρ).val := by
    rw [← Scheme.Hom.comp_apply, he]
    exact h.algebraicMap_rayBoundaryPoint_liftRay hΦ hΨ ρ
  have houtside : e.hom x ∉ ((I.comap I.blowupToBase).support : Set I.blowup) := by
    rwa [support_comap, Closeds.coe_preimage, Set.mem_preimage, hx]
  rw [Ψ.rayBoundaryIdeal_def, ← hx, I.ker_blowupMap_vanishingIdeal_closure_singleton _ houtside,
    comap_vanishingIdeal_closure_singleton_apply, Φ.rayBoundaryIdeal_def]

/-- Subdivision preserves the order of every rational function along each old boundary ray. -/
theorem ord_functionFieldMap_liftRay [Nonempty Φ.cones] [Nonempty Ψ.cones]
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (ρ : Ψ.Ray)
    (g : Ψ.algebraicRealization.functionField) :
    Φ.algebraicRealization.ord (h.toFanHom.algebraicMap.functionFieldMap g)
        (Φ.rayBoundaryPoint hΦ (h.liftRay ρ)).val =
      Ψ.algebraicRealization.ord g (Ψ.rayBoundaryPoint hΨ ρ).val := by
  let j := Φ.affineToricChartι (h.liftRay ρ).toCone
  let k : Φ.affineToricChart (h.liftRay ρ).toCone ⟶ Ψ.algebraicRealization :=
    Ψ.affineToricChartι ρ.toCone
  have : IsOpenImmersion k := inferInstanceAs (IsOpenImmersion (Ψ.affineToricChartι ρ.toCone))
  let x : AlgebraicGeometry.CodimensionOnePoint (Φ.affineToricChart (h.liftRay ρ).toCone) :=
    (isRegular_iff.1 hΦ _ (h.ray_mem ρ)).rayPoint Φ.lattice
      (Φ.isToricCone (h.ray_mem ρ)) ((h.liftRay ρ).toToricRay Φ (h.liftRay ρ).toCone le_rfl)
  have hchart : j ≫ h.toFanHom.algebraicMap = k :=
    h.affineToricChartι_comp_algebraicMap (h.ray_mem ρ) ρ.toCone.property
  have hx : j x.val = (Φ.rayBoundaryPoint hΦ (h.liftRay ρ)).val :=
    (Fan.coe_rayBoundaryPoint _ _ _).symm
  have hy : k x.val = (Ψ.rayBoundaryPoint hΨ ρ).val := by
    calc
      k x.val = h.toFanHom.algebraicMap (j x.val) :=
        (congrArg (fun f ↦ f x.val) hchart.symm).trans (Scheme.Hom.comp_apply _ _ _)
      _ = _ := by rw [hx, h.algebraicMap_rayBoundaryPoint_liftRay hΦ hΨ]
  have : Nonempty (Φ.affineToricChart (h.liftRay ρ).toCone) := ⟨x.val⟩
  have : IsIntegral (Φ.affineToricChart (h.liftRay ρ).toCone) := isIntegral_of_isOpenImmersion j
  have : IsLocallyNoetherian (Φ.affineToricChart (h.liftRay ρ).toCone) :=
    isLocallyNoetherian_of_isOpenImmersion j
  rw [← hx, ← hy, ← TauCeti.AlgebraicGeometry.Scheme.ord_functionFieldMap j _ x.val,
    ← TauCeti.AlgebraicGeometry.Scheme.ord_functionFieldMap k _ x.val]
  exact congrArg (fun a ↦ (Φ.affineToricChart (h.liftRay ρ).toCone).ord a x.val)
    (ConcreteCategory.congr_hom ((Scheme.Hom.functionFieldMap_comp j _).symm.trans
      (Scheme.Hom.functionFieldMap_congr hchart)) g)

end RayPoints

section Centers

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} (h : Φ.IsSubdivision Ψ)

variable (ρ : Ψ.Ray) {m : N →+ ℤ} (hdim : Module.finrank ℤ N = 2)
  (hm : m ρ.primitiveGenerator = 0) (hp : Function.Surjective m) (c : ℂˣ)

local notation "s" => ρ.binomialCenter hdim hm hp c
local notation "s'" =>
  Ray.binomialCenter (liftRay h ρ) hdim (m := m)
    (Eq.trans (congrArg m (primitiveGenerator_liftRay h ρ)) hm) hp c

private theorem binomialCenterEval_liftRay :
    (h.liftRay ρ).binomialCenterEval hdim ((congrArg m (h.primitiveGenerator_liftRay ρ)).trans hm)
      hp c = ρ.binomialCenterEval hdim hm hp c := by
  let a := (h.liftRay ρ).binomialCenterEval hdim
    ((congrArg m (h.primitiveGenerator_liftRay ρ)).trans hm) hp c
  let b := ρ.binomialCenterEval hdim hm hp c
  have hker : RingHom.ker a = RingHom.ker b := by
    dsimp only [a, b]
    rw [Ray.ker_binomialCenterEval, Ray.ker_binomialCenterEval]
    have hχ : (h.liftRay ρ).chartCharacter
        ((congrArg m (h.primitiveGenerator_liftRay ρ)).trans hm) = ρ.chartCharacter hm :=
      Subtype.ext (by simp only [Ray.coe_chartCharacter])
    rw [h.liftRay_toToricRay, hχ]
    rfl
  let r := Algebra.ofId ℂ (_root_.IsLocalRing.ResidueField ℂ)
  have he : r.comp a = r.comp b := by
    apply TauCeti.IsLocalRing.algHom_residueField_eq_of_ker_eq
    exact (RingHom.ker_comp_of_injective a.toRingHom r.toRingHom.injective).trans
      (hker.trans (RingHom.ker_comp_of_injective b.toRingHom r.toRingHom.injective).symm)
  exact AlgHom.ext fun x ↦ r.toRingHom.injective (congrArg (fun e ↦ e x) he)

/-- The subdivision morphism agrees on old ray centers with the identification of their charts. -/
@[reassoc (attr := simp)]
theorem binomialCenter_comp_algebraicMap :
    s' ≫ h.toFanHom.algebraicMap = s := by
  have hchart : Φ.affineToricChartι (h.liftRay ρ).toCone ≫ h.toFanHom.algebraicMap =
      Ψ.affineToricChartι ρ.toCone :=
    h.affineToricChartι_comp_algebraicMap (h.ray_mem ρ) ρ.toCone.property
  rw [Ray.binomialCenter_def, Category.assoc, hchart, Ray.binomialCenter_def,
    h.binomialCenterEval_liftRay ρ hdim hm hp c]
  rfl

/-- Each binomial center on the old boundary belongs to the isomorphism locus. -/
theorem range_binomialCenter_subset_isoLocus :
    Set.range s ⊆ h.toFanHom.algebraicMap.isoLocus := by
  rw [Ray.binomialCenter_def, Scheme.Hom.comp_base, TopCat.coe_comp]
  exact (Set.range_comp_subset_range _ _).trans
    (h.range_affineToricChartι_subset_isoLocus (h.ray_mem ρ) ρ.toCone.property)

/-- The binomial section in the subdividing fan is the scheme-theoretic inverse image of
the original section. -/
theorem isPullback_binomialCenter :
    IsPullback s' (𝟙 _) h.toFanHom.algebraicMap s :=
  h.toFanHom.algebraicMap.isPullback_of_isIso_of_range_subset_isoLocus _ _ _
    (by simpa only [Category.id_comp] using h.binomialCenter_comp_algebraicMap ρ hdim hm hp c)
    (h.range_binomialCenter_subset_isoLocus ρ hdim hm hp c)

/-- The comparison also identifies the centers as sections on the reduced boundaries. -/
@[reassoc (attr := simp)]
theorem binomialCenterOnBoundary_comp_boundaryMap :
    Ray.binomialCenterOnBoundary (h.liftRay ρ) hdim (m := m)
        ((congrArg m (h.primitiveGenerator_liftRay ρ)).trans hm) hp c ≫
      h.boundaryMap ⟨(h.liftRay ρ).toCone⟩ ⟨ρ.toCone⟩ =
        ρ.binomialCenterOnBoundary hdim hm hp c := by
  apply (cancel_mono (Ψ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι).mp
  rw [Category.assoc, boundaryMap_comp_subschemeι, ← Category.assoc,
    Ray.binomialCenterOnBoundary_comp_subschemeι, Ray.binomialCenterOnBoundary_comp_subschemeι]
  exact h.binomialCenter_comp_algebraicMap ρ hdim hm hp c

end Centers

/-- When a subdivision lifts a ray, its binomial center expressed in the determinant
character of a fixed lattice basis projects to the binomial center with the original
parameter in that basis. -/
theorem binomialCenter_liftRay_comp_algebraicMap
    {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
    {i : N →+ V} {Φ Ψ : Fan i} (h : Φ.IsSubdivision Ψ) (ρ : Ψ.Ray)
    (b : Module.Basis (Fin 2) ℤ N) (c : ℂˣ) :
    let τ := h.liftRay ρ
    let hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
    τ.binomialCenter hdim (b.detDualEquiv_self τ.primitiveGenerator)
        (τ.surjective_detCharacter b) c ≫ h.toFanHom.algebraicMap =
      ρ.binomialCenter hdim (b.detDualEquiv_self ρ.primitiveGenerator)
        (ρ.surjective_detCharacter b) c := by
  intro τ hdim
  let χ := (b.detDualEquiv ρ.primitiveGenerator).toAddMonoidHom
  -- Transport the vanishing and surjectivity proofs together with the orbit character.
  have lift (m : N →+ ℤ) (hm : m = χ) (hz : m τ.primitiveGenerator = 0)
      (hs : Function.Surjective m) :
      τ.binomialCenter hdim hz hs c ≫ h.toFanHom.algebraicMap =
        ρ.binomialCenter hdim (b.detDualEquiv_self ρ.primitiveGenerator)
          (ρ.surjective_detCharacter b) c := by
    subst m
    exact h.binomialCenter_comp_algebraicMap ρ hdim
      (b.detDualEquiv_self ρ.primitiveGenerator) (ρ.surjective_detCharacter b) c
  exact lift _ (congrArg (fun z ↦ (b.detDualEquiv z).toAddMonoidHom)
    (h.primitiveGenerator_liftRay ρ)) _ _

section SharedRay

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ F : Fan i}

local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "π[" H "]" => FanHom.algebraicMap (Fan.IsSubdivision.toFanHom H)
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "pt" => IsLocalRing.closedPoint ℂ
local notation "dim(" b ")" =>
  Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "p[" b "," ρ "," c "]" =>
  Fan.Ray.binomialCenter ρ dim(b)
    (Module.Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
    (Fan.Ray.surjective_detCharacter ρ b) c

/-- Binomial centers on a shared ray of two subdivisions lift to the same point of the
common refinement after expressing the parameter in the target basis. Both centers lie
in the isomorphism loci of the respective subdivision maps. -/
theorem exists_binomialCenter_lift_of_shared_ray
    (s : F.IsSubdivision Φ) (t : F.IsSubdivision Ψ)
    (ρ : Φ.Ray) (ρ' : Ψ.Ray) (hρ : ρ.primitiveGenerator = ρ'.primitiveGenerator)
    (b d : Module.Basis (Fin 2) ℤ N) (c : ℂˣ) :
    ∃ (c' : ℂˣ) (z : X[F]),
      π[s] z = p[b,ρ,c] pt ∧ π[t] z = p[d,ρ',c'] pt ∧
      p[b,ρ,c] pt ∈ (π[s]).isoLocus ∧ p[d,ρ',c'] pt ∈ (π[t]).isoLocus := by
  have hl : s.liftRay ρ = t.liftRay ρ' := Fan.Ray.primitiveGenerator_injective (by
    rw [s.primitiveGenerator_liftRay, t.primitiveGenerator_liftRay, hρ])
  obtain ⟨c', hc'⟩ := ρ'.exists_binomialCenter_eq_of_basis d b c
  let z := p[b,s.liftRay ρ,c] pt
  have hs := s.binomialCenter_liftRay_comp_algebraicMap ρ b c
  have ht := t.binomialCenter_liftRay_comp_algebraicMap ρ' b c
  dsimp only at hs ht
  have hsrc : π[s] z = p[b,ρ,c] pt := congrArg (fun a : S ⟶ X[Φ] ↦ a pt) hs
  have htgt : π[t] z = p[d,ρ',c'] pt := by
    rw [hc']
    exact congrArg (fun a : S ⟶ X[Ψ] ↦ a pt) (hl ▸ ht)
  refine ⟨c', z, hsrc, htgt, ?_, ?_⟩
  · exact s.range_binomialCenter_subset_isoLocus ρ dim(b) (b.detDualEquiv_self _)
      (ρ.surjective_detCharacter b) c (Set.mem_range_self pt)
  · exact t.range_binomialCenter_subset_isoLocus ρ' dim(d) (d.detDualEquiv_self _)
      (ρ'.surjective_detCharacter d) c' (Set.mem_range_self pt)

end SharedRay

end TauCeti.Toric.Fan.IsSubdivision

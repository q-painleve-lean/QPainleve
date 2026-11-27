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
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import QPainleve.AlgebraicGeometry.Morphisms.Pullback.IsoLocus
import QPainleve.AlgebraicGeometry.Scheme.FunctionField
import QPainleve.Geometry.Toric.BaseChange.FiniteType
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
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
open TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.IsSubdivision

universe u

variable (k : Type u) [Field k]

section Boundary

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} (h : Φ.IsSubdivision Ψ)
  (hΦ : Nonempty Φ.cones) (hΨ : Nonempty Ψ.cones)

/-- An isomorphism over a subdivision morphism identifies the reduced inverse image
of the original boundary with the boundary of the subdivision. -/
theorem radical_comap_toricBoundaryIdeal_of_iso {Y : Scheme.{u}}
    (f : Y ⟶ (Ψ.finiteFanScheme k)) (e : (Φ.finiteFanScheme k) ≅ Y)
    (he : e.hom ≫ f = (h.toFanHom.finiteFanSchemeHom k)) :
    (((Ψ.toricBoundaryIdeal k hΨ).comap f).radical).comap e.hom = Φ.toricBoundaryIdeal k hΦ := by
  rw [← radical_comap_of_isOpenImmersion, ← comap_comp, he,
    h.radical_comap_toricBoundaryIdeal k hΦ hΨ]

/-- The subdivision morphism restricted to the reduced toric boundaries. -/
noncomputable def boundaryMap :
    (Φ.toricBoundaryIdeal k hΦ).subscheme ⟶ (Ψ.toricBoundaryIdeal k hΨ).subscheme :=
  subschemeMap _ _ (h.toFanHom.finiteFanSchemeHom k) (le_map_iff_comap_le.mpr
    ((le_radical _).trans_eq (h.radical_comap_toricBoundaryIdeal k hΦ hΨ)))

/-- The boundary map commutes with the ambient toric morphism. -/
@[reassoc (attr := simp)]
theorem boundaryMap_comp_subschemeι :
    (h.boundaryMap k hΦ hΨ) ≫ (Ψ.toricBoundaryIdeal k hΨ).subschemeι =
      (Φ.toricBoundaryIdeal k hΦ).subschemeι ≫ (h.toFanHom.finiteFanSchemeHom k) :=
  subschemeMap_subschemeι _ _ _ _

end Boundary

section Over

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} (h : Φ.IsSubdivision Ψ)
  (hΦ : Nonempty Φ.cones) (hΨ : Nonempty Ψ.cones)

/-- A toric subdivision restricts to a morphism of boundaries over the ground field. -/
instance isOver_boundaryMap : (h.boundaryMap k hΦ hΨ).IsOver (Spec (.of k)) := ⟨by
  rw [over_eq_subschemeι_comp, ← Category.assoc, boundaryMap_comp_subschemeι,
    Category.assoc, Ψ.finiteFanScheme_over k,
    FanHom.finiteFanSchemeHom_comp_finiteFanSchemeToSpec k,
    ← Φ.finiteFanScheme_over k, ← over_eq_subschemeι_comp]⟩

end Over

section RayPoints

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} (h : Φ.IsSubdivision Ψ)

/-- Subdivision preserves the order of every rational function along each old boundary ray. -/
theorem ord_functionFieldMap_liftRay [Nonempty Φ.cones] [Nonempty Ψ.cones]
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (ρ : Ψ.Ray)
    (g : (Ψ.finiteFanScheme k).functionField) :
    (Φ.finiteFanScheme k).ord ((h.toFanHom.finiteFanSchemeHom k).functionFieldMap g)
        (Φ.rayBoundaryChartPoint (R := k) hΦ (h.liftRay ρ)).val =
      (Ψ.finiteFanScheme k).ord g (Ψ.rayBoundaryChartPoint (R := k) hΨ ρ).val := by
  let j := Φ.affineChartι k (h.liftRay ρ).toCone
  let j' : affineChart k Φ.lattice (h.liftRay ρ).toCone.val ⟶ (Ψ.finiteFanScheme k) :=
    Ψ.affineChartι k ρ.toCone
  have : IsOpenImmersion j' := inferInstanceAs (IsOpenImmersion (Ψ.affineChartι k ρ.toCone))
  let X := affineChart k Φ.lattice (h.liftRay ρ).toCone.val
  let x : AlgebraicGeometry.CodimensionOnePoint X :=
    (isRegular_iff.1 hΦ _ (h.ray_mem ρ)).rayChartPoint Φ.lattice
      (Φ.isToricCone (h.ray_mem ρ)) ((h.liftRay ρ).toToricRay Φ (h.liftRay ρ).toCone le_rfl) k
  have hchart : j ≫ (h.toFanHom.finiteFanSchemeHom k) = j' :=
    h.affineChartι_comp_finiteFanSchemeHom k (h.ray_mem ρ) ρ.toCone.property
  have hx : j x.val = (Φ.rayBoundaryChartPoint (R := k) hΦ (h.liftRay ρ)).val :=
    (Fan.coe_rayBoundaryChartPoint (R := k) _ _ _).symm
  have hy : j' x.val = (Ψ.rayBoundaryChartPoint (R := k) hΨ ρ).val := by
    calc
      j' x.val = (h.toFanHom.finiteFanSchemeHom k) (j x.val) :=
        (congrArg (fun f ↦ f x.val) hchart.symm).trans (Scheme.Hom.comp_apply _ _ _)
      _ = _ := by rw [hx, h.finiteFanSchemeHom_rayBoundaryChartPoint_liftRay k hΦ hΨ]
  have : Nonempty X := ⟨x.val⟩
  have : IsIntegral X := isIntegral_of_isOpenImmersion j
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion j
  rw [← hx, ← hy, ← TauCeti.AlgebraicGeometry.Scheme.ord_functionFieldMap j _ x.val,
    ← TauCeti.AlgebraicGeometry.Scheme.ord_functionFieldMap j' _ x.val]
  exact congrArg (fun a ↦ (affineChart k Φ.lattice (h.liftRay ρ).toCone.val).ord a x.val)
    (ConcreteCategory.congr_hom ((Scheme.Hom.functionFieldMap_comp j _).symm.trans
      (Scheme.Hom.functionFieldMap_congr hchart)) g)

end RayPoints

section Centers

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} (h : Φ.IsSubdivision Ψ)

variable (ρ : Ψ.Ray) {m : N →+ ℤ} (hdim : Module.finrank ℤ N = 2)
  (hm : m ρ.primitiveGenerator = 0) (hp : Function.Surjective m) (c : kˣ)

local notation "s" => ρ.binomialCenter k hdim hm hp c
local notation "s'" =>
  Ray.binomialCenter (liftRay h ρ) k hdim (m := m)
    (Eq.trans (congrArg m (primitiveGenerator_liftRay h ρ)) hm) hp c

private theorem binomialCenterEval_liftRay :
    (h.liftRay ρ).binomialCenterEval k hdim ((congrArg m (h.primitiveGenerator_liftRay ρ)).trans hm)
      hp c = ρ.binomialCenterEval k hdim hm hp c := by
  let a := (h.liftRay ρ).binomialCenterEval k hdim
    ((congrArg m (h.primitiveGenerator_liftRay ρ)).trans hm) hp c
  let b := ρ.binomialCenterEval k hdim hm hp c
  have hker : RingHom.ker a = RingHom.ker b := by
    dsimp only [a, b]
    rw [Ray.ker_binomialCenterEval, Ray.ker_binomialCenterEval]
    have hχ : (h.liftRay ρ).chartCharacter
        ((congrArg m (h.primitiveGenerator_liftRay ρ)).trans hm) = ρ.chartCharacter hm :=
      Subtype.ext (by simp only [Ray.coe_chartCharacter])
    rw [h.liftRay_toToricRay, hχ]
    rfl
  let r := Algebra.ofId k (_root_.IsLocalRing.ResidueField k)
  have he : r.comp a = r.comp b := by
    apply TauCeti.IsLocalRing.algHom_residueField_eq_of_ker_eq
    exact (RingHom.ker_comp_of_injective a.toRingHom r.toRingHom.injective).trans
      (hker.trans (RingHom.ker_comp_of_injective b.toRingHom r.toRingHom.injective).symm)
  exact AlgHom.ext fun x ↦ r.toRingHom.injective (congrArg (fun e ↦ e x) he)

/-- The subdivision morphism agrees on old ray centers with the identification of their charts. -/
@[reassoc (attr := simp)]
theorem binomialCenter_comp_finiteFanSchemeHom :
    s' ≫ (h.toFanHom.finiteFanSchemeHom k) = s := by
  have hchart : Φ.affineChartι k (h.liftRay ρ).toCone ≫ (h.toFanHom.finiteFanSchemeHom k) =
      Ψ.affineChartι k ρ.toCone :=
    h.affineChartι_comp_finiteFanSchemeHom k (h.ray_mem ρ) ρ.toCone.property
  rw [Ray.binomialCenter_def, Category.assoc, hchart, Ray.binomialCenter_def,
    h.binomialCenterEval_liftRay k ρ hdim hm hp c]
  rfl

/-- Each binomial center on the old boundary belongs to the isomorphism locus. -/
theorem range_binomialCenter_subset_isoLocus :
    Set.range s ⊆ (h.toFanHom.finiteFanSchemeHom k).isoLocus := by
  rw [Ray.binomialCenter_def, Scheme.Hom.comp_base, TopCat.coe_comp]
  exact (Set.range_comp_subset_range _ _).trans
    (h.range_affineChartι_subset_isoLocus k (h.ray_mem ρ) ρ.toCone.property)

/-- The binomial section in the subdividing fan is the scheme-theoretic inverse image of
the original section. -/
theorem isPullback_binomialCenter :
    IsPullback s' (𝟙 _) (h.toFanHom.finiteFanSchemeHom k) s :=
  (h.toFanHom.finiteFanSchemeHom k).isPullback_of_isIso_of_range_subset_isoLocus _ _ _
    (by simpa only [Category.id_comp] using
      h.binomialCenter_comp_finiteFanSchemeHom k ρ hdim hm hp c)
    (h.range_binomialCenter_subset_isoLocus k ρ hdim hm hp c)

/-- The comparison also identifies the centers as sections on the reduced boundaries. -/
@[reassoc (attr := simp)]
theorem binomialCenterOnBoundary_comp_boundaryMap :
    Ray.binomialCenterOnBoundary (h.liftRay ρ) k hdim (m := m)
        ((congrArg m (h.primitiveGenerator_liftRay ρ)).trans hm) hp c ≫
      h.boundaryMap k ⟨(h.liftRay ρ).toCone⟩ ⟨ρ.toCone⟩ =
        ρ.binomialCenterOnBoundary k hdim hm hp c := by
  apply (cancel_mono (Ψ.toricBoundaryIdeal k ⟨ρ.toCone⟩).subschemeι).mp
  rw [Category.assoc, boundaryMap_comp_subschemeι, ← Category.assoc,
    Ray.binomialCenterOnBoundary_comp_subschemeι, Ray.binomialCenterOnBoundary_comp_subschemeι]
  exact h.binomialCenter_comp_finiteFanSchemeHom k ρ hdim hm hp c

end Centers

/-- When a subdivision lifts a ray, its binomial center expressed in the determinant
character of a fixed lattice basis projects to the binomial center with the original
parameter in that basis. -/
theorem binomialCenter_liftRay_comp_finiteFanSchemeHom
    {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
    {i : N →+ V} {Φ Ψ : Fan i} (h : Φ.IsSubdivision Ψ) (ρ : Ψ.Ray)
    (b : Module.Basis (Fin 2) ℤ N) (c : kˣ) :
    let τ := h.liftRay ρ
    let hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
    τ.binomialCenter k hdim (b.detDualEquiv_self τ.primitiveGenerator)
        (τ.surjective_detCharacter b) c ≫ (h.toFanHom.finiteFanSchemeHom k) =
      ρ.binomialCenter k hdim (b.detDualEquiv_self ρ.primitiveGenerator)
        (ρ.surjective_detCharacter b) c := by
  intro τ hdim
  let χ := (b.detDualEquiv ρ.primitiveGenerator).toAddMonoidHom
  -- Transport the vanishing and surjectivity proofs together with the orbit character.
  have lift (m : N →+ ℤ) (hm : m = χ) (hz : m τ.primitiveGenerator = 0)
      (hs : Function.Surjective m) :
      τ.binomialCenter k hdim hz hs c ≫ (h.toFanHom.finiteFanSchemeHom k) =
        ρ.binomialCenter k hdim (b.detDualEquiv_self ρ.primitiveGenerator)
          (ρ.surjective_detCharacter b) c := by
    subst m
    exact h.binomialCenter_comp_finiteFanSchemeHom k ρ hdim
      (b.detDualEquiv_self ρ.primitiveGenerator) (ρ.surjective_detCharacter b) c
  exact lift _ (congrArg (fun z ↦ (b.detDualEquiv z).toAddMonoidHom)
    (h.primitiveGenerator_liftRay ρ)) _ _

/-- Pullback to the refined boundary preserves each binomial center ideal on a lifted ray. -/
theorem comap_internalCenter {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
    {i : N →+ V} {Φ Ψ : Fan i} [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones]
    (h : Ψ.IsSubdivision Φ) (b : Module.Basis (Fin 2) ℤ N) (ρ : Φ.Ray) (c : kˣ) :
    (ρ.internalCenter k b c).val.comap (h.boundaryMap k hΨ₀ hΦ₀) =
      ((h.liftRay ρ).internalCenter k b c).val := by
  have hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let τ := h.liftRay ρ
  let μ := (b.detDualEquiv ρ.primitiveGenerator).toAddMonoidHom
  have hμ : (b.detDualEquiv τ.primitiveGenerator).toAddMonoidHom = μ :=
    congrArg (fun v ↦ (b.detDualEquiv v).toAddMonoidHom) (h.primitiveGenerator_liftRay ρ)
  let p := ρ.binomialCenterOnBoundary k hdim (m := μ) (b.detDualEquiv_self _)
    (ρ.surjective_detCharacter b) c
  let q := τ.binomialCenterOnBoundary k hdim (m := μ)
    ((congrArg μ (h.primitiveGenerator_liftRay ρ)).trans (b.detDualEquiv_self _))
    (ρ.surjective_detCharacter b) c
  have : IsClosedImmersion (ρ.binomialCenter k hdim (m := μ) (b.detDualEquiv_self _)
      (ρ.surjective_detCharacter b) c) :=
    ρ.isClosedImmersion_binomialCenter k hdim (b.detDualEquiv_self _)
      (ρ.surjective_detCharacter b) c
  have hpcomp : p ≫ (Φ.toricBoundaryIdeal k hΦ₀).subschemeι =
      ρ.binomialCenter k hdim (m := μ) (b.detDualEquiv_self _)
        (ρ.surjective_detCharacter b) c :=
    ρ.binomialCenterOnBoundary_comp_subschemeι k hdim (b.detDualEquiv_self _)
      (ρ.surjective_detCharacter b) c
  have hqcomp : q ≫ (Ψ.toricBoundaryIdeal k hΨ₀).subschemeι =
      τ.binomialCenter k hdim (m := μ)
        ((congrArg μ (h.primitiveGenerator_liftRay ρ)).trans (b.detDualEquiv_self _))
        (ρ.surjective_detCharacter b) c :=
    τ.binomialCenterOnBoundary_comp_subschemeι k hdim _ _ c
  have hp : (p ≫ (Φ.toricBoundaryIdeal k hΦ₀).subschemeι).ker.comap
      (h.toFanHom.finiteFanSchemeHom k) = (q ≫ (Ψ.toricBoundaryIdeal k hΨ₀).subschemeι).ker := by
    rw [hpcomp, hqcomp]
    exact (ker_eq_comap_of_isPullback _
      (h.isPullback_binomialCenter k ρ hdim (m := μ) (b.detDualEquiv_self _)
        (ρ.surjective_detCharacter b) c)).symm
  have hker : p.ker.comap (h.boundaryMap k hΨ₀ hΦ₀) = q.ker := by
    rw [← p.comap_ker_comp_of_isClosedImmersion (Φ.toricBoundaryIdeal k hΦ₀).subschemeι,
      ← comap_comp, h.boundaryMap_comp_subschemeι k, comap_comp, hp,
      q.comap_ker_comp_of_isClosedImmersion]
  rw [Ray.internalCenter_val, Ray.internalCenter_val]
  -- Transport the orbit character together with the proofs of vanishing and surjectivity.
  have hq' (m : N →+ ℤ) (hm : m = μ) (hz : m τ.primitiveGenerator = 0)
      (hs : Function.Surjective m) :
      (τ.binomialCenterOnBoundary k hdim hz hs c).ker = q.ker := by
    subst m
    rfl
  exact hker.trans (hq' _ hμ _ _).symm

section CenterTransport

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ F : Fan i}

local notation "X[" Δ "]" => Fan.finiteFanScheme k Δ
local notation "π[" H "]" => FanHom.finiteFanSchemeHom k (Fan.IsSubdivision.toFanHom H)
local notation "S" => Spec (CommRingCat.of k)
local notation "pt" => IsLocalRing.closedPoint k
local notation "dim(" b ")" =>
  Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "p[" b "," ρ "," c "]" =>
  Fan.Ray.binomialCenter ρ k dim(b)
    (Module.Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
    (Fan.Ray.surjective_detCharacter ρ b) c

/-- A lift of a binomial center to a common refinement projects to the distinguished
point on the other fan if the second subdivision contracts the lifted ray to that point. -/
theorem finiteFanSchemeHom_eq_distinguishedSection_of_binomialCenter
    (s : F.IsSubdivision Φ) (t : F.IsSubdivision Ψ) [Nonempty F.cones]
    (b : Module.Basis (Fin 2) ℤ N) (hF : F.IsRegular) (τ : Ψ.cones) (ρ : Φ.Ray)
    (hcontract : (Ψ.distinguishedSection (R := k) τ).ker.comap π[t] =
      F.rayDivisorIdeal k hF (s.liftRay ρ))
    (c : kˣ) {z : X[F]} (hz : π[s] z = p[b,ρ,c] pt) :
    π[t] z = Ψ.distinguishedSection (R := k) τ pt := by
  let q := p[b,s.liftRay ρ,c] pt
  have hq : π[s] q = p[b,ρ,c] pt := congrArg (fun f : S ⟶ X[Φ] ↦ f pt)
    (s.binomialCenter_liftRay_comp_finiteFanSchemeHom k ρ b c)
  have hi : p[b,ρ,c] pt ∈ (π[s]).isoLocus :=
    s.range_binomialCenter_subset_isoLocus k ρ dim(b) (b.detDualEquiv_self _)
      (ρ.surjective_detCharacter b) c (Set.mem_range_self pt)
  have hqz : q = z := (π[s]).injOn_preimage_isoLocus (by rwa [Set.mem_preimage, hq])
    (by rwa [Set.mem_preimage, hz]) (hq.trans hz.symm)
  have hs := ((s.liftRay ρ).binomialCenter_mem_support_sdiff_colon k hF dim(b)
    (b.detDualEquiv_self _) ((s.liftRay ρ).surjective_detCharacter b) c).1
  let : IsClosedImmersion (Ψ.distinguishedSection (R := k) τ) :=
    Ψ.isClosedImmersion_distinguishedSection (R := k) τ
  rw [← hcontract, support_comap, Closeds.coe_preimage, Set.mem_preimage,
    Scheme.Hom.support_ker,
    (Ψ.distinguishedSection (R := k) τ).isClosedEmbedding.isClosed_range.closure_eq]
    at hs
  obtain ⟨x, hx⟩ := hs
  rw [← hqz, ← hx, Subsingleton.elim pt x]

/-- Binomial centers on a shared ray of two subdivisions lift to the same point of the
common refinement after expressing the parameter in the target basis. Both centers lie
in the isomorphism loci of the respective subdivision maps. -/
theorem exists_binomialCenter_lift_of_shared_ray
    (s : F.IsSubdivision Φ) (t : F.IsSubdivision Ψ)
    (ρ : Φ.Ray) (ρ' : Ψ.Ray) (hρ : ρ.primitiveGenerator = ρ'.primitiveGenerator)
    (b d : Module.Basis (Fin 2) ℤ N) (c : kˣ) :
    ∃ (c' : kˣ) (z : X[F]),
      π[s] z = p[b,ρ,c] pt ∧ π[t] z = p[d,ρ',c'] pt ∧
      p[b,ρ,c] pt ∈ (π[s]).isoLocus ∧ p[d,ρ',c'] pt ∈ (π[t]).isoLocus := by
  have hl : s.liftRay ρ = t.liftRay ρ' := Fan.Ray.primitiveGenerator_injective (by
    rw [s.primitiveGenerator_liftRay, t.primitiveGenerator_liftRay, hρ])
  obtain ⟨c', hc'⟩ := ρ'.exists_binomialCenter_eq_of_basis k d b c
  let z := p[b,s.liftRay ρ,c] pt
  have hs := s.binomialCenter_liftRay_comp_finiteFanSchemeHom k ρ b c
  have ht := t.binomialCenter_liftRay_comp_finiteFanSchemeHom k ρ' b c
  dsimp only at hs ht
  have hsrc : π[s] z = p[b,ρ,c] pt := congrArg (fun a : S ⟶ X[Φ] ↦ a pt) hs
  have htgt : π[t] z = p[d,ρ',c'] pt := by
    rw [hc']
    exact congrArg (fun a : S ⟶ X[Ψ] ↦ a pt) (hl ▸ ht)
  refine ⟨c', z, hsrc, htgt, ?_, ?_⟩
  · exact s.range_binomialCenter_subset_isoLocus k ρ dim(b) (b.detDualEquiv_self _)
      (ρ.surjective_detCharacter b) c (Set.mem_range_self pt)
  · exact t.range_binomialCenter_subset_isoLocus k ρ' dim(d) (d.detDualEquiv_self _)
      (ρ'.surjective_detCharacter d) c' (Set.mem_range_self pt)

end CenterTransport

end TauCeti.Toric.Fan.IsSubdivision

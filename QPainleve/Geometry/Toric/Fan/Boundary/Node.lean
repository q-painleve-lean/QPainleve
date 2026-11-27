/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Locus
public import QPainleve.Geometry.Toric.BaseChange.Boundary
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.RingTheory.Node.Branches

import QPainleve.AlgebraicGeometry.Curves.Node.Split
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Cone.TwoDimensional
import QPainleve.Geometry.Toric.BaseChange.Point
import QPainleve.Geometry.Toric.RegularChart
import QPainleve.Geometry.Toric.Fan.TwoDimensional
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Pullback.Carrier
import TauCeti.RingTheory.Node.Reduced

/-!
# Nodes in regular toric surface boundaries

On the affine chart of a two-dimensional regular cone, the two ray divisors
are the coordinate axes and the distinguished point is their common origin.
The reduced boundary at that point is therefore the split node
`Spec k[x,y]/(xy)`. The comparison uses the regular affine chart coordinates
and its split-node singular locus. For a complete rank-two fan, these charts
cover the reduced boundary and identify its nodes with the two-ray cones.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric

universe u

variable (k : Type u) [Field k] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

private theorem exists_twoRayChartCoordinates {C : PointedCone ℝ V}
    (hi : IsIntegralLattice i) (hC : IsRegularCone i C)
    (hN : Module.finrank ℤ N = 2) (hc : Nat.card (ToricRay C) = 2) :
    ∃ (r : Fin 2 ≃ ToricRay C) (e : affineChartRing k hi C ≃ₐ[k] MvPolynomial (Fin 2) k),
      (∀ j, rayChartIdeal hi hC.toIsToricCone (r j) k =
        Ideal.span {e.symm (MvPolynomial.X j)}) ∧
      (NodeAlgebra.origin k).comp ((NodeAlgebra.mk 0).comp e.toAlgHom) =
        facePointAlgebraHom hi (⊤ : C.Face) k := by
  classical
  obtain ⟨r, b, hb⟩ := hC.exists_basis_primitiveGenerators hi hN hc
  let b' := b.reindex (r.trans (Equiv.sumEmpty (ToricRay C) (Fin 0)).symm)
  have hb' (j : Fin 2) : b' (Sum.inl (r j)) = b j := by simp [b']
  have hprim (t : ToricRay C) : IsPrimitiveGenerator i t (b' (Sum.inl t)) := by
    obtain ⟨j, rfl⟩ := r.surjective t
    rw [hb', hb]
    exact isPrimitiveGenerator_primitiveGenerator hi hC.toIsToricCone _
  let e := (affineChartRingEquivMvPolynomial hi hC.toIsToricCone hprim k).trans
    ((MvPolynomial.mapAlgEquiv (ToricRay C) (AddMonoidAlgebra.uniqueAlgEquiv k (Fin 0 →₀ ℤ))).trans
      (MvPolynomial.renameEquiv k r.symm))
  have hX (j : Fin 2) : e.symm (MvPolynomial.X j) =
      AddMonoidAlgebra.single (dualSemigroupCoord hi hC.toIsToricCone hprim (Sum.inl (r j))) 1 := by
    apply e.injective
    rw [AlgEquiv.apply_symm_apply]
    dsimp only [e, AlgEquiv.trans_apply]
    rw [affineChartRingEquivMvPolynomial_rayCoord]
    simp
  refine ⟨r, e, fun j ↦ ?_, ?_⟩
  · rw [hX, rayChartIdeal_eq_span_rayCoordinate hi hC.toIsToricCone (r j) k hprim]
  · apply (AlgHom.cancel_right (f := e.symm.toAlgHom) e.symm.surjective).mp
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply,
      NodeAlgebra.mk_X, NodeAlgebra.origin_coord]
    rw [hX, facePointAlgebraHom_single]
    refine (ite_eq_right fun h ↦ ?_).symm
    have hz := h (i (b' (Sum.inl (r j)))) ((r j).val.isFaceOf.le (hprim (r j)).mem)
    rw [hi.realCharacter_apply] at hz
    rw [dualSemigroupCoord_apply_basis_self] at hz
    norm_num at hz

namespace Fan

variable {Φ : Fan i}

private theorem mem_boundaryIdeal_comap_chart_iff (hΦ : Φ.IsRegular) (σ : Φ.cones)
    (x : affineChart k Φ.lattice σ.val) :
    x ∈ ((Φ.toricBoundaryIdeal k ⟨σ⟩).comap (Φ.affineChartι k σ)).support ↔
      ∃ r : ToricRay σ.val, rayChartIdeal Φ.lattice (Φ.isToricCone σ.property) r k ≤ x.asIdeal := by
  have hcomap (ρ : Φ.Ray) :
      x ∈ ((Φ.rayDivisorIdeal k hΦ ρ).comap (Φ.affineChartι k σ)).support ↔
        Φ.affineChartι k σ x ∈ (Φ.rayDivisorIdeal k hΦ ρ).support := by
    rw [← SetLike.mem_coe, support_comap, Closeds.coe_preimage]
    rfl
  rw [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage,
    Φ.support_toricBoundaryIdeal_eq_iUnion_closure k hΦ, Set.mem_iUnion]
  simp only [← Φ.coe_support_rayDivisorIdeal k hΦ]
  have hlocal (r : ToricRay σ.val) :
      x ∈ ((Φ.rayDivisorIdeal k hΦ (Ray.ofToricRay Φ σ r)).comap
          (Φ.affineChartι k σ)).support ↔
        rayChartIdeal Φ.lattice (Φ.isToricCone σ.property) r k ≤ x.asIdeal := by
    have hle := Ray.toCone_ofToricRay_le Φ σ r
    rw [Φ.comap_rayDivisorIdeal_eq_ofIdealTop k hΦ _ σ hle,
      ← SetLike.mem_coe, coe_support_ofIdealTop, Spec_zeroLocus]
    let p : PrimeSpectrum (affineChartRing k Φ.lattice σ.val) := x
    -- Use the prime spectrum carrier explicitly to apply the affine zero-locus API.
    change p ∈ PrimeSpectrum.zeroLocus _ ↔ _ ≤ p.asIdeal
    rw [PrimeSpectrum.mem_zeroLocus, ← Ideal.coe_comap,
      Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso (C := CommRingCat) _),
      SetLike.coe_subset_coe]
    simpa only [rayEquiv_apply, rayEquiv_symm_apply] using
      iff_of_eq (congrArg
        (fun t ↦ rayChartIdeal Φ.lattice (Φ.isToricCone σ.property) t k ≤ x.asIdeal)
        ((Φ.rayEquiv σ).apply_symm_apply r))
  constructor
  · rintro ⟨ρ, hρ⟩
    have hx := (hcomap ρ).mpr hρ
    by_cases hle : ρ.toCone ≤ σ
    · obtain ⟨r, hr⟩ := (Φ.rayEquiv σ).symm.surjective ⟨ρ, hle⟩
      have he : Ray.ofToricRay Φ σ r = ρ := by
        simpa only [rayEquiv_symm_apply] using congrArg Subtype.val hr
      exact ⟨r, (hlocal r).mp (he.symm ▸ hx)⟩
    · rw [Φ.comap_rayDivisorIdeal_eq_top k hΦ ρ σ hle, support_top] at hx
      exact hx.elim
  · rintro ⟨r, hr⟩
    exact ⟨Ray.ofToricRay Φ σ r, (hcomap _).mp ((hlocal r).mpr hr)⟩

private theorem ker_nodeChart {R : Type*} [CommRing R] [Algebra k R]
    (e : R ≃ₐ[k] MvPolynomial (Fin 2) k) :
    RingHom.ker ((NodeAlgebra.mk 0).comp e.toAlgHom).toRingHom =
      Ideal.span {e.symm (MvPolynomial.X 0) * e.symm (MvPolynomial.X 1)} := by
  refine (AlgHom.comap_ker (NodeAlgebra.mk (0 : k)) e.toAlgHom).symm.trans ?_
  have hker : RingHom.ker (NodeAlgebra.mk (0 : k) :
      MvPolynomial (Fin 2) k →+* NodeAlgebra k 0) =
      Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1} := by simp
  refine (congrArg (Ideal.comap (e.toAlgHom : R →+* MvPolynomial (Fin 2) k)) hker).trans ?_
  exact (Ideal.map_symm e.toRingEquiv).symm.trans (by simp [Ideal.map_span])

private theorem comap_boundaryIdeal_eq_ker_nodeChart (hΦ : Φ.IsRegular) (σ : Φ.cones)
    (r : Fin 2 ≃ ToricRay σ.val)
    (e : affineChartRing k Φ.lattice σ.val ≃ₐ[k] MvPolynomial (Fin 2) k)
    (hr : ∀ j, rayChartIdeal Φ.lattice (Φ.isToricCone σ.property) (r j) k =
      Ideal.span {e.symm (MvPolynomial.X j)}) :
    let a := (NodeAlgebra.mk 0).comp e.toAlgHom
    (Φ.toricBoundaryIdeal k ⟨σ⟩).comap (Φ.affineChartι k σ) =
      (Spec.map (CommRingCat.ofHom a.toRingHom)).ker := by
  intro a
  let j := Φ.affineChartι k σ
  let q : Spec (.of (NodeAlgebra k 0)) ⟶ affineChart k Φ.lattice σ.val :=
    Spec.map (CommRingCat.ofHom a.toRingHom)
  have hsurj : Function.Surjective a := (NodeAlgebra.mk_surjective 0).comp e.surjective
  have : IsClosedImmersion q := IsClosedImmersion.spec_of_surjective _ hsurj
  -- Work with the named quotient morphism so that its affine range formula applies below.
  change (Φ.toricBoundaryIdeal k ⟨σ⟩).comap j = q.ker
  have hD : ((Φ.toricBoundaryIdeal k ⟨σ⟩).comap j).radical =
      (Φ.toricBoundaryIdeal k ⟨σ⟩).comap j := by
    rw [radical_comap_of_isOpenImmersion]
    congr 1
    apply (isReduced_subscheme_iff_radical_eq _).mp
    infer_instance
  rw [q.ker_eq_vanishingIdeal_support, ← hD, ← vanishingIdeal_support]
  apply congrArg vanishingIdeal
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, mem_boundaryIdeal_comap_chart_iff k hΦ,
    ← SetLike.mem_coe, q.support_ker, q.isClosedEmbedding.isClosed_range.closure_eq]
  have hqrange : Set.range q = PrimeSpectrum.zeroLocus (RingHom.ker a.toRingHom : Set _) :=
    range_comap_of_surjective _ _ hsurj
  rw [hqrange]
  let p : PrimeSpectrum (affineChartRing k Φ.lattice σ.val) := x
  -- The chart is affine, so the range condition is ideal containment at its prime.
  change (∃ t : ToricRay σ.val, rayChartIdeal Φ.lattice (Φ.isToricCone σ.property) t k ≤
    p.asIdeal) ↔ p ∈ PrimeSpectrum.zeroLocus _
  rw [PrimeSpectrum.mem_zeroLocus, r.symm.exists_congr_left, Equiv.symm_symm,
    Fin.exists_fin_two, hr, hr]
  rw [ker_nodeChart k e]
  simp only [SetLike.coe_subset_coe, Ideal.span_singleton_le_iff_mem,
    p.isPrime.mul_mem_iff_mem_or_mem]

/-- The reduced boundary on the chart of a two-ray cone is the split node. The
comparison is a pullback of the ambient affine toric chart along the boundary inclusion. -/
theorem exists_isPullback_boundaryIdeal_splitNode (hΦ : Φ.IsRegular) (σ : Φ.cones)
    (hN : Module.finrank ℤ N = 2) (hc : Nat.card (ToricRay σ.val) = 2) :
    ∃ (q : Spec (.of (NodeAlgebra k 0)) ⟶ affineChart k Φ.lattice σ.val)
      (b : Spec (.of (NodeAlgebra k 0)) ⟶ (Φ.toricBoundaryIdeal k ⟨σ⟩).subscheme),
      IsPullback q b (Φ.affineChartι k σ) (Φ.toricBoundaryIdeal k ⟨σ⟩).subschemeι ∧
      b ≫ (Φ.toricBoundaryIdeal k ⟨σ⟩).subschemeι ≫ (Φ.finiteFanSchemeToSpec k) =
        Spec.map (CommRingCat.ofHom (algebraMap k (NodeAlgebra k 0))) ∧
      Spec.map (CommRingCat.ofHom (NodeAlgebra.origin k).toRingHom) ≫ q ≫
        Φ.affineChartι k σ = Φ.distinguishedSection (R := k) σ := by
  obtain ⟨r, e, hr, ho⟩ := exists_twoRayChartCoordinates k Φ.lattice
    ((isRegular_iff.mp hΦ) σ.val σ.property) hN hc
  let a := (NodeAlgebra.mk 0).comp e.toAlgHom
  let q : Spec (.of (NodeAlgebra k 0)) ⟶ affineChart k Φ.lattice σ.val :=
    Spec.map (CommRingCat.ofHom a.toRingHom)
  let j := Φ.affineChartι k σ
  let D := Φ.toricBoundaryIdeal k ⟨σ⟩
  have : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ ((NodeAlgebra.mk_surjective 0).comp e.surjective)
  have hker : D.comap j = q.ker := comap_boundaryIdeal_eq_ker_nodeChart k hΦ σ r e hr
  let b := IsClosedImmersion.lift D.subschemeι (q ≫ j) (by
    rw [ker_subschemeι, Scheme.Hom.ker_comp, ← hker]
    exact le_map_comap _ _)
  have hb : b ≫ D.subschemeι = q ≫ j := IsClosedImmersion.lift_fac _ _ _
  refine ⟨q, b, isPullback_of_isClosedImmersion q D.subschemeι b j hb.symm (by
    rwa [ker_subschemeι]), ?_, ?_⟩
  · rw [← Category.assoc, hb, Category.assoc,
      Φ.affineChartι_finiteFanSchemeToSpec k]
    dsimp only [q]
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact a.commutes c
  · rw [Φ.distinguishedSection_def (R := k), ← Category.assoc]
    dsimp only [q]
    rw [← Spec.map_comp]
    have ha : CommRingCat.ofHom a.toRingHom ≫ CommRingCat.ofHom (NodeAlgebra.origin k).toRingHom =
        CommRingCat.ofHom (facePointAlgebraHom Φ.lattice (⊤ : σ.val.Face) k).toRingHom := by
      rw [← CommRingCat.ofHom_comp]
      exact congrArg (fun g : affineChartRing k Φ.lattice σ.val →ₐ[k] k ↦
        CommRingCat.ofHom g.toRingHom) ho
    rw [ha]

/-- The distinguished point of a two-dimensional cone of a regular surface fan is a
node of the reduced toric boundary. This holds for noncomplete fans as well. -/
theorem isNodeOfReducedBoundary_distinguishedSection (hΦ : Φ.IsRegular) (σ : Φ.cones)
    (hN : Module.finrank ℤ N = 2) (hc : Nat.card (ToricRay σ.val) = 2) :
    (Φ.toricBoundaryIdeal k ⟨σ⟩).IsNodeOfReducedBoundary (Φ.finiteFanSchemeToSpec k)
      (Φ.distinguishedSection (R := k) σ (IsLocalRing.closedPoint k)) := by
  obtain ⟨q, b, hpb, hbase, ho⟩ := Φ.exists_isPullback_boundaryIdeal_splitNode k hΦ σ hN hc
  let D := Φ.toricBoundaryIdeal k ⟨σ⟩
  let x := Spec.map (CommRingCat.ofHom (NodeAlgebra.origin k).toRingHom)
    (IsLocalRing.closedPoint k)
  have : IsOpenImmersion b := MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    hpb inferInstance
  have : IsReduced D.subscheme := by
    dsimp only [D]
    infer_instance
  refine (D.isNodeOfReducedBoundary_iff_of_isReduced _ _).mpr ⟨b x, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← hpb.w]
    exact congrArg (fun a : Spec (.of k) ⟶ (Φ.finiteFanScheme k) ↦
      a (IsLocalRing.closedPoint k)) ho
  · apply (Scheme.Hom.isNodeAt_comp_iff_of_isOpenImmersion
      (D.subschemeι ≫ (Φ.finiteFanSchemeToSpec k)) b x).mp
    rw [hbase]
    exact (NodeAlgebra.isNodeAt_iff_mem_range_origin x).mpr ⟨IsLocalRing.closedPoint k, rfl⟩

private theorem exists_twoRayChart_apply_eq (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hdim : Module.finrank ℤ N = 2) (x : (Φ.finiteFanScheme k)) :
    ∃ (υ : Φ.cones) (_ : Nat.card (ToricRay υ.val) = 2)
      (y : affineChart k Φ.lattice υ.val), Φ.affineChartι k υ y = x := by
  obtain ⟨σ, y, hy⟩ := Φ.exists_affineChartι_apply_eq k x
  obtain ⟨υ, hσυ, hυ⟩ := exists_le_cone_of_card_toricRay_eq_two hΦ hc hdim σ
  let j := faceAffineChartMap k Φ.lattice (Φ.isFaceOf_of_le υ.property σ.property hσυ)
  refine ⟨υ, hυ, j y, ?_⟩
  rw [← Scheme.Hom.comp_apply, Φ.faceAffineChartMap_comp_affineChartι k]
  exact hy

private theorem mem_range_rayChart_of_not_mem_otherRayIdeal (σ : Φ.cones)
    (hΦ : Φ.IsRegular) (hc : Nat.card (ToricRay σ.val) = 2)
    {r t : ToricRay σ.val} (hrt : r ≠ t) (y : affineChart k Φ.lattice σ.val)
    (hy : ¬ rayChartIdeal Φ.lattice (Φ.isToricCone σ.property) t k ≤ y.asIdeal) :
    Φ.affineChartι k σ y ∈ Set.range (Φ.affineChartι k (Ray.ofToricRay Φ σ r).toCone) := by
  let hreg := isRegular_iff.mp hΦ σ.val σ.property
  let hσ := hreg.toIsToricCone
  obtain ⟨l, b, hb⟩ := hreg.exists_basis_sum
  let m := dualSemigroupCoord Φ.lattice hσ hb (Sum.inl t)
  let F : σ.val.Face := ⟨_, PointedCone.isFaceOf_inf_ker
    ((mem_dualSemigroup Φ.lattice m).mp m.property)⟩
  have : Finite (ToricRay σ.val) := ToricRay.finite_of_fg hσ.fg
  have hall (u : ToricRay σ.val) : u = r ∨ u = t := by
    have hpair : ({r, t} : Set (ToricRay σ.val)) = Set.univ :=
      (Set.eq_univ_iff_ncard _).mpr ((Set.ncard_pair hrt).trans hc.symm)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hpair.ge (Set.mem_univ u)
  have hface : F = r.val := by
    apply (hreg.faceOrderIso Φ.lattice).injective
    rw [hreg.faceOrderIso_toricRay Φ.lattice]
    ext u
    rw [hreg.mem_faceOrderIso_iff, Set.mem_singleton_iff]
    -- In the chosen dual coordinates the face consists of the generators where m vanishes.
    change (i (primitiveGenerator Φ.lattice hσ u) ∈ σ.val ∧
      i (primitiveGenerator Φ.lattice hσ u) ∈ LinearMap.ker (Φ.lattice.realCharacter m)) ↔ u = r
    rw [and_iff_right (u.val.isFaceOf.le (primitiveGenerator_mem Φ.lattice hσ u)),
      LinearMap.mem_ker, Φ.lattice.realCharacter_apply, Int.cast_eq_zero,
      ← (hb u).eq_primitiveGenerator Φ.lattice hσ]
    rcases hall u with rfl | rfl
    · simp [m, hrt]
    · simp [m, hrt.symm]
  have hy' : y ∈ Set.range (faceAffineChartMap k Φ.lattice F.isFaceOf) := by
    rw [range_faceAffineChartMap k Φ.lattice hσ.fg m]
    let p : PrimeSpectrum (affineChartRing k Φ.lattice σ.val) := y
    -- The spectrum's basic open is written on the affine chart's point carrier.
    change p ∈ PrimeSpectrum.basicOpen (AddMonoidAlgebra.single m 1)
    rw [PrimeSpectrum.mem_basicOpen]
    simpa only [rayChartIdeal_eq_span_rayCoordinate Φ.lattice hσ t k hb,
      Ideal.span_singleton_le_iff_mem, m] using hy
  rw [hface] at hy'
  let τ : Φ.cones := ⟨r.toPointedCone, Φ.mem_of_isFaceOf σ.property r.val.isFaceOf⟩
  have hτ : (Ray.ofToricRay Φ σ r).toCone = τ :=
    Subtype.ext (Ray.toCone_ofToricRay Φ σ r)
  rw [hτ]
  obtain ⟨z, hz⟩ := hy'
  refine ⟨z, ?_⟩
  rw [← hz, ← Scheme.Hom.comp_apply]
  exact (congrArg (fun f : affineChart k Φ.lattice τ.val ⟶ (Φ.finiteFanScheme k) ↦ f z)
    (Φ.faceAffineChartMap_comp_affineChartι k (τ := τ) (σ := σ) r.val.isFaceOf)).symm

/-- Every point of a complete regular toric surface outside the nodes of the reduced
boundary belongs to a ray chart. -/
theorem exists_rayChart_of_not_isNodeOfReducedBoundary
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (hdim : Module.finrank ℤ N = 2)
    {x : (Φ.finiteFanScheme k)}
    (hn : ¬ (Φ.toricBoundaryIdeal k hc.nonempty_cones).IsNodeOfReducedBoundary
      (Φ.finiteFanSchemeToSpec k) x) :
    ∃ ρ : Φ.Ray, x ∈ Set.range (Φ.affineChartι k ρ.toCone) := by
  obtain ⟨σ, hσ, y, rfl⟩ := exists_twoRayChart_apply_eq k hΦ hc hdim x
  classical
  have hnot : ¬ (⨆ t : ToricRay σ.val, rayChartIdeal Φ.lattice (Φ.isToricCone σ.property) t k) ≤
      y.asIdeal := by
    rw [iSup_rayChartIdeal_eq_ker_facePointAlgebraHom k Φ.lattice (Φ.isToricCone σ.property)
      (isRegular_iff.mp hΦ _ σ.property) (hσ.trans hdim.symm)]
    intro h
    let d := facePointAlgebraHom Φ.lattice (⊤ : σ.val.Face) k
    let g : Spec (.of k) ⟶ affineChart k Φ.lattice σ.val := Spec.map (CommRingCat.ofHom d.toRingHom)
    have hg : Set.range g = PrimeSpectrum.zeroLocus (RingHom.ker d.toRingHom : Set _) :=
      range_comap_of_surjective _ _ (fun a ↦ ⟨algebraMap k _ a, d.commutes a⟩)
    have hy' : y ∈ Set.range g := hg.symm ▸ (PrimeSpectrum.mem_zeroLocus y _).mpr h
    obtain ⟨z, rfl⟩ := hy'
    let o : Spec (.of k) := IsLocalRing.closedPoint k
    have hz : z = o := Subsingleton.elim _ _
    subst z
    have ho : Φ.distinguishedSection (R := k) σ o = Φ.affineChartι k σ (g o) := by
      rw [Φ.distinguishedSection_def (R := k)]
      exact Scheme.Hom.comp_apply g (Φ.affineChartι k σ) o
    exact hn (ho ▸ Φ.isNodeOfReducedBoundary_distinguishedSection k hΦ σ hdim hσ)
  obtain ⟨t, ht⟩ := not_forall.mp (fun h ↦ hnot (iSup_le h))
  have : Finite (ToricRay σ.val) := ToricRay.finite_of_fg (Φ.isToricCone σ.property).fg
  have : Nontrivial (ToricRay σ.val) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hσ]; decide)
  obtain ⟨r, hrt⟩ := exists_ne t
  exact ⟨Ray.ofToricRay Φ σ r, mem_range_rayChart_of_not_mem_otherRayIdeal k σ hΦ hσ hrt y ht⟩

variable [Nonempty Φ.cones]

local notation "D" => Φ.toricBoundaryIdeal k inferInstance
local notation "boundaryMap" => subschemeι D ≫ (Φ.finiteFanSchemeToSpec k)

/-- The reduced boundary of a complete regular rank-two fan is effective Cartier.
On each maximal cone chart the ideal is generated by the product of the two ray coordinates. -/
theorem isEffectiveCartier_boundaryIdeal (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hdim : Module.finrank ℤ N = 2) : (D).IsEffectiveCartier := by
  rw [isEffectiveCartier_iff_exists_isOpenImmersion]
  intro x
  obtain ⟨σ, hσ, y, hy⟩ := Φ.exists_twoRayChart_apply_eq k hΦ hc hdim x
  obtain ⟨r, e, hr, _⟩ := exists_twoRayChartCoordinates k Φ.lattice
    ((isRegular_iff.mp hΦ) σ.val σ.property) hdim hσ
  let a := e.symm (MvPolynomial.X 0) * e.symm (MvPolynomial.X 1)
  let E := Scheme.ΓSpecIso (.of (affineChartRing k Φ.lattice σ.val))
  have ha : a ≠ 0 := by
    dsimp only [a]
    rw [← map_mul]
    exact e.symm.toRingEquiv.map_ne_zero_iff.mpr
      (mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _))
  refine ⟨affineChart k Φ.lattice σ.val, inferInstance, Φ.affineChartι k σ, inferInstance, ⟨y, hy⟩,
    E.inv a, IsSMulRegular.of_ne_zero (E.symm.commRingCatIsoToRingEquiv.map_ne_zero_iff.mpr ha), ?_⟩
  rw [comap_boundaryIdeal_eq_ker_nodeChart k hΦ σ r e hr, Scheme.Hom.ker_Spec_map,
    CommRingCat.hom_ofHom, ker_nodeChart, Ideal.map_span, Set.image_singleton]

/-- The reduced boundary of a complete regular rank-two fan is nodal over the coefficient field. -/
theorem atWorstNodalOfRelativeDimensionOne_boundary (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hdim : Module.finrank ℤ N = 2) : AtWorstNodalOfRelativeDimensionOne boundaryMap := by
  classical
  let J := {σ : Φ.cones // Nat.card (ToricRay σ.val) = 2}
  choose q b hpb hbase _ using fun σ : J ↦
    Φ.exists_isPullback_boundaryIdeal_splitNode k hΦ σ.val hdim σ.property
  let (σ : J) : IsOpenImmersion (b σ) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hpb σ) inferInstance
  let U : (D).subscheme.OpenCover := Scheme.Cover.mkOfCovers J _ b (by
    intro x
    obtain ⟨σ, hσ, y, hy⟩ := exists_twoRayChart_apply_eq k hΦ hc hdim ((D).subschemeι x)
    refine ⟨⟨σ, hσ⟩, ?_⟩
    rw [← Set.mem_range, Scheme.Pullback.range_snd_of_isPullback (hpb ⟨σ, hσ⟩)]
    exact ⟨y, hy⟩)
  refine IsZariskiLocalAtSource.of_openCover (P := @AtWorstNodalOfRelativeDimensionOne) U ?_
  intro σ
  -- Unfold the cover member so that its inclusion is the chosen split-node chart.
  change AtWorstNodalOfRelativeDimensionOne (b σ ≫ boundaryMap)
  exact (hbase (σ : J)).symm ▸ NodeAlgebra.atWorstNodalOfRelativeDimensionOne 0

/-- Each node of the reduced boundary is the distinguished point of a unique two-ray
cone, and each such cone gives a node. -/
theorem isNodeOfReducedBoundary_iff_existsUnique_twoRayCone (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hdim : Module.finrank ℤ N = 2) {x : (Φ.finiteFanScheme k)} :
    (D).IsNodeOfReducedBoundary (Φ.finiteFanSchemeToSpec k) x ↔
      ∃! σ : Φ.cones, Nat.card (ToricRay σ.val) = 2 ∧
        Φ.distinguishedSection (R := k) σ (IsLocalRing.closedPoint k) = x := by
  have : IsReduced (D).subscheme := by
    infer_instance
  constructor
  · rw [isNodeOfReducedBoundary_iff_of_isReduced]
    rintro ⟨z, rfl, hz⟩
    obtain ⟨σ, hσ, y, hy⟩ := exists_twoRayChart_apply_eq k hΦ hc hdim ((D).subschemeι z)
    obtain ⟨q, b, hpb, hbase, ho⟩ := Φ.exists_isPullback_boundaryIdeal_splitNode k hΦ σ hdim hσ
    have : IsOpenImmersion b :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb inferInstance
    have hz' : z ∈ Set.range b := by
      rw [Scheme.Pullback.range_snd_of_isPullback hpb]
      exact ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := hz'
    have hw := (Scheme.Hom.isNodeAt_comp_iff_of_isOpenImmersion boundaryMap b w).mpr hz
    rw [hbase] at hw
    obtain ⟨o, rfl⟩ := (NodeAlgebra.isNodeAt_iff_mem_range_origin w).mp hw
    have hcomp : Spec.map (CommRingCat.ofHom (NodeAlgebra.origin k).toRingHom) ≫
        b ≫ (D).subschemeι = Φ.distinguishedSection (R := k) σ := by
      rw [← hpb.w, ho]
    have ho' : o = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    subst o
    have hx := congrArg
      (fun a : Spec (.of k) ⟶ (Φ.finiteFanScheme k) ↦ a (IsLocalRing.closedPoint k)) hcomp.symm
    refine ⟨σ, ⟨hσ, hx⟩, fun τ ⟨hτ, hpt⟩ ↦ ?_⟩
    apply Φ.eq_of_le_fullCone hΦ hdim hτ
    let p : Spec (.of k) := IsLocalRing.closedPoint k
    have hm := (Φ.distinguishedSection_mem_range_affineChartι_iff (R := k) σ σ p).mpr le_rfl
    exact (Φ.distinguishedSection_mem_range_affineChartι_iff (R := k) τ σ p).mp
      ((hpt.trans hx.symm).symm ▸ hm)
  · rintro ⟨σ, ⟨hσ, rfl⟩, -⟩
    exact Φ.isNodeOfReducedBoundary_distinguishedSection k hΦ σ hdim hσ

end Fan

end TauCeti.Toric

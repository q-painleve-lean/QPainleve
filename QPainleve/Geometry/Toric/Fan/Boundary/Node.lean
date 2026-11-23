/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Locus
public import QPainleve.Geometry.Toric.Fan.Boundary.Basic
public import QPainleve.Geometry.Toric.Fan.Point
public import TauCeti.RingTheory.Node.Branches

import QPainleve.AlgebraicGeometry.Curves.Node.Split
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Cone.TwoDimensional
import QPainleve.Geometry.Toric.Fan.Boundary.Ideal
import QPainleve.Geometry.Toric.Fan.Boundary.Intersection
import QPainleve.Geometry.Toric.Fan.TwoDimensional
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Pullback.Carrier
import TauCeti.RingTheory.Node.Reduced
import TauCeti.Geometry.Toric.Algebraic.Fan.AffineSpace.Scheme

/-!
# Nodes in regular toric surface boundaries

On the affine chart of a two-dimensional regular cone, the two ray divisors
are the coordinate axes and the distinguished point is their common origin.
The reduced boundary at that point is therefore the split node
`Spec ℂ[x,y]/(xy)`. The comparison uses Tau Ceti's affine-space coordinates
and its split-node singular locus. For a complete rank-two fan, these charts
cover the reduced boundary and identify its nodes with the two-ray cones.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

private theorem exists_twoRayChartCoordinates {C : PointedCone ℝ V}
    (hi : IsIntegralLattice i) (hC : IsRegularCone i C)
    (hN : Module.finrank ℤ N = 2) (hc : Nat.card (ToricRay C) = 2) :
    ∃ (r : Fin 2 ≃ ToricRay C) (e : affineCoordinateRing hi C ≃ₐ[ℂ] MvPolynomial (Fin 2) ℂ),
      (∀ j, rayIdeal hi hC.toIsToricCone (r j) =
        Ideal.span {e.symm (MvPolynomial.X j)}) ∧
      (NodeAlgebra.origin ℂ).comp ((NodeAlgebra.mk 0).comp e.toAlgHom) =
        distinguishedPoint hi (⊤ : C.Face) := by
  classical
  obtain ⟨r, b, hb⟩ := hC.exists_basis_primitiveGenerators hi hN hc
  have hcone : C = projectiveSpaceCone b i {none}ᶜ := by
    rw [projectiveSpaceCone_compl_none]
    simpa only [← Set.range_comp, Function.comp_def] using
      (hC.hull_eq_of_basis_primitiveGenerators hi b r hb).symm
  subst C
  let e := Fan.affineSpaceCoordinateRingEquiv b hi
  let b' := b.reindex (r.trans (Equiv.sumEmpty (ToricRay (projectiveSpaceCone b i {none}ᶜ))
    (Fin 0)).symm)
  have hb' (k : Fin 2) : b' (Sum.inl (r k)) = b k := by simp [b']
  have hprim (t : ToricRay (projectiveSpaceCone b i {none}ᶜ)) :
      IsPrimitiveGenerator i t (b' (Sum.inl t)) := by
    obtain ⟨k, rfl⟩ := r.surjective t
    rw [hb', hb]
    exact isPrimitiveGenerator_primitiveGenerator hi hC.toIsToricCone _
  refine ⟨r, e, ?_, ?_⟩
  · intro j
    dsimp only [e]
    rw [rayIdeal_eq_span hi _ hprim, Fan.affineSpaceCoordinateRingEquiv_symm_X]
    have hcoord : b'.coord (Sum.inl (r j)) = b.coord j := by
      apply b.ext
      intro k
      nth_rw 1 [← hb' k]
      simp [Module.Basis.coord_apply, Finsupp.single_apply, r.injective.eq_iff]
    have hm : dualSemigroupCoord hi hC.toIsToricCone hprim (Sum.inl (r j)) =
        ⟨(b.coord j).toAddMonoidHom,
          Fan.coord_mem_dualSemigroup_affineSpace b hi j (Fan.affineSpaceMaximalCone b hi)⟩ := by
      apply Subtype.ext
      exact (coe_dualSemigroupCoord hi _ hprim _).trans
        (congrArg LinearMap.toAddMonoidHom hcoord)
    rw [hm, MonoidAlgebra.of_apply]
  · apply (AlgHom.cancel_right (f := e.symm.toAlgHom) e.symm.surjective).mp
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply,
      NodeAlgebra.mk_X, NodeAlgebra.origin_coord]
    dsimp only [e]
    rw [Fan.affineSpaceCoordinateRingEquiv_symm_X, distinguishedPoint_apply_single]
    have hnonzero : ¬ ∀ x ∈ (⊤ : (projectiveSpaceCone b i {none}ᶜ).Face),
        hi.realCharacter (b.coord j).toAddMonoidHom x = 0 := by
      intro h
      have hz := h (i (b j)) ((r j).val.isFaceOf.le
        (by rw [hb j]; exact primitiveGenerator_mem hi hC.toIsToricCone (r j)))
      simp [hi.realCharacter_apply, Module.Basis.coord_apply] at hz
    simp [hnonzero]

namespace Fan

variable {Φ : Fan i}

private theorem mem_boundaryIdeal_comap_chart_iff (hΦ : Φ.IsRegular) (σ : Φ.cones)
    (x : Φ.affineToricChart σ) :
    x ∈ ((Φ.boundaryIdeal ⟨σ⟩).comap (Φ.affineToricChartι σ)).support ↔
      ∃ r : ToricRay σ.val, rayIdeal Φ.lattice (Φ.isToricCone σ.property) r ≤ x.asIdeal := by
  have hcomap (ρ : Φ.Ray) :
      x ∈ ((Φ.rayBoundaryIdeal hΦ ρ).comap (Φ.affineToricChartι σ)).support ↔
        Φ.affineToricChartι σ x ∈ (Φ.rayBoundaryIdeal hΦ ρ).support := by
    rw [← SetLike.mem_coe, support_comap, Closeds.coe_preimage]
    rfl
  rw [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage,
    Φ.support_boundaryIdeal_eq_iUnion_closure hΦ, Set.mem_iUnion]
  simp only [← Φ.coe_support_rayBoundaryIdeal hΦ]
  have hlocal (r : ToricRay σ.val) :
      x ∈ ((Φ.rayBoundaryIdeal hΦ (Ray.ofToricRay Φ σ r)).comap
          (Φ.affineToricChartι σ)).support ↔
        rayIdeal Φ.lattice (Φ.isToricCone σ.property) r ≤ x.asIdeal := by
    have hle := Ray.toCone_ofToricRay_le Φ σ r
    rw [Φ.comap_rayBoundaryIdeal_eq_ofIdealTop hΦ _ σ hle,
      ← SetLike.mem_coe, coe_support_ofIdealTop, Spec_zeroLocus]
    let p : PrimeSpectrum (affineCoordinateRing Φ.lattice σ.val) := x
    -- Use the prime spectrum carrier explicitly to apply the affine zero-locus API.
    change p ∈ PrimeSpectrum.zeroLocus _ ↔ _ ≤ p.asIdeal
    rw [PrimeSpectrum.mem_zeroLocus, ← Ideal.coe_comap,
      Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso (C := CommRingCat) _),
      SetLike.coe_subset_coe]
    simpa only [rayEquiv_apply, rayEquiv_symm_apply] using
      iff_of_eq (congrArg (fun t ↦ rayIdeal Φ.lattice (Φ.isToricCone σ.property) t ≤ x.asIdeal)
        ((Φ.rayEquiv σ).apply_symm_apply r))
  constructor
  · rintro ⟨ρ, hρ⟩
    have hx := (hcomap ρ).mpr hρ
    by_cases hle : ρ.toCone ≤ σ
    · obtain ⟨r, hr⟩ := (Φ.rayEquiv σ).symm.surjective ⟨ρ, hle⟩
      have he : Ray.ofToricRay Φ σ r = ρ := by
        simpa only [rayEquiv_symm_apply] using congrArg Subtype.val hr
      exact ⟨r, (hlocal r).mp (he.symm ▸ hx)⟩
    · rw [Φ.comap_rayBoundaryIdeal_eq_top hΦ ρ σ hle, support_top] at hx
      exact hx.elim
  · rintro ⟨r, hr⟩
    exact ⟨Ray.ofToricRay Φ σ r, (hcomap _).mp ((hlocal r).mpr hr)⟩

private theorem comap_boundaryIdeal_eq_ker_nodeChart (hΦ : Φ.IsRegular) (σ : Φ.cones)
    (r : Fin 2 ≃ ToricRay σ.val)
    (e : affineCoordinateRing Φ.lattice σ.val ≃ₐ[ℂ] MvPolynomial (Fin 2) ℂ)
    (hr : ∀ j, rayIdeal Φ.lattice (Φ.isToricCone σ.property) (r j) =
      Ideal.span {e.symm (MvPolynomial.X j)}) :
    let a := (NodeAlgebra.mk 0).comp e.toAlgHom
    (Φ.boundaryIdeal ⟨σ⟩).comap (Φ.affineToricChartι σ) =
      (Spec.map (CommRingCat.ofHom a.toRingHom)).ker := by
  intro a
  let j := Φ.affineToricChartι σ
  let q : Spec (.of (NodeAlgebra ℂ 0)) ⟶ Φ.affineToricChart σ :=
    Spec.map (CommRingCat.ofHom a.toRingHom)
  have hsurj : Function.Surjective a := (NodeAlgebra.mk_surjective 0).comp e.surjective
  have : IsClosedImmersion q := IsClosedImmersion.spec_of_surjective _ hsurj
  -- Work with the named quotient morphism so that its affine range formula applies below.
  change (Φ.boundaryIdeal ⟨σ⟩).comap j = q.ker
  have hD : ((Φ.boundaryIdeal ⟨σ⟩).comap j).radical = (Φ.boundaryIdeal ⟨σ⟩).comap j := by
    rw [radical_comap_of_isOpenImmersion]
    congr 1
    apply (isReduced_subscheme_iff_radical_eq _).mp
    rw [Φ.boundaryIdeal_def]
    infer_instance
  rw [q.ker_eq_vanishingIdeal_support, ← hD, ← vanishingIdeal_support]
  apply congrArg vanishingIdeal
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, mem_boundaryIdeal_comap_chart_iff hΦ,
    ← SetLike.mem_coe, q.support_ker, q.isClosedEmbedding.isClosed_range.closure_eq]
  have hqrange : Set.range q = PrimeSpectrum.zeroLocus (RingHom.ker a.toRingHom : Set _) :=
    range_comap_of_surjective _ _ hsurj
  rw [hqrange]
  let p : PrimeSpectrum (affineCoordinateRing Φ.lattice σ.val) := x
  -- The chart is affine, so the range condition is ideal containment at its prime.
  change (∃ t : ToricRay σ.val, rayIdeal Φ.lattice (Φ.isToricCone σ.property) t ≤ p.asIdeal) ↔
    p ∈ PrimeSpectrum.zeroLocus _
  rw [PrimeSpectrum.mem_zeroLocus, r.symm.exists_congr_left, Equiv.symm_symm,
    Fin.exists_fin_two, hr, hr]
  have hk : RingHom.ker a.toRingHom =
      Ideal.span {e.symm (MvPolynomial.X 0) * e.symm (MvPolynomial.X 1)} := by
    refine (AlgHom.comap_ker (NodeAlgebra.mk (0 : ℂ)) e.toAlgHom).symm.trans ?_
    have hqker : RingHom.ker (NodeAlgebra.mk (0 : ℂ) :
        MvPolynomial (Fin 2) ℂ →+* NodeAlgebra ℂ 0) =
        Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1} := by simp
    refine (congrArg (Ideal.comap (e.toAlgHom :
      affineCoordinateRing Φ.lattice σ.val →+* MvPolynomial (Fin 2) ℂ)) hqker).trans ?_
    exact (Ideal.map_symm e.toRingEquiv).symm.trans (by simp [Ideal.map_span])
  rw [hk]
  simp only [SetLike.coe_subset_coe, Ideal.span_singleton_le_iff_mem,
    p.isPrime.mul_mem_iff_mem_or_mem]

/-- The reduced boundary on the chart of a two-ray cone is the split node. The
comparison is a pullback of the ambient affine toric chart along the boundary inclusion. -/
theorem exists_isPullback_boundaryIdeal_splitNode (hΦ : Φ.IsRegular) (σ : Φ.cones)
    (hN : Module.finrank ℤ N = 2) (hc : Nat.card (ToricRay σ.val) = 2) :
    ∃ (q : Spec (.of (NodeAlgebra ℂ 0)) ⟶ Φ.affineToricChart σ)
      (b : Spec (.of (NodeAlgebra ℂ 0)) ⟶ (Φ.boundaryIdeal ⟨σ⟩).subscheme),
      IsPullback q b (Φ.affineToricChartι σ) (Φ.boundaryIdeal ⟨σ⟩).subschemeι ∧
      b ≫ (Φ.boundaryIdeal ⟨σ⟩).subschemeι ≫ Φ.algebraicRealizationStructureMap =
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (NodeAlgebra ℂ 0))) ∧
      Spec.map (CommRingCat.ofHom (NodeAlgebra.origin ℂ).toRingHom) ≫ q ≫
        Φ.affineToricChartι σ = Φ.distinguishedPointHom σ := by
  obtain ⟨r, e, hr, ho⟩ := exists_twoRayChartCoordinates Φ.lattice
    ((isRegular_iff.mp hΦ) σ.val σ.property) hN hc
  let a := (NodeAlgebra.mk 0).comp e.toAlgHom
  let q : Spec (.of (NodeAlgebra ℂ 0)) ⟶ Φ.affineToricChart σ :=
    Spec.map (CommRingCat.ofHom a.toRingHom)
  let j := Φ.affineToricChartι σ
  let D := Φ.boundaryIdeal ⟨σ⟩
  have : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ ((NodeAlgebra.mk_surjective 0).comp e.surjective)
  have hker : D.comap j = q.ker := comap_boundaryIdeal_eq_ker_nodeChart hΦ σ r e hr
  let b := IsClosedImmersion.lift D.subschemeι (q ≫ j) (by
    rw [ker_subschemeι, Scheme.Hom.ker_comp, ← hker]
    exact le_map_comap _ _)
  have hb : b ≫ D.subschemeι = q ≫ j := IsClosedImmersion.lift_fac _ _ _
  refine ⟨q, b, isPullback_of_isClosedImmersion q D.subschemeι b j hb.symm (by
    rwa [ker_subschemeι]), ?_, ?_⟩
  · rw [← Category.assoc, hb, Category.assoc,
      Φ.affineToricChartι_comp_algebraicRealizationStructureMap]
    dsimp only [q]
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact a.commutes c
  · rw [Φ.distinguishedPointHom_def, ← Category.assoc]
    dsimp only [q]
    rw [← Spec.map_comp]
    have ha : CommRingCat.ofHom a.toRingHom ≫ CommRingCat.ofHom (NodeAlgebra.origin ℂ).toRingHom =
        CommRingCat.ofHom (distinguishedPoint Φ.lattice (⊤ : σ.val.Face)).toRingHom := by
      rw [← CommRingCat.ofHom_comp]
      exact congrArg (fun g : affineCoordinateRing Φ.lattice σ.val →ₐ[ℂ] ℂ ↦
        CommRingCat.ofHom g.toRingHom) ho
    rw [ha]

/-- The distinguished point of a two-dimensional cone of a regular surface fan is a
node of the reduced toric boundary. This holds for noncomplete fans as well. -/
theorem isNodeOfReducedBoundary_distinguishedPointHom (hΦ : Φ.IsRegular) (σ : Φ.cones)
    (hN : Module.finrank ℤ N = 2) (hc : Nat.card (ToricRay σ.val) = 2) :
    (Φ.boundaryIdeal ⟨σ⟩).IsNodeOfReducedBoundary Φ.algebraicRealizationStructureMap
      (Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ)) := by
  obtain ⟨q, b, hpb, hbase, ho⟩ := Φ.exists_isPullback_boundaryIdeal_splitNode hΦ σ hN hc
  let D := Φ.boundaryIdeal ⟨σ⟩
  let x := Spec.map (CommRingCat.ofHom (NodeAlgebra.origin ℂ).toRingHom)
    (IsLocalRing.closedPoint ℂ)
  have : IsOpenImmersion b := MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    hpb inferInstance
  have : IsReduced D.subscheme := by
    dsimp only [D]
    rw [Φ.boundaryIdeal_def]
    infer_instance
  refine (D.isNodeOfReducedBoundary_iff_of_isReduced _ _).mpr ⟨b x, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← hpb.w]
    exact congrArg (fun a : Spec (.of ℂ) ⟶ Φ.algebraicRealization ↦
      a (IsLocalRing.closedPoint ℂ)) ho
  · apply (Scheme.Hom.isNodeAt_comp_iff_of_isOpenImmersion
      (D.subschemeι ≫ Φ.algebraicRealizationStructureMap) b x).mp
    rw [hbase]
    exact (NodeAlgebra.isNodeAt_iff_mem_range_origin x).mpr ⟨IsLocalRing.closedPoint ℂ, rfl⟩

private theorem exists_twoRayChart_apply_eq (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hdim : Module.finrank ℤ N = 2) (x : Φ.algebraicRealization) :
    ∃ (υ : Φ.cones) (_ : Nat.card (ToricRay υ.val) = 2)
      (y : Φ.affineToricChart υ), Φ.affineToricChartι υ y = x := by
  obtain ⟨σ, y, hy⟩ := Φ.exists_affineToricChartι_apply_eq x
  obtain ⟨υ, hσυ, hυ⟩ := exists_le_cone_of_card_toricRay_eq_two hΦ hc hdim σ
  let j := faceAffineToricSchemeMap Φ.lattice (Φ.isFaceOf_of_le υ.property σ.property hσυ)
  refine ⟨υ, hυ, j y, ?_⟩
  rw [← Scheme.Hom.comp_apply, Φ.faceAffineToricSchemeMap_comp_affineToricChartι]
  exact hy

private theorem mem_range_rayChart_of_not_mem_otherRayIdeal (σ : Φ.cones)
    (hΦ : Φ.IsRegular) (hc : Nat.card (ToricRay σ.val) = 2)
    {r t : ToricRay σ.val} (hrt : r ≠ t) (y : Φ.affineToricChart σ)
    (hy : ¬ rayIdeal Φ.lattice (Φ.isToricCone σ.property) t ≤ y.asIdeal) :
    Φ.affineToricChartι σ y ∈ Set.range (Φ.affineToricChartι (Ray.ofToricRay Φ σ r).toCone) := by
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
  have hy' : y ∈ Set.range (faceAffineToricSchemeMap Φ.lattice F.isFaceOf) := by
    rw [range_faceAffineToricSchemeMap Φ.lattice hσ.fg m]
    let p : PrimeSpectrum (affineCoordinateRing Φ.lattice σ.val) := y
    -- The spectrum's basic open is written on the affine chart's point carrier.
    change p ∈ PrimeSpectrum.basicOpen (MonoidAlgebra.single (ofAdd m) 1)
    rw [PrimeSpectrum.mem_basicOpen]
    simpa only [rayIdeal_eq_span Φ.lattice hσ hb, Ideal.span_singleton_le_iff_mem,
      MonoidAlgebra.of_apply, m] using hy
  rw [hface] at hy'
  let τ : Φ.cones := ⟨r.toPointedCone, Φ.mem_of_isFaceOf σ.property r.val.isFaceOf⟩
  have hτ : (Ray.ofToricRay Φ σ r).toCone = τ :=
    Subtype.ext (Ray.toCone_ofToricRay Φ σ r)
  rw [hτ]
  obtain ⟨z, hz⟩ := hy'
  refine ⟨z, ?_⟩
  rw [← hz, ← Scheme.Hom.comp_apply]
  exact (congrArg (fun f : Φ.affineToricChart τ ⟶ Φ.algebraicRealization ↦ f z)
    (Φ.faceAffineToricSchemeMap_comp_affineToricChartι (τ := τ) (σ := σ) r.val.isFaceOf)).symm

/-- Every point of a complete regular toric surface outside the nodes of the reduced
boundary belongs to a ray chart. -/
theorem exists_rayChart_of_not_isNodeOfReducedBoundary
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (hdim : Module.finrank ℤ N = 2)
    {x : Φ.algebraicRealization}
    (hn : ¬ (Φ.boundaryIdeal hc.nonempty_cones).IsNodeOfReducedBoundary
      Φ.algebraicRealizationStructureMap x) :
    ∃ ρ : Φ.Ray, x ∈ Set.range (Φ.affineToricChartι ρ.toCone) := by
  obtain ⟨σ, hσ, y, rfl⟩ := exists_twoRayChart_apply_eq hΦ hc hdim x
  classical
  have hnot : ¬ (⨆ t : ToricRay σ.val, rayIdeal Φ.lattice (Φ.isToricCone σ.property) t) ≤
      y.asIdeal := by
    rw [iSup_rayIdeal_eq_ker_distinguishedPoint Φ.lattice (Φ.isToricCone σ.property)
      (isRegular_iff.mp hΦ _ σ.property) (hσ.trans hdim.symm)]
    intro h
    let d := distinguishedPoint Φ.lattice (⊤ : σ.val.Face)
    let g : Spec (.of ℂ) ⟶ Φ.affineToricChart σ := Spec.map (CommRingCat.ofHom d.toRingHom)
    have hg : Set.range g = PrimeSpectrum.zeroLocus (RingHom.ker d.toRingHom : Set _) :=
      range_comap_of_surjective _ _ (fun a ↦ ⟨algebraMap ℂ _ a, d.commutes a⟩)
    have hy' : y ∈ Set.range g := hg.symm ▸ (PrimeSpectrum.mem_zeroLocus y _).mpr h
    obtain ⟨z, rfl⟩ := hy'
    let o : Spec (.of ℂ) := IsLocalRing.closedPoint ℂ
    have hz : z = o := Subsingleton.elim _ _
    subst z
    have ho : Φ.distinguishedPointHom σ o = Φ.affineToricChartι σ (g o) := by
      rw [Φ.distinguishedPointHom_def]
      exact Scheme.Hom.comp_apply g (Φ.affineToricChartι σ) o
    exact hn (ho ▸ Φ.isNodeOfReducedBoundary_distinguishedPointHom hΦ σ hdim hσ)
  obtain ⟨t, ht⟩ := not_forall.mp (fun h ↦ hnot (iSup_le h))
  have : Finite (ToricRay σ.val) := ToricRay.finite_of_fg (Φ.isToricCone σ.property).fg
  have : Nontrivial (ToricRay σ.val) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hσ]; decide)
  obtain ⟨r, hrt⟩ := exists_ne t
  exact ⟨Ray.ofToricRay Φ σ r, mem_range_rayChart_of_not_mem_otherRayIdeal σ hΦ hσ hrt y ht⟩

variable [Nonempty Φ.cones]

local notation "D" => Φ.boundaryIdeal inferInstance
local notation "boundaryMap" => subschemeι D ≫ Φ.algebraicRealizationStructureMap

/-- The reduced boundary of a complete regular rank-two fan is nodal over `ℂ`. -/
theorem atWorstNodalOfRelativeDimensionOne_boundary (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hdim : Module.finrank ℤ N = 2) : AtWorstNodalOfRelativeDimensionOne boundaryMap := by
  classical
  let J := {σ : Φ.cones // Nat.card (ToricRay σ.val) = 2}
  choose q b hpb hbase _ using fun σ : J ↦
    Φ.exists_isPullback_boundaryIdeal_splitNode hΦ σ.val hdim σ.property
  let (σ : J) : IsOpenImmersion (b σ) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hpb σ) inferInstance
  let U : (D).subscheme.OpenCover := Scheme.Cover.mkOfCovers J _ b (by
    intro x
    obtain ⟨σ, hσ, y, hy⟩ := exists_twoRayChart_apply_eq hΦ hc hdim ((D).subschemeι x)
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
    (hdim : Module.finrank ℤ N = 2) {x : Φ.algebraicRealization} :
    (D).IsNodeOfReducedBoundary Φ.algebraicRealizationStructureMap x ↔
      ∃! σ : Φ.cones, Nat.card (ToricRay σ.val) = 2 ∧
        Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ) = x := by
  have : IsReduced (D).subscheme := by
    rw [Φ.boundaryIdeal_def]
    infer_instance
  constructor
  · rw [isNodeOfReducedBoundary_iff_of_isReduced]
    rintro ⟨z, rfl, hz⟩
    obtain ⟨σ, hσ, y, hy⟩ := exists_twoRayChart_apply_eq hΦ hc hdim ((D).subschemeι z)
    obtain ⟨q, b, hpb, hbase, ho⟩ := Φ.exists_isPullback_boundaryIdeal_splitNode hΦ σ hdim hσ
    have : IsOpenImmersion b :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb inferInstance
    have hz' : z ∈ Set.range b := by
      rw [Scheme.Pullback.range_snd_of_isPullback hpb]
      exact ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := hz'
    have hw := (Scheme.Hom.isNodeAt_comp_iff_of_isOpenImmersion boundaryMap b w).mpr hz
    rw [hbase] at hw
    obtain ⟨o, rfl⟩ := (NodeAlgebra.isNodeAt_iff_mem_range_origin w).mp hw
    have hcomp : Spec.map (CommRingCat.ofHom (NodeAlgebra.origin ℂ).toRingHom) ≫
        b ≫ (D).subschemeι = Φ.distinguishedPointHom σ := by
      rw [← hpb.w, ho]
    have ho' : o = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst o
    have hx := congrArg
      (fun a : Spec (.of ℂ) ⟶ Φ.algebraicRealization ↦ a (IsLocalRing.closedPoint ℂ)) hcomp.symm
    refine ⟨σ, ⟨hσ, hx⟩, fun τ ⟨hτ, hpt⟩ ↦ ?_⟩
    apply Φ.eq_of_le_fullCone hΦ hdim hτ
    let p : Spec (.of ℂ) := IsLocalRing.closedPoint ℂ
    have hm := (Φ.distinguishedPointHom_mem_range_affineToricChartι_iff σ σ p).mpr le_rfl
    exact (Φ.distinguishedPointHom_mem_range_affineToricChartι_iff τ σ p).mp
      ((hpt.trans hx.symm).symm ▸ hm)
  · rintro ⟨σ, ⟨hσ, rfl⟩, -⟩
    exact Φ.isNodeOfReducedBoundary_distinguishedPointHom hΦ σ hdim hσ

end Fan

end TauCeti.Toric

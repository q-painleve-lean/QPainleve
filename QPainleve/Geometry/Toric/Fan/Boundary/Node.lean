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
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.RingTheory.Node.Reduced
import TauCeti.Geometry.Toric.Algebraic.Fan.AffineSpace.Scheme

/-!
# Nodes in regular toric surface boundaries

On the affine chart of a two-dimensional regular cone, the two ray divisors
are the coordinate axes and the distinguished point is their common origin.
The reduced boundary at that point is therefore the split node
`Spec ℂ[x,y]/(xy)`. The comparison uses Tau Ceti's affine-space coordinates
and its split-node singular locus.
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

end Fan

end TauCeti.Toric

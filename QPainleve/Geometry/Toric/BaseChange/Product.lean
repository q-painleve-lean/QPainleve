/-
Copyright (c) 2026 The Tau Ceti contributors and The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import QPainleve.Geometry.Toric.BaseChange.Fan.Map
public import TauCeti.Geometry.Toric.Algebraic.Fan.Product.Basic

import QPainleve.Geometry.Toric.BaseChange.Subfan
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Equiv
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Product

/-!
# Products of toric fan schemes over a ring

The cone chart of a product fan is the affine fiber product of the two
factor charts. These affine products cover the fiber product of the fan schemes
and their overlaps are computed by intersecting the cones in each factor.

The affine and fan comparisons follow Tau Ceti's product-scheme construction.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Multiplicative TensorProduct

namespace TauCeti.Toric

universe u

variable (R : Type u) [CommRing R]

section CoordinateRing

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
  (σ : PointedCone ℝ V) (τ : PointedCone ℝ V')

/-- The tensor product of the coordinate rings of two cones is the coordinate ring of their
product, canonically and without choosing bases. -/
noncomputable def affineChartRingProdEquiv :
    affineChartRing R hi σ ⊗[R] affineChartRing R hi' τ ≃ₐ[R]
      affineChartRing R (hi.prod hi') (σ.prod τ) :=
  (Algebra.TensorProduct.congr
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv R R (dualSemigroup hi σ))
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv R R (dualSemigroup hi' τ))).trans <|
    (TauCeti.MonoidAlgebra.prodTensorBialgEquiv R
      (G := Multiplicative (dualSemigroup hi σ))
      (H := Multiplicative (dualSemigroup hi' τ))).symm.toAlgEquiv.trans <|
    (MonoidAlgebra.domCongr R R
      ((MulEquiv.prodMultiplicative _ _).symm.trans
        (dualSemigroupProdEquiv hi hi' σ τ).symm.toMultiplicative)).trans
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv R R
        (dualSemigroup (hi.prod hi') (σ.prod τ))).symm

/-- A tensor of monomials maps to the monomial of the coproduct character. -/
@[simp]
theorem affineChartRingProdEquiv_single_tmul_single
    (m : dualSemigroup hi σ) (m' : dualSemigroup hi' τ) (z z' : R) :
    affineChartRingProdEquiv R hi hi' σ τ
        (AddMonoidAlgebra.single m z ⊗ₜ[R] AddMonoidAlgebra.single m' z') =
      AddMonoidAlgebra.single ((dualSemigroupProdEquiv hi hi' σ τ).symm (m, m')) (z * z') := by
  simp only [affineChartRingProdEquiv, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom,
    AddMonoidAlgebra.toMultiplicativeAlgEquiv_single,
    BialgEquiv.coe_toAlgEquiv, TauCeti.MonoidAlgebra.prodTensorBialgEquiv_symm_single_tmul_single,
    MonoidAlgebra.domCongr_single, MulEquiv.trans_apply, MulEquiv.prodMultiplicative_symm_apply,
    AddEquiv.toMultiplicative_apply_apply, AddMonoidAlgebra.toMultiplicativeAlgEquiv_symm_single,
    toAdd_ofAdd]

/-- The first lattice projection induces the first inclusion into the tensor product of
coordinate rings under the product comparison. -/
@[simp]
theorem affineChartRingProdEquiv_comp_includeLeft :
    (affineChartRingProdEquiv R hi hi' σ τ).toAlgHom.comp
        Algebra.TensorProduct.includeLeft =
      AddMonoidAlgebra.mapDomainAlgHom R R
        (dualSemigroupMap (σ := σ.prod τ) (τ := σ)
          (hi.prod hi') hi (AddMonoidHom.fst N N')
          (LinearMap.fst ℝ V V') (fun n ↦ by simp) (by
            simpa only [LinearMap.coe_fst, Submodule.prod_coe] using
              (Set.mapsTo_fst_prod (s := (σ : Set V)) (t := (τ : Set V'))))) := by
  apply AddMonoidAlgebra.algHom_ext
  · intro m
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
      Algebra.TensorProduct.includeLeft_apply, AddMonoidAlgebra.one_def,
      affineChartRingProdEquiv_single_tmul_single, AddMonoidAlgebra.mapDomainAlgHom_apply,
      AddMonoidAlgebra.mapDomain_single, mul_one]
    congr 1
    apply Subtype.ext
    ext n
    simp
  · ext

/-- The second lattice projection induces the second inclusion into the tensor product of
coordinate rings under the product comparison. -/
@[simp]
theorem affineChartRingProdEquiv_comp_includeRight :
    (affineChartRingProdEquiv R hi hi' σ τ).toAlgHom.comp
        Algebra.TensorProduct.includeRight =
      AddMonoidAlgebra.mapDomainAlgHom R R
        (dualSemigroupMap (σ := σ.prod τ) (τ := τ)
          (hi.prod hi') hi' (AddMonoidHom.snd N N')
          (LinearMap.snd ℝ V V') (fun n ↦ by simp) (by
            simpa only [LinearMap.coe_snd, Submodule.prod_coe] using
              (Set.mapsTo_snd_prod (s := (σ : Set V)) (t := (τ : Set V'))))) := by
  apply AddMonoidAlgebra.algHom_ext
  · intro m
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
      Algebra.TensorProduct.includeRight_apply, AddMonoidAlgebra.one_def,
      affineChartRingProdEquiv_single_tmul_single, AddMonoidAlgebra.mapDomainAlgHom_apply,
      AddMonoidAlgebra.mapDomain_single, one_mul]
    congr 1
    apply Subtype.ext
    ext n
    simp
  · ext

end CoordinateRing

section Scheme

variable {N N' : Type u} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
  (σ : PointedCone ℝ V) (τ : PointedCone ℝ V')

/-- The affine toric scheme of a product cone is canonically the fibre product of the
factor affine toric schemes over `Spec R`. -/
noncomputable def affineChartProdIso :
    affineChart R (hi.prod hi') (σ.prod τ) ≅
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (affineChartRing R hi σ))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (affineChartRing R hi' τ)))) :=
  Scheme.Spec.mapIso
    (affineChartRingProdEquiv R hi hi' σ τ).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso R (affineChartRing R hi σ) (affineChartRing R hi' τ)).symm

/-- The first fibre-product projection is the toric morphism of the first lattice projection. -/
@[reassoc (attr := simp)]
theorem affineChartProdIso_hom_fst :
    (affineChartProdIso R hi hi' σ τ).hom ≫ pullback.fst _ _ =
      affineChartMap R (σ := σ.prod τ) (τ := σ)
        (hi.prod hi') hi (AddMonoidHom.fst N N') (LinearMap.fst ℝ V V')
        (fun n ↦ by simp) (by
          simpa only [LinearMap.coe_fst, Submodule.prod_coe] using
            (Set.mapsTo_fst_prod (s := (σ : Set V)) (t := (τ : Set V')))) := by
  simp only [affineChartProdIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, pullbackSpecIso_inv_fst, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map]
  rw [← Spec.map_comp, affineChartMap_def]
  congr 1
  exact congrArg (fun f ↦ CommRingCat.ofHom f.toRingHom)
    (affineChartRingProdEquiv_comp_includeLeft R hi hi' σ τ)

/-- The second fibre-product projection is the toric morphism of the second lattice projection. -/
@[reassoc (attr := simp)]
theorem affineChartProdIso_hom_snd :
    (affineChartProdIso R hi hi' σ τ).hom ≫ pullback.snd _ _ =
      affineChartMap R (σ := σ.prod τ) (τ := τ)
        (hi.prod hi') hi' (AddMonoidHom.snd N N') (LinearMap.snd ℝ V V')
        (fun n ↦ by simp) (by
          simpa only [LinearMap.coe_snd, Submodule.prod_coe] using
            (Set.mapsTo_snd_prod (s := (σ : Set V)) (t := (τ : Set V')))) := by
  simp only [affineChartProdIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, pullbackSpecIso_inv_snd, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map]
  rw [← Spec.map_comp, affineChartMap_def]
  congr 1
  exact congrArg (fun f ↦ CommRingCat.ofHom f.toRingHom)
    (affineChartRingProdEquiv_comp_includeRight R hi hi' σ τ)

end Scheme

variable {N N' : Type u} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'}

namespace FanHom

variable (Φ : Fan i) (Ψ : Fan i')

/-- On a product affine chart, the algebraic map of the first fan projection is the affine
toric projection followed by the corresponding chart inclusion. -/
@[reassoc]
theorem affineChartι_prodCone_comp_fst_finiteFanSchemeHom
    (σ : Φ.cones) (τ : Ψ.cones) :
    (Φ.prod Ψ).affineChartι R (Φ.prodCone Ψ σ τ) ≫
        (FanHom.fst Φ Ψ).finiteFanSchemeHom R =
      affineChartMap R (σ := σ.val.prod τ.val) (τ := σ.val)
          (Φ.lattice.prod Ψ.lattice) Φ.lattice
          (AddMonoidHom.fst N N') (LinearMap.fst ℝ V V') (fun _ ↦ by simp)
          (by
            simpa only [LinearMap.coe_fst, Submodule.prod_coe] using
              (Set.mapsTo_fst_prod (s := (σ.val : Set V)) (t := (τ.val : Set V')))) ≫
        Φ.affineChartι R σ := by
  convert affineChartι_comp_finiteFanSchemeHom R (FanHom.fst Φ Ψ)
    (Φ.prodCone Ψ σ τ) σ
    (fun _ hx ↦ by simpa only [FanHom.fst_realMap, LinearMap.fst_apply] using hx.1) using 3
  simp only [FanHom.fst_latticeMap, FanHom.fst_realMap]

/-- On a product affine chart, the algebraic map of the second fan projection is the affine
toric projection followed by the corresponding chart inclusion. -/
@[reassoc]
theorem affineChartι_prodCone_comp_snd_finiteFanSchemeHom
    (σ : Φ.cones) (τ : Ψ.cones) :
    (Φ.prod Ψ).affineChartι R (Φ.prodCone Ψ σ τ) ≫
        (FanHom.snd Φ Ψ).finiteFanSchemeHom R =
      affineChartMap R (σ := σ.val.prod τ.val) (τ := τ.val)
          (Φ.lattice.prod Ψ.lattice) Ψ.lattice
          (AddMonoidHom.snd N N') (LinearMap.snd ℝ V V') (fun _ ↦ by simp)
          (by
            simpa only [LinearMap.coe_snd, Submodule.prod_coe] using
              (Set.mapsTo_snd_prod (s := (σ.val : Set V)) (t := (τ.val : Set V')))) ≫
        Ψ.affineChartι R τ := by
  convert affineChartι_comp_finiteFanSchemeHom R (FanHom.snd Φ Ψ)
    (Φ.prodCone Ψ σ τ) τ
    (fun _ hx ↦ by simpa only [FanHom.snd_realMap, LinearMap.snd_apply] using hx.2) using 3
  simp only [FanHom.snd_latticeMap, FanHom.snd_realMap]

end FanHom

namespace Fan

variable (Φ : Fan i) (Ψ : Fan i')

/-- The scheme of a product fan maps canonically to the fibre product of the two fan schemes
over `Spec R`, through the algebraic maps induced by the fan projections. -/
noncomputable def finiteFanSchemeProdComparison :
    ((Φ.prod Ψ).finiteFanScheme R) ⟶
      pullback (Φ.finiteFanSchemeToSpec R) (Ψ.finiteFanSchemeToSpec R) :=
  pullback.lift ((FanHom.fst Φ Ψ).finiteFanSchemeHom R) ((FanHom.snd Φ Ψ).finiteFanSchemeHom R)
    (by simp only [FanHom.finiteFanSchemeHom_comp_finiteFanSchemeToSpec])

/-- The first projection of the product comparison is the toric map induced by the first fan
projection. -/
@[reassoc (attr := simp)]
theorem finiteFanSchemeProdComparison_fst :
    Φ.finiteFanSchemeProdComparison R Ψ ≫
        pullback.fst (Φ.finiteFanSchemeToSpec R) (Ψ.finiteFanSchemeToSpec R) =
      (FanHom.fst Φ Ψ).finiteFanSchemeHom R := by
  simp [finiteFanSchemeProdComparison]

/-- The second projection of the product comparison is the toric map induced by the second fan
projection. -/
@[reassoc (attr := simp)]
theorem finiteFanSchemeProdComparison_snd :
    Φ.finiteFanSchemeProdComparison R Ψ ≫
        pullback.snd (Φ.finiteFanSchemeToSpec R) (Ψ.finiteFanSchemeToSpec R) =
      (FanHom.snd Φ Ψ).finiteFanSchemeHom R := by
  simp [finiteFanSchemeProdComparison]

/-- The product of two affine chart inclusions, as a morphism from the fibre product of the
affine charts to the fibre product of the two fan schemes. -/
noncomputable def affineChartProdMap (σ : Φ.cones) (τ : Ψ.cones) :
    pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (affineChartRing R Φ.lattice σ.val))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (affineChartRing R Ψ.lattice τ.val)))) ⟶
      pullback (Φ.finiteFanSchemeToSpec R) (Ψ.finiteFanSchemeToSpec R) :=
  pullback.map
    (Spec.map (CommRingCat.ofHom (algebraMap R (affineChartRing R Φ.lattice σ.val))))
    (Spec.map (CommRingCat.ofHom (algebraMap R (affineChartRing R Ψ.lattice τ.val))))
    (Φ.finiteFanSchemeToSpec R) (Ψ.finiteFanSchemeToSpec R)
    (Φ.affineChartι R σ) (Ψ.affineChartι R τ) (𝟙 _) (by
      rw [Category.comp_id, affineChartι_finiteFanSchemeToSpec R]) (by
      rw [Category.comp_id, affineChartι_finiteFanSchemeToSpec R])

/-- The first projection of the product of two affine chart inclusions is the first local
projection followed by the first chart inclusion. -/
@[reassoc (attr := simp)]
theorem affineChartProdMap_fst (σ : Φ.cones) (τ : Ψ.cones) :
    Φ.affineChartProdMap R Ψ σ τ ≫
        pullback.fst (Φ.finiteFanSchemeToSpec R) (Ψ.finiteFanSchemeToSpec R) =
      pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap R (affineChartRing R Φ.lattice σ.val))))
          (Spec.map (CommRingCat.ofHom (algebraMap R (affineChartRing R Ψ.lattice τ.val)))) ≫
        Φ.affineChartι R σ := by
  simp [affineChartProdMap]

/-- The second projection of the product of two affine chart inclusions is the second local
projection followed by the second chart inclusion. -/
@[reassoc (attr := simp)]
theorem affineChartProdMap_snd (σ : Φ.cones) (τ : Ψ.cones) :
    Φ.affineChartProdMap R Ψ σ τ ≫
        pullback.snd (Φ.finiteFanSchemeToSpec R) (Ψ.finiteFanSchemeToSpec R) =
      pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap R (affineChartRing R Φ.lattice σ.val))))
          (Spec.map (CommRingCat.ofHom (algebraMap R (affineChartRing R Ψ.lattice τ.val)))) ≫
        Ψ.affineChartι R τ := by
  simp [affineChartProdMap]

/-- On the affine chart of a product cone, the global product comparison is the affine product
isomorphism followed by the product of the two chart inclusions. -/
@[reassoc]
theorem affineChartι_comp_finiteFanSchemeProdComparison
    (σ : Φ.cones) (τ : Ψ.cones) :
    (Φ.prod Ψ).affineChartι R (Φ.prodCone Ψ σ τ) ≫
        Φ.finiteFanSchemeProdComparison R Ψ =
      (affineChartProdIso R Φ.lattice Ψ.lattice σ.val τ.val).hom ≫
        Φ.affineChartProdMap R Ψ σ τ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, finiteFanSchemeProdComparison_fst,
      FanHom.affineChartι_prodCone_comp_fst_finiteFanSchemeHom,
      affineChartProdMap_fst, affineChartProdIso_hom_fst_assoc]
  · simp only [Category.assoc, finiteFanSchemeProdComparison_snd,
      FanHom.affineChartι_prodCone_comp_snd_finiteFanSchemeHom,
      affineChartProdMap_snd, affineChartProdIso_hom_snd_assoc]

/-- The product of two affine cone opens is open in the fibre product of the fan schemes. -/
instance isOpenImmersion_affineChartProdMap (σ : Φ.cones) (τ : Ψ.cones) :
    IsOpenImmersion (Φ.affineChartProdMap R Ψ σ τ) := by
  unfold affineChartProdMap
  infer_instance

/-- The product chart is the locus where both projections lie in the respective cone opens. -/
theorem range_affineChartProdMap (σ : Φ.cones) (τ : Ψ.cones) :
    Set.range (Φ.affineChartProdMap R Ψ σ τ) =
      pullback.fst (Φ.finiteFanSchemeToSpec R) (Ψ.finiteFanSchemeToSpec R) ⁻¹'
          Set.range (Φ.affineChartι R σ) ∩
        pullback.snd (Φ.finiteFanSchemeToSpec R) (Ψ.finiteFanSchemeToSpec R) ⁻¹'
          Set.range (Ψ.affineChartι R τ) := by
  unfold affineChartProdMap
  exact Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _

/-- The product affine charts cover the fibre product of the fan schemes. -/
theorem exists_affineChartProdMap_apply_eq
    (x : ↥(pullback (Φ.finiteFanSchemeToSpec R) (Ψ.finiteFanSchemeToSpec R))) :
    ∃ (σ : Φ.cones) (τ : Ψ.cones), ∃ y, Φ.affineChartProdMap R Ψ σ τ y = x := by
  obtain ⟨σ, y, hy⟩ := Φ.exists_affineChartι_apply_eq R
    (pullback.fst (Φ.finiteFanSchemeToSpec R) (Ψ.finiteFanSchemeToSpec R) x)
  obtain ⟨τ, z, hz⟩ := Ψ.exists_affineChartι_apply_eq R
    (pullback.snd (Φ.finiteFanSchemeToSpec R) (Ψ.finiteFanSchemeToSpec R) x)
  have hx : x ∈ Set.range (Φ.affineChartProdMap R Ψ σ τ) := by
    rw [range_affineChartProdMap]
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
  exact ⟨σ, τ, hx⟩

/-- Intersections of product cone opens are computed in each factor. -/
theorem range_affineChartProdMap_inter_range_affineChartProdMap
    (σ σ' : Φ.cones) (τ τ' : Ψ.cones) :
    Set.range (Φ.affineChartProdMap R Ψ σ τ) ∩
        Set.range (Φ.affineChartProdMap R Ψ σ' τ') =
      Set.range (Φ.affineChartProdMap R Ψ (σ ⊓ σ') (τ ⊓ τ')) := by
  simp only [range_affineChartProdMap, ← range_affineChartι_inter,
    Set.preimage_inter]
  exact Set.inter_inter_inter_comm _ _ _ _

/-- On each product-cone chart the comparison is an open immersion. -/
instance isOpenImmersion_affineChartι_comp_finiteFanSchemeProdComparison
    (σ : Φ.cones) (τ : Ψ.cones) :
    IsOpenImmersion ((Φ.prod Ψ).affineChartι R (Φ.prodCone Ψ σ τ) ≫
      Φ.finiteFanSchemeProdComparison R Ψ) := by
  rw [affineChartι_comp_finiteFanSchemeProdComparison]
  infer_instance

/-- The image of a product-cone chart under the comparison is the corresponding product open. -/
theorem range_affineChartι_comp_finiteFanSchemeProdComparison (σ : Φ.cones) (τ : Ψ.cones) :
    Set.range ((Φ.prod Ψ).affineChartι R (Φ.prodCone Ψ σ τ) ≫
        Φ.finiteFanSchemeProdComparison R Ψ) = Set.range (Φ.affineChartProdMap R Ψ σ τ) := by
  have hs : Function.Surjective
      (affineChartProdIso R Φ.lattice Ψ.lattice σ.val τ.val).hom := by
    simpa only [Scheme.coe_homeoOfIso] using
      (Scheme.homeoOfIso (affineChartProdIso R Φ.lattice Ψ.lattice σ.val τ.val)).surjective
  rw [affineChartι_comp_finiteFanSchemeProdComparison, Scheme.Hom.comp_base,
    TopCat.coe_comp, hs.range_comp]

/-- Every point of a product-fan scheme lies in a chart indexed by a pair of factor cones. -/
theorem exists_affineChartι_prodCone_apply_eq (x : ((Φ.prod Ψ).finiteFanScheme R)) :
    ∃ (σ : Φ.cones) (τ : Ψ.cones), ∃ y,
      (Φ.prod Ψ).affineChartι R (Φ.prodCone Ψ σ τ) y = x := by
  obtain ⟨ξ, y, hy⟩ := (Φ.prod Ψ).exists_affineChartι_apply_eq R x
  obtain ⟨σ, τ, rfl⟩ := Φ.exists_prodCone_eq Ψ ξ
  exact ⟨σ, τ, y, hy⟩

private theorem surjective_finiteFanSchemeProdComparison :
    Function.Surjective (Φ.finiteFanSchemeProdComparison R Ψ) := by
  intro x
  obtain ⟨σ, τ, y, hy⟩ := Φ.exists_affineChartProdMap_apply_eq R Ψ x
  have hx : x ∈ Set.range ((Φ.prod Ψ).affineChartι R (Φ.prodCone Ψ σ τ) ≫
      Φ.finiteFanSchemeProdComparison R Ψ) := by
    rw [range_affineChartι_comp_finiteFanSchemeProdComparison]
    exact ⟨y, hy⟩
  obtain ⟨z, hz⟩ := hx
  exact ⟨(Φ.prod Ψ).affineChartι R (Φ.prodCone Ψ σ τ) z, hz⟩

/-- The product comparison is injective. -/
private theorem injective_finiteFanSchemeProdComparison :
    Function.Injective (Φ.finiteFanSchemeProdComparison R Ψ) := by
  -- Representatives with the same image meet in the chart of the factor intersections.
  intro x y hxy
  obtain ⟨σ, τ, a, rfl⟩ := Φ.exists_affineChartι_prodCone_apply_eq R Ψ x
  obtain ⟨σ', τ', b, rfl⟩ := Φ.exists_affineChartι_prodCone_apply_eq R Ψ y
  let c := Φ.finiteFanSchemeProdComparison R Ψ
  let A := (Φ.prod Ψ).affineChartι R (Φ.prodCone Ψ σ τ)
  let B := (Φ.prod Ψ).affineChartι R (Φ.prodCone Ψ σ' τ')
  let C := (Φ.prod Ψ).affineChartι R (Φ.prodCone Ψ (σ ⊓ σ') (τ ⊓ τ'))
  have hq : c (A a) ∈ Set.range (Φ.affineChartProdMap R Ψ (σ ⊓ σ') (τ ⊓ τ')) := by
    rw [← range_affineChartProdMap_inter_range_affineChartProdMap]
    constructor
    · rw [← range_affineChartι_comp_finiteFanSchemeProdComparison]
      exact ⟨a, rfl⟩
    · rw [← range_affineChartι_comp_finiteFanSchemeProdComparison]
      exact ⟨b, hxy.symm⟩
  obtain ⟨z, hz⟩ : c (A a) ∈ Set.range (C ≫ c) := by
    rwa [range_affineChartι_comp_finiteFanSchemeProdComparison]
  have hzin : C z ∈ Set.range A ∩ Set.range B := by
    rw [(Φ.prod Ψ).range_affineChartι_inter R,
      prodCone_inf_prodCone]
    exact ⟨z, rfl⟩
  obtain ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ := hzin
  have ha : a' = a := (A ≫ c).isOpenEmbedding.injective <| by
    simp only [Scheme.Hom.comp_apply]
    rw [ha']
    exact hz
  have hb : b' = b := (B ≫ c).isOpenEmbedding.injective <| by
    simp only [Scheme.Hom.comp_apply]
    rw [hb']
    exact hz.trans hxy
  exact (ha ▸ ha').trans (hb ▸ hb').symm

/-- The scheme of a product fan is the fibre product of the fan schemes over `Spec R`. -/
instance isIso_finiteFanSchemeProdComparison : IsIso (Φ.finiteFanSchemeProdComparison R Ψ) := by
  have : Surjective (Φ.finiteFanSchemeProdComparison R Ψ) :=
    ⟨Φ.surjective_finiteFanSchemeProdComparison R Ψ⟩
  have : IsOpenImmersion (Φ.finiteFanSchemeProdComparison R Ψ) := by
    apply IsOpenImmersion.of_openCover_source (Φ.finiteFanSchemeProdComparison R Ψ)
      ((Φ.prod Ψ).affineChartOpenCover R) (Φ.injective_finiteFanSchemeProdComparison R Ψ)
    intro ξ
    let cone : (Φ.prod Ψ).cones := ξ
    change IsOpenImmersion (((Φ.prod Ψ).affineChartOpenCover R).f cone ≫ _)
    obtain ⟨σ, τ, hcone⟩ := Φ.exists_prodCone_eq Ψ cone
    rw [affineChartOpenCover_f, ← hcone]
    exact Φ.isOpenImmersion_affineChartι_comp_finiteFanSchemeProdComparison R Ψ σ τ
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩

/-- The canonical isomorphism from the product-fan scheme to the fibre product of its factors. -/
noncomputable def finiteFanSchemeProdIso : ((Φ.prod Ψ).finiteFanScheme R) ≅
    pullback (Φ.finiteFanSchemeToSpec R) (Ψ.finiteFanSchemeToSpec R) :=
  asIso (Φ.finiteFanSchemeProdComparison R Ψ)

@[simp]
theorem finiteFanSchemeProdIso_hom :
    (Φ.finiteFanSchemeProdIso R Ψ).hom = Φ.finiteFanSchemeProdComparison R Ψ :=
  (rfl)

@[simp]
theorem finiteFanSchemeProdIso_inv :
    (Φ.finiteFanSchemeProdIso R Ψ).inv = inv (Φ.finiteFanSchemeProdComparison R Ψ) :=
  (rfl)

/-- The algebraic maps of the fan projections exhibit the product-fan scheme as a fibre
product over `Spec R`. -/
theorem isPullback_fst_snd_finiteFanSchemeHom :
    IsPullback ((FanHom.fst Φ Ψ).finiteFanSchemeHom R) ((FanHom.snd Φ Ψ).finiteFanSchemeHom R)
      (Φ.finiteFanSchemeToSpec R) (Ψ.finiteFanSchemeToSpec R) := by
  refine IsPullback.of_iso_pullback ?_ (Φ.finiteFanSchemeProdIso R Ψ) ?_ ?_
  · exact ⟨by
      rw [← Φ.finiteFanSchemeProdComparison_fst R Ψ, ← Φ.finiteFanSchemeProdComparison_snd R Ψ,
        Category.assoc, Category.assoc, pullback.condition]⟩
  · exact Φ.finiteFanSchemeProdComparison_fst R Ψ
  · exact Φ.finiteFanSchemeProdComparison_snd R Ψ

end Fan

end TauCeti.Toric

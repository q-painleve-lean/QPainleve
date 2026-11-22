/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.CharacterTorus.Scheme
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Product

/-!
# Products of character schemes

The character scheme of a product lattice is the fiber product of the two character schemes
over the coefficient ring. The inclusions of the summands induce the two projections.
The comparison uses Tau Ceti's `MonoidAlgebra.prodTensorBialgEquiv` in additive coordinates
and Mathlib's `pullbackSpecIso`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace QPainleve.CharacterTorus

universe u

variable (k A N : Type u) [CommRing k] [AddCommGroup A] [AddCommGroup N]

private def prodCoordinates :
    AddMonoidAlgebra k (A × N) ≃ₐ[k] AddMonoidAlgebra k A ⊗[k] AddMonoidAlgebra k N :=
  ((AddMonoidAlgebra.toMultiplicativeAlgEquiv k k (A × N)).trans
    (MonoidAlgebra.domCongr k k (MulEquiv.prodMultiplicative A N))).trans
    ((TauCeti.MonoidAlgebra.prodTensorBialgEquiv k
      (G := Multiplicative A) (H := Multiplicative N)).toAlgEquiv.trans
      (Algebra.TensorProduct.congr (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k A).symm
        (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k N).symm))

private theorem prodCoordinates_single (a : A) (n : N) (r : k) :
    prodCoordinates k A N (AddMonoidAlgebra.single (a, n) r) =
      AddMonoidAlgebra.single a (1 : k) ⊗ₜ[k] AddMonoidAlgebra.single n r := by
  simp [prodCoordinates]
  simp only [← AddMonoidAlgebra.toMultiplicativeAlgEquiv_single (R := k) a (1 : k),
    ← AddMonoidAlgebra.toMultiplicativeAlgEquiv_single (R := k) n r, AlgEquiv.symm_apply_apply]

/-- The affine product over the base is the character scheme of the product lattice. -/
def prodIso :
    pullback (structureMap k A) (structureMap k N) ≅ scheme k (A × N) :=
  pullbackSpecIso k (AddMonoidAlgebra k A) (AddMonoidAlgebra k N) ≪≫
    Scheme.Spec.mapIso (prodCoordinates k A N).toRingEquiv.toCommRingCatIso.op

private theorem prodIso_hom :
    (prodIso k A N).hom =
      (pullbackSpecIso k (AddMonoidAlgebra k A) (AddMonoidAlgebra k N)).hom ≫
        Spec.map (CommRingCat.ofHom (prodCoordinates k A N).toRingHom) :=
  rfl

/-- The first projection of the product pulls back exponents along the first inclusion. -/
@[reassoc (attr := simp)]
theorem prodIso_hom_fst :
    (prodIso k A N).hom ≫ map k (AddMonoidHom.inl A N) = pullback.fst _ _ := by
  rw [← Spec.map_preimage (map k (AddMonoidHom.inl A N)),
    ← CommRingCat.ofHom_hom (Spec.preimage _), preimage_map]
  rw [prodIso_hom, Category.assoc, ← Spec.map_comp, ← pullbackSpecIso_hom_fst]
  congr 2
  have h :
      (prodCoordinates k A N).toAlgHom.comp
          (AddMonoidAlgebra.mapDomainAlgHom k k (AddMonoidHom.inl A N)) =
        Algebra.TensorProduct.includeLeft := by
    apply AddMonoidAlgebra.algHom_ext
    · intro a
      simp [prodCoordinates_single, AddMonoidAlgebra.one_def]
    · exact Subsingleton.elim _ _
  exact congrArg (fun f ↦ CommRingCat.ofHom f.toRingHom) h

/-- The second projection of the product pulls back exponents along the second inclusion. -/
@[reassoc (attr := simp)]
theorem prodIso_hom_snd :
    (prodIso k A N).hom ≫ map k (AddMonoidHom.inr A N) = pullback.snd _ _ := by
  rw [← Spec.map_preimage (map k (AddMonoidHom.inr A N)),
    ← CommRingCat.ofHom_hom (Spec.preimage _), preimage_map]
  rw [prodIso_hom, Category.assoc, ← Spec.map_comp, ← pullbackSpecIso_hom_snd]
  congr 2
  have h :
      (prodCoordinates k A N).toAlgHom.comp
          (AddMonoidAlgebra.mapDomainAlgHom k k (AddMonoidHom.inr A N)) =
        Algebra.TensorProduct.includeRight := by
    apply AddMonoidAlgebra.algHom_ext
    · intro a
      simp [prodCoordinates_single, AddMonoidAlgebra.one_def]
    · exact Subsingleton.elim _ _
  exact congrArg (fun f ↦ CommRingCat.ofHom f.toRingHom) h

/-- The first projection is dominant, with a section given by the identity of the second
character scheme. -/
instance isDominant_map_inl : IsDominant (map k (AddMonoidHom.inl A N)) := by
  have : IsDominant (map k (AddMonoidHom.fst A N) ≫ map k (AddMonoidHom.inl A N)) := by
    rw [← map_comp, AddMonoidHom.fst_comp_inl, map_id]
    infer_instance
  exact IsDominant.of_comp (map k (AddMonoidHom.fst A N)) _

/-- The second projection is dominant, with a section given by the identity of the first
character scheme. -/
instance isDominant_map_inr : IsDominant (map k (AddMonoidHom.inr A N)) := by
  have : IsDominant (map k (AddMonoidHom.snd A N) ≫ map k (AddMonoidHom.inr A N)) := by
    rw [← map_comp, AddMonoidHom.snd_comp_inr, map_id]
    infer_instance
  exact IsDominant.of_comp (map k (AddMonoidHom.snd A N)) _

end QPainleve.CharacterTorus

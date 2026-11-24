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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti DiagonalizableGroup
open scoped TensorProduct

namespace QPainleve.CharacterTorus

universe u

variable (k A N : Type u) [CommRing k] [AddCommGroup A] [AddCommGroup N]

local notation "L" B => FGCommGrpCat.of (Multiplicative B)
local notation "D" B => groupScheme k (L B)
local notation "Dmap" f => groupSchemeMap k (FGCommGrpCat.ofHom (AddMonoidHom.toMultiplicative f))

private def prodCoordinates :
    MonoidAlgebra k (Multiplicative (A × N)) ≃ₐ[k]
      MonoidAlgebra k (Multiplicative A) ⊗[k] MonoidAlgebra k (Multiplicative N) :=
  (MonoidAlgebra.domCongr k k (MulEquiv.prodMultiplicative A N)).trans
    (TauCeti.MonoidAlgebra.prodTensorBialgEquiv k).toAlgEquiv

private theorem prodCoordinates_inl :
    (prodCoordinates k A N).toAlgHom.comp
      (MonoidAlgebra.mapDomainAlgHom k k (AddMonoidHom.inl A N).toMultiplicative) =
        Algebra.TensorProduct.includeLeft := by
  apply MonoidAlgebra.algHom_ext
  · intro a
    simp [prodCoordinates, TauCeti.MonoidAlgebra.prodTensorBialgEquiv_single, MonoidAlgebra.one_def]
  · exact Subsingleton.elim _ _

private theorem prodCoordinates_inr :
    (prodCoordinates k A N).toAlgHom.comp
      (MonoidAlgebra.mapDomainAlgHom k k (AddMonoidHom.inr A N).toMultiplicative) =
        Algebra.TensorProduct.includeRight := by
  apply MonoidAlgebra.algHom_ext
  · intro a
    simp [prodCoordinates, TauCeti.MonoidAlgebra.prodTensorBialgEquiv_single, MonoidAlgebra.one_def]
  · exact Subsingleton.elim _ _

variable [IsAddFG A] [IsAddFG N]

private theorem isPullback_prod :
    IsPullback (Dmap (AddMonoidHom.inl A N)).hom.hom.left (Dmap (AddMonoidHom.inr A N)).hom.hom.left
      (D A).X.hom (D N).X.hom := by
  let R := MonoidAlgebra k (Multiplicative A)
  let S := MonoidAlgebra k (Multiplicative N)
  let e := pullbackSpecIso k R S ≪≫
    Scheme.Spec.mapIso (prodCoordinates k A N).toRingEquiv.toCommRingCatIso.op
  have he : e.hom = (pullbackSpecIso k R S).hom ≫
      Spec.map (CommRingCat.ofHom (prodCoordinates k A N).toRingHom) := rfl
  refine (IsPullback.of_hasPullback (Spec.algebraMap k R) (Spec.algebraMap k S)).of_iso'
    (eqToIso (groupScheme_X_left k (L (A × N))) ≪≫ e.symm)
    (eqToIso (groupScheme_X_left k (L A))) (eqToIso (groupScheme_X_left k (L N)))
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc,
      groupSchemeMap_comp_toSpec, FGCommGrpCat.hom_hom_ofHom]
    congr 1
    rw [Iso.inv_comp_eq, he, Category.assoc, ← Spec.map_comp, ← pullbackSpecIso_hom_fst]
    congr 2
    exact congrArg (fun f ↦ CommRingCat.ofHom f.toRingHom) (prodCoordinates_inl k A N).symm
  · simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc,
      groupSchemeMap_comp_toSpec, FGCommGrpCat.hom_hom_ofHom]
    congr 1
    rw [Iso.inv_comp_eq, he, Category.assoc, ← Spec.map_comp, ← pullbackSpecIso_hom_snd]
    congr 2
    exact congrArg (fun f ↦ CommRingCat.ofHom f.toRingHom) (prodCoordinates_inr k A N).symm
  · simpa only [Iso.refl_hom, Category.comp_id, eqToIso.hom] using (groupScheme_X_hom k (L A)).symm
  · simpa only [Iso.refl_hom, Category.comp_id, eqToIso.hom] using (groupScheme_X_hom k (L N)).symm

/-- The fiber product of two diagonalizable group schemes is the scheme for the product
of the character lattices, with restrictions along the two inclusions as projections. -/
def prodIso : pullback (D A).X.hom (D N).X.hom ≅ (D (A × N)).X.left :=
  (isPullback_prod k A N).isoPullback.symm

/-- The first projection of the product pulls back along the first inclusion of lattices. -/
@[reassoc (attr := simp)]
theorem prodIso_hom_fst :
    (prodIso k A N).hom ≫ (Dmap (AddMonoidHom.inl A N)).hom.hom.left = pullback.fst _ _ :=
  (isPullback_prod k A N).isoPullback_inv_fst

/-- The second projection of the product pulls back along the second inclusion of lattices. -/
@[reassoc (attr := simp)]
theorem prodIso_hom_snd :
    (prodIso k A N).hom ≫ (Dmap (AddMonoidHom.inr A N)).hom.hom.left = pullback.snd _ _ :=
  (isPullback_prod k A N).isoPullback_inv_snd

/-- The first projection is smooth when the second factor is smooth over the base. -/
theorem smooth_map_inl [Smooth (D N).X.hom] :
    Smooth (Dmap (AddMonoidHom.inl A N)).hom.hom.left := by
  have h : Smooth ((prodIso k A N).inv ≫ pullback.fst (D A).X.hom (D N).X.hom) :=
    inferInstance
  simpa only [← prodIso_hom_fst, Iso.inv_hom_id_assoc] using h

/-- The first projection is dominant. -/
instance isDominant_map_inl : IsDominant (Dmap (AddMonoidHom.inl A N)).hom.hom.left :=
  isDominant_groupSchemeMap k _ (fun _ _ h ↦ congrArg (fun x : A × N ↦ x.1) h)

/-- The second projection is dominant. -/
instance isDominant_map_inr : IsDominant (Dmap (AddMonoidHom.inr A N)).hom.hom.left :=
  isDominant_groupSchemeMap k _ (fun _ _ h ↦ congrArg (fun x : A × N ↦ x.2) h)

end QPainleve.CharacterTorus

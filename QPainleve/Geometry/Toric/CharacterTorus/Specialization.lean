/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.CharacterTorus.Evaluation

import QPainleve.Algebra.MonoidAlgebra.MonomialEquiv

/-!
# Specializing the center of a character torus

Insert a fixed center character into the center factor of the joint torus.
On the coordinate ring, this specializes the center exponent to a scalar
and keeps the other exponent as a character.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Multiplicative TauCeti.DiagonalizableGroup
open TauCeti (FGCommGrpCat)
open scoped CategoryTheory.MonObj

namespace QPainleve.CharacterTorus

universe u

variable {k A N : Type u} [CommRing k] [AddCommGroup A] [AddCommGroup N]

private def centerSliceAlgHom (c : Multiplicative A →* kˣ) :
    AddMonoidAlgebra k (A × N) →ₐ[k] AddMonoidAlgebra k N :=
  (AddMonoidAlgebra.mapDomainAlgHom k k (AddMonoidHom.snd A N)).comp
    (AddMonoidAlgebra.monomialAlgEquiv
      (c.comp (AddMonoidHom.fst A N).toMultiplicative) (AddEquiv.refl _)).toAlgHom

private theorem centerSliceAlgHom_single (c : Multiplicative A →* kˣ) (a : A) (x : N) (r : k) :
    centerSliceAlgHom c (AddMonoidAlgebra.single (a, x) r) =
      AddMonoidAlgebra.single x ((c (ofAdd a) : k) * r) := by
  simp [centerSliceAlgHom, AddMonoidAlgebra.mapDomainAlgHom]

/-- The slice of the joint torus at a fixed center character. -/
def affineCenterSlice (c : Multiplicative A →* kˣ) : scheme k N ⟶ scheme k (A × N) :=
  Spec.map (CommRingCat.ofHom (centerSliceAlgHom c).toRingHom)

/-- Pullback to the center slice evaluates the first exponent at the center. -/
@[simp]
theorem preimage_affineCenterSlice_single (c : Multiplicative A →* kˣ)
    (a : A) (x : N) (r : k) :
    (Spec.preimage (affineCenterSlice (N := N) c)).hom (AddMonoidAlgebra.single (a, x) r) =
      AddMonoidAlgebra.single x ((c (ofAdd a) : k) * r) := by
  rw [affineCenterSlice, Spec.preimage_map, CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe]
  exact centerSliceAlgHom_single c a x r

/-- The center projection of a slice is constant at its specified point. -/
@[reassoc (attr := simp)]
theorem affineCenterSlice_comp_map_inl (c : Multiplicative A →* kˣ) :
    affineCenterSlice (N := N) c ≫ map k (AddMonoidHom.inl A N) =
      structureMap k N ≫ ((pointsEquiv k A).symm c).val := by
  apply Spec.preimage_injective
  rw [Spec.preimage_comp, Spec.preimage_comp, pointsEquiv_symm_apply_val,
    Spec.preimage_map, Spec.preimage_map, affineCenterSlice, Spec.preimage_map]
  apply CommRingCat.hom_ext
  simp only [CommRingCat.hom_comp, preimage_map, CommRingCat.hom_ofHom]
  let f := (centerSliceAlgHom (N := N) c).comp
    (AddMonoidAlgebra.mapDomainAlgHom k k (AddMonoidHom.inl A N))
  let g := (Algebra.ofId k (AddMonoidAlgebra k N)).comp
    ((point c).comp (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k A).toAlgHom)
  suffices f = g by exact congrArg AlgHom.toRingHom this
  apply AddMonoidAlgebra.algHom_ext
  · intro a
    simp [f, g, AddMonoidAlgebra.mapDomainAlgHom, centerSliceAlgHom_single]
  · exact Subsingleton.elim _ _

/-- The charge projection of a center slice is the identity. -/
@[reassoc (attr := simp)]
theorem affineCenterSlice_comp_map_inr (c : Multiplicative A →* kˣ) :
    affineCenterSlice (N := N) c ≫ map k (AddMonoidHom.inr A N) = 𝟙 _ := by
  apply Spec.preimage_injective
  rw [Spec.preimage_comp, Spec.preimage_id, affineCenterSlice, Spec.preimage_map]
  apply CommRingCat.hom_ext
  simp only [CommRingCat.hom_comp, preimage_map, CommRingCat.hom_ofHom, CommRingCat.hom_id]
  let f := (centerSliceAlgHom (N := N) c).comp
    (AddMonoidAlgebra.mapDomainAlgHom k k (AddMonoidHom.inr A N))
  suffices f = AlgHom.id k _ by exact congrArg AlgHom.toRingHom this
  apply AddMonoidAlgebra.algHom_ext
  · intro a
    simp [f, centerSliceAlgHom_single, AddMonoidAlgebra.mapDomainAlgHom]
  · exact Subsingleton.elim _ _

section Diagonalizable

variable [IsAddFG A] [IsAddFG N]

local notation "G" B:arg => FGCommGrpCat.of (Multiplicative B)
local notation "D" B:arg => groupScheme k (G B)
local notation "τ" B:arg =>
  (diagonalizableGroupSchemeIso k (G B) : Over.left (Grp.X (D B)) ≅ scheme k B)
local notation "S" => Spec (CommRingCat.of k)

/-- The center insertion into the product of diagonalizable groups agrees with the
additive-coordinate slice at its character. -/
@[reassoc]
theorem pullback_lift_prodIso_comp_diagonalizableGroupSchemeIso
    (c : S ⟶ (D A).X.left) (hc : c ≫ (D A).X.hom = 𝟙 S) :
    let point : (S).asOver S ⟶ (D A).X :=
      Over.homMk c (hc.trans (Spec.map_id (CommRingCat.of k)).symm)
    let slice : scheme k N ⟶ scheme k (A × N) :=
      affineCenterSlice
        (schemePointsMulEquiv (R := k) (A := k) (G A) point : Multiplicative A →* kˣ)
    pullback.lift (f := (D A).X.hom) (g := (D N).X.hom)
        ((D N).X.hom ≫ c) (𝟙 _) (by simp [hc]) ≫
      (prodIso k A N).hom ≫ (τ (A × N)).hom =
    (τ N).hom ≫ slice := by
  intro point slice
  let e := prodIso k A N ≪≫ τ (A × N)
  let χ : Multiplicative A →* kˣ := schemePointsMulEquiv (R := k) (A := k) (G A) point
  let q := (τ N).hom ≫ slice
  have hfst : e.inv ≫ pullback.fst (D A).X.hom (D N).X.hom =
      map k (AddMonoidHom.inl A N) ≫ (τ A).inv := by
    apply (cancel_mono (τ A).hom).mp
    simp only [e, Iso.trans_inv, Category.assoc, ← prodIso_hom_fst,
      Iso.inv_hom_id_assoc, groupSchemeMap_comp_diagonalizableGroupSchemeIso]
    erw [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have hsnd : e.inv ≫ pullback.snd (D A).X.hom (D N).X.hom =
      map k (AddMonoidHom.inr A N) ≫ (τ N).inv := by
    apply (cancel_mono (τ N).hom).mp
    simp only [e, Iso.trans_inv, Category.assoc, ← prodIso_hom_snd,
      Iso.inv_hom_id_assoc, groupSchemeMap_comp_diagonalizableGroupSchemeIso]
    erw [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have hpoint : ((pointsEquiv k A).symm χ).val ≫ (τ A).inv = c := by
    rw [← schemePointsMulEquiv_symm_comp_diagonalizableGroupSchemeIso,
      MulEquiv.symm_apply_apply]
    erw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  suffices h : q ≫ e.inv =
      pullback.lift ((D N).X.hom ≫ c) (𝟙 _) (by simp [hc]) by
    exact (e.comp_inv_eq.mp h).symm
  apply pullback.hom_ext
  · erw [pullback.lift_fst, Category.assoc, hfst]
    dsimp only [q, slice]
    erw [Category.assoc, affineCenterSlice_comp_map_inl_assoc, hpoint,
      diagonalizableGroupSchemeIso_hom_structureMap_assoc]
  · erw [pullback.lift_snd, Category.assoc, hsnd]
    dsimp only [q, slice]
    erw [Category.assoc, affineCenterSlice_comp_map_inr_assoc, Iso.hom_inv_id]

/-- Fixed-center evaluation in diagonalizable group schemes is the affine evaluation
restricted to the slice at that center. -/
theorem pullback_lift_comp_evaluation_comp_diagonalizableGroupSchemeIso
    (v : A →+ N) (c : S ⟶ (D A).X.left) (hc : c ≫ (D A).X.hom = 𝟙 S) :
    let point : (S).asOver S ⟶ (D A).X :=
      Over.homMk c (hc.trans (Spec.map_id (CommRingCat.of k)).symm)
    let slice : scheme k N ⟶ scheme k (A × N) :=
      affineCenterSlice
        (schemePointsMulEquiv (R := k) (A := k) (G A) point : Multiplicative A →* kˣ)
    pullback.lift (f := (D A).X.hom) (g := (D N).X.hom)
        ((D N).X.hom ≫ c) (𝟙 _) (by simp [hc]) ≫
      (prodIso k A N).hom ≫ (evaluation k v).hom.hom.left ≫ (τ A).hom =
    (τ N).hom ≫ slice ≫ affineEvaluation k v := by
  intro point slice
  erw [evaluation_comp_diagonalizableGroupSchemeIso,
    pullback_lift_prodIso_comp_diagonalizableGroupSchemeIso_assoc c hc, Category.assoc]

end Diagonalizable

end QPainleve.CharacterTorus

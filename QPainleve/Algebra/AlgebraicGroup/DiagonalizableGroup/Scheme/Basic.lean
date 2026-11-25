/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Basic

import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Points
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Morphisms of diagonalizable group schemes

The structure morphism and the morphism induced by a character-group homomorphism are
obtained by applying `Spec` to the corresponding group-algebra maps. An injective
character-group homomorphism induces a dominant scheme morphism.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.DiagonalizableGroup

universe u

variable (k : Type u) [CommRing k] {G H : FGCommGrpCat.{u}}

/-- In the group-algebra presentation, the structure morphism is induced by the coefficient
map. -/
@[reassoc]
theorem groupScheme_X_hom (G : FGCommGrpCat.{u}) :
    (groupScheme k G).X.hom =
      eqToHom (groupScheme_X_left k G) ≫ Spec.algebraMap k (MonoidAlgebra k G) := by
  have h : (groupScheme k G).X =
      (Spec (CommRingCat.of (MonoidAlgebra k G))).asOver (Spec (CommRingCat.of k)) :=
    (congrArg (fun X ↦ X.X) (groupScheme_def k G)).trans
      (congrArg (fun X ↦ X.X) (hopfSpec_obj_eq_asOver k (coordinateRing k G).obj))
  have hw := Over.w (eqToHom h)
  rw [Over.eqToHom_left] at hw
  exact hw.symm

/-- The pullback on group algebras of a diagonalizable group morphism transports exponents
along the character-group homomorphism. -/
@[reassoc]
theorem groupSchemeMap_comp_toSpec (f : G ⟶ H) :
    (groupSchemeMap k f).hom.hom.left ≫ eqToHom (groupScheme_X_left k G) =
      eqToHom (groupScheme_X_left k H) ≫ Spec.map
        (CommRingCat.ofHom (MonoidAlgebra.mapDomainAlgHom k k f.hom.hom).toRingHom) := by
  rw [groupSchemeMap_def]
  simp only [Grp.comp_hom_hom, Over.comp_left,
    eqToHom_hom_hom_left, Category.assoc, eqToHom_trans]
  rfl

/-- An injective homomorphism of character groups induces a dominant morphism of schemes. -/
theorem isDominant_groupSchemeMap (f : G ⟶ H) (hf : Function.Injective f.hom.hom) :
    IsDominant (groupSchemeMap k f).hom.hom.left := by
  apply IsDominant.of_comp_of_isOpenImmersion _ (eqToHom (groupScheme_X_left k G)) (H := ?_)
  rw [groupSchemeMap_comp_toSpec]
  have : IsDominant (Spec.map
      (CommRingCat.ofHom (MonoidAlgebra.mapDomainAlgHom k k f.hom.hom).toRingHom)) := by
    rw [isDominant_iff]
    -- On affine spectra the underlying map is contraction of prime ideals.
    change DenseRange (PrimeSpectrum.comap
      (MonoidAlgebra.mapDomainAlgHom k k f.hom.hom).toRingHom)
    exact RingHom.denseRange_comap_of_injective _ (MonoidAlgebra.mapDomain_injective hf)
  infer_instance

variable {k}

local notation "S" => Spec (CommRingCat.of k)

/-- The point of a diagonalizable group over its coordinate ring corresponding to the
identity algebra map. -/
noncomputable def groupSchemeUniversalPoint (G : FGCommGrpCat.{u}) :
    (Spec (CommRingCat.of (MonoidAlgebra k G))).asOver S ⟶ (groupScheme k G).X :=
  (groupSchemePointsMulEquiv G).symm (WithConv.toConv (AlgHom.id k (MonoidAlgebra k G)))

instance (G : FGCommGrpCat.{u}) : IsIso (groupSchemeUniversalPoint (k := k) G) := by
  suffices IsIso ((Over.forget S).map (groupSchemeUniversalPoint (k := k) G)) from
    isIso_of_reflects_iso _ (Over.forget S)
  rw [Over.forget_map, groupSchemeUniversalPoint, groupSchemePointsMulEquiv_symm_apply_left]
  simp only [AlgHom.id_toRingHom, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  exact (eqToIso (groupScheme_X_left k G).symm).isIso_hom

/-- Pointwise multiplication of character homomorphisms induces pointwise multiplication
of the corresponding morphisms of diagonalizable schemes. -/
theorem groupSchemeMap_mul (f g : G →* H) :
    (groupSchemeMap k (FGCommGrpCat.ofHom (f * g))).hom.hom =
      (groupSchemeMap k (FGCommGrpCat.ofHom f)).hom.hom *
        (groupSchemeMap k (FGCommGrpCat.ofHom g)).hom.hom := by
  let p := groupSchemeUniversalPoint (k := k) H
  apply (cancel_epi p).mp
  apply (schemePointsMulEquiv G).injective
  simp only [MonObj.comp_mul, map_mul, schemePointsMulEquiv_groupSchemeMap,
    FGCommGrpCat.hom_hom_ofHom]
  exact MonoidHom.ext fun a ↦ map_mul (schemePointsMulEquiv H p) (f a) (g a)

end TauCeti.DiagonalizableGroup

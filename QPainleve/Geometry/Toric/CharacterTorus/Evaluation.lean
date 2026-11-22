/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Prod
public import QPainleve.Geometry.Toric.CharacterTorus.Product

/-!
# Evaluation with variable centers

Given a charge map `v : A →+ N`, evaluation sends a center character `c` and a torus
character `z` to the character `a ↦ c(a) * z(v(a))`. In the product model of the
source this is the morphism induced by the graph of `v` on exponents. Setting `z = 1`
gives a section. For free lattices over a field, evaluation remains dominant when the
centers vary in any nonempty open.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti DiagonalizableGroup
open scoped CategoryTheory.MonObj

namespace QPainleve.CharacterTorus

universe u

variable {A N : Type u} [AddCommGroup A] [AddCommGroup N]

/-- Evaluation in additive coordinates, also for character groups that are not finitely
generated. -/
def affineEvaluation (k : Type u) [CommRing k] (v : A →+ N) :
    scheme k (A × N) ⟶ scheme k A :=
  map k ((AddMonoidHom.id A).prod v)

instance isDominant_affineEvaluation (k : Type u) [CommRing k] (v : A →+ N) :
    IsDominant (affineEvaluation k v) := by
  have : IsDominant (map k (AddMonoidHom.fst A N) ≫ affineEvaluation k v) := by
    rw [affineEvaluation, ← map_comp, AddMonoidHom.fst_comp_prod, map_id]
    infer_instance
  exact IsDominant.of_comp (map k (AddMonoidHom.fst A N)) _

/-- Evaluation in additive coordinates pulls a monomial back along the graph of the charge map. -/
@[simp]
theorem affineRationalPullback_affineEvaluation_monomial (k : Type u) [Field k]
    [Module.Free ℤ A] [Module.Free ℤ N] (v : A →+ N) (a : A) :
    affineRationalPullback k (affineEvaluation k v).toRationalMap
        (monomial k (Multiplicative.ofAdd a)) =
      monomial k (Multiplicative.ofAdd (a, v a)) := by
  unfold affineEvaluation
  rw [affineRationalPullback_map ((AddMonoidHom.id A).prod v)
    (fun _ _ h ↦ congrArg Prod.fst h)]
  exact functionFieldMap_monomial k _ _ a

variable [IsAddFG A] [IsAddFG N]

section CommRing

variable (k : Type u) [CommRing k]

local notation "L" B => FGCommGrpCat.of (Multiplicative B)
local notation:max "D" B:arg => groupScheme k (L B)
local notation "Dmap" f => groupSchemeMap k (FGCommGrpCat.ofHom (AddMonoidHom.toMultiplicative f))
local notation "π₁" => Dmap (AddMonoidHom.inl A N)

/-- Evaluation of independent characters using a variable center and a charge map.
The domain models the product of the center and charge tori via `prodIso`. -/
def evaluation (v : A →+ N) : (D (A × N)) ⟶ (D A) :=
  Dmap ((AddMonoidHom.id A).prod v)

/-- On points evaluation multiplies the center character by the pullback of the charge
character. -/
@[reassoc (attr := simp)]
theorem schemePointsMulEquiv_symm_comp_evaluation (v : A →+ N)
    (c : Multiplicative A →* kˣ) (z : Multiplicative N →* kˣ) :
    ((schemePointsMulEquiv (R := k) (A := k) (L (A × N))).symm
        (c.comp (AddMonoidHom.fst A N).toMultiplicative) *
      (schemePointsMulEquiv (R := k) (A := k) (L (A × N))).symm
        (z.comp (AddMonoidHom.snd A N).toMultiplicative)) ≫ (evaluation k v).hom.hom =
      (schemePointsMulEquiv (R := k) (A := k) (L A)).symm c *
        (schemePointsMulEquiv (R := k) (A := k) (L A)).symm (z.comp v.toMultiplicative) := by
  apply (schemePointsMulEquiv (R := k) (A := k) (L A)).injective
  rw [← map_mul, ← map_mul, evaluation, schemePointsMulEquiv_groupSchemeMap,
    MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  ext a
  rfl

/-- Setting the charge character to the identity recovers the center. -/
@[reassoc (attr := simp)]
theorem section_evaluation (v : A →+ N) :
    (Dmap (AddMonoidHom.fst A N)).hom.hom.left ≫ (evaluation k v).hom.hom.left =
      𝟙 (D A).X.left := by
  rw [evaluation, ← Over.comp_left, ← Grp.comp_hom_hom, ← groupSchemeMap_comp]
  have hcomp : (FGCommGrpCat.ofHom ((AddMonoidHom.id A).prod v).toMultiplicative) ≫
      FGCommGrpCat.ofHom (AddMonoidHom.fst A N).toMultiplicative = 𝟙 (L A) := by
    apply FGCommGrpCat.hom_ext
    simp only [FGCommGrpCat.hom_hom_comp, FGCommGrpCat.hom_hom_ofHom, FGCommGrpCat.hom_hom_id]
    exact congrArg AddMonoidHom.toMultiplicative
      (AddMonoidHom.fst_comp_prod (AddMonoidHom.id A) v)
  rw [hcomp]
  simp

/-- Evaluation is dominant since it has a section obtained by setting the charge character
to the identity. -/
instance isDominant_evaluation (v : A →+ N) : IsDominant (evaluation k v).hom.hom.left := by
  have : IsDominant ((Dmap (AddMonoidHom.fst A N)).hom.hom.left ≫
      (evaluation k v).hom.hom.left) := by
    rw [section_evaluation]
    infer_instance
  exact IsDominant.of_comp (Dmap (AddMonoidHom.fst A N)).hom.hom.left _

/-- Evaluation is dominant on the inverse image of any nonempty open of the center torus. -/
theorem isDominant_evaluation_on_center_open
    [PreirreducibleSpace (groupScheme k (FGCommGrpCat.of (Multiplicative (A × N)))).X.left]
    (v : A →+ N) (U : (D A).X.left.Opens) [Nonempty U] :
    IsDominant (((π₁).hom.hom.left ⁻¹ᵁ U).ι ≫ (evaluation k v).hom.hom.left) := by
  let V := (π₁).hom.hom.left ⁻¹ᵁ U
  have hV : Nonempty V := inferInstanceAs (Nonempty ((π₁).hom.hom.left ⁻¹ᵁ U))
  have : IsDominant V.ι := Opens.isDominant_ι (V.isOpen.dense (Set.nonempty_coe_sort.mp hV))
  exact inferInstanceAs (IsDominant (V.ι ≫ (evaluation k v).hom.hom.left))

/-- Equality after evaluating on a nonempty center open detects equality of the original
rational maps on the independent variables. -/
theorem comp_evaluation_on_center_open_eq_iff
    [IsIntegral (groupScheme k (FGCommGrpCat.of (Multiplicative (A × N)))).X.left]
    [IsIntegral (D A).X.left] (v : A →+ N) (U : (D A).X.left.Opens) [Nonempty U]
    {Z : Scheme.{u}} (f g : (D A).X.left ⤏ Z) :
    let e := ((π₁).hom.hom.left ⁻¹ᵁ U).ι ≫ (evaluation k v).hom.hom.left
    let : IsDominant e := isDominant_evaluation_on_center_open k v U
    e.toRationalMap.comp f = e.toRationalMap.comp g ↔ f = g := by
  dsimp only
  have := isDominant_evaluation_on_center_open k v U
  exact (Scheme.RationalMap.comp_left_injective _).eq_iff

end CommRing

variable (k : Type u) [Field k] [Module.Free ℤ A] [Module.Free ℤ N]

/-- Evaluation pulls a monomial of exponent `a` back to the joint center and charge
monomial of exponent `(a, v a)`. -/
@[simp]
theorem rationalPullback_evaluation_monomial (v : A →+ N) (a : A) :
    rationalPullback k (evaluation k v).hom.hom.left.toRationalMap
        (monomial k (Multiplicative.ofAdd a)) =
      monomial k (Multiplicative.ofAdd (a, v a)) := by
  unfold evaluation
  rw [rationalPullback_groupSchemeMap ((AddMonoidHom.id A).prod v)
    (fun _ _ h ↦ congrArg Prod.fst h)]
  exact functionFieldMap_monomial k _ _ a

end QPainleve.CharacterTorus

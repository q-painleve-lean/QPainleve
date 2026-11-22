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

open AlgebraicGeometry CategoryTheory

namespace QPainleve.CharacterTorus

universe u

variable {A N : Type u} [AddCommGroup A] [AddCommGroup N]

section CommRing

variable (k : Type u) [CommRing k]

/-- Evaluation of independent characters using a variable center and a charge map.
The domain models the product of the center and charge tori via `prodIso`. -/
def evaluation (v : A →+ N) : scheme k (A × N) ⟶ scheme k A :=
  map k ((AddMonoidHom.id A).prod v)

/-- On points evaluation multiplies the center character by the pullback of the charge
character. -/
@[reassoc (attr := simp)]
theorem pointsEquiv_symm_comp_evaluation (v : A →+ N)
    (c : Multiplicative A →* kˣ) (z : Multiplicative N →* kˣ) :
    ((pointsEquiv k (A × N)).symm
      ((c.comp (AddMonoidHom.fst A N).toMultiplicative) *
        (z.comp (AddMonoidHom.snd A N).toMultiplicative))).val ≫ evaluation k v =
      ((pointsEquiv k A).symm (c * z.comp v.toMultiplicative)).val := by
  rw [evaluation, pointsEquiv_symm_comp_map]
  congr 2

/-- Setting the charge character to the identity recovers the center. -/
@[reassoc (attr := simp)]
theorem section_evaluation (v : A →+ N) :
    map k (AddMonoidHom.fst A N) ≫ evaluation k v = 𝟙 (scheme k A) := by
  rw [evaluation, ← map_comp, AddMonoidHom.fst_comp_prod, map_id]

/-- Evaluation is dominant since it has a section obtained by setting the charge character
to the identity. -/
instance isDominant_evaluation (v : A →+ N) : IsDominant (evaluation k v) := by
  have : IsDominant (map k (AddMonoidHom.fst A N) ≫ evaluation k v) := by
    rw [section_evaluation]
    infer_instance
  exact IsDominant.of_comp (map k (AddMonoidHom.fst A N)) _

/-- Evaluation is dominant on the inverse image of any nonempty open of the center torus. -/
theorem isDominant_evaluation_on_center_open [PreirreducibleSpace (scheme k (A × N))]
    (v : A →+ N) (U : (scheme k A).Opens) [Nonempty U] :
    IsDominant ((map k (AddMonoidHom.inl A N) ⁻¹ᵁ U).ι ≫ evaluation k v) := by
  let V := map k (AddMonoidHom.inl A N) ⁻¹ᵁ U
  have hV : Nonempty V := inferInstanceAs (Nonempty (map k (AddMonoidHom.inl A N) ⁻¹ᵁ U))
  have : IsDominant V.ι := Opens.isDominant_ι (V.isOpen.dense (Set.nonempty_coe_sort.mp hV))
  exact inferInstanceAs (IsDominant (V.ι ≫ evaluation k v))

/-- Equality after evaluating on a nonempty center open detects equality of the original
rational maps on the independent variables. -/
theorem comp_evaluation_on_center_open_eq_iff [IsIntegral (scheme k (A × N))]
    [IsIntegral (scheme k A)] (v : A →+ N) (U : (scheme k A).Opens) [Nonempty U]
    {Z : Scheme.{u}} (f g : (scheme k A) ⤏ Z) :
    let e := (map k (AddMonoidHom.inl A N) ⁻¹ᵁ U).ι ≫ evaluation k v
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
    rationalPullback k (evaluation k v).toRationalMap (monomial k (Multiplicative.ofAdd a)) =
      monomial k (Multiplicative.ofAdd (a, v a)) := by
  unfold evaluation
  rw [rationalPullback_map ((AddMonoidHom.id A).prod v)
    (fun _ _ h ↦ congrArg Prod.fst h)]
  exact functionFieldMap_monomial k _ _ a

end QPainleve.CharacterTorus

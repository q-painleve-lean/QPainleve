/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.CharacterTorus.Scheme
public import TauCeti.CategoryTheory.Monoidal.Grp.Translation
import QPainleve.Algebra.AlgebraicGroup.Hopf.SchemeTranslation
import QPainleve.Algebra.MonoidAlgebra.MonomialEquiv
import TauCeti.Algebra.Group.UniqueProds.TorsionFree

/-!
# Isomorphisms and translations of character tori

A split torus isomorphism over the base field is a lattice isomorphism followed by translation
by a base-valued point. The pullback combines exponent transport with multiplication by the
point character. The relative spectrum construction uses Mathlib's `algSpec` and the
translation comparison uses Tau Ceti's `leftTranslation` on the relative spectrum.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open AddMonoidAlgebra TauCeti

namespace QPainleve.CharacterTorus

universe u

variable {k A B C : Type u} [CommRing k] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

private def specIsoEquiv :
    (AddMonoidAlgebra k A ≃ₐ[k] AddMonoidAlgebra k B) ≃
      ((scheme k B).asOver (Spec (CommRingCat.of k)) ≅
        (scheme k A).asOver (Spec (CommRingCat.of k))) :=
  CommAlgCat.isoEquivAlgEquiv.symm.trans <|
    (isoOpEquiv _ _).symm.trans (algSpec.fullyFaithful (R := CommRingCat.of k)).isoEquiv

/-- A character twist and exponent change induce an isomorphism of tori over the base. -/
def monomialIso (χ : Multiplicative A →* kˣ) (e : A ≃+ B) :
    (scheme k B).asOver (Spec (CommRingCat.of k)) ≅
      (scheme k A).asOver (Spec (CommRingCat.of k)) :=
  specIsoEquiv (monomialAlgEquiv χ e)

private theorem monomialIso_hom_left (χ : Multiplicative A →* kˣ) (e : A ≃+ B) :
    (monomialIso χ e).hom.left =
      Spec.map (CommRingCat.ofHom (monomialAlgEquiv χ e).toAlgHom.toRingHom) := rfl

/-- The pullback of a monomial multiplies its coefficient by the character value
and transports its exponent along the lattice isomorphism. -/
@[simp]
theorem preimage_monomialIso_hom_single (χ : Multiplicative A →* kˣ) (e : A ≃+ B) (a : A) (r : k) :
    (Spec.preimage (monomialIso χ e).hom.left).hom (single a r) =
      single (e a) ((χ (.ofAdd a) : k) * r) := by
  rw [monomialIso_hom_left, Spec.preimage_map]
  exact monomialAlgEquiv_single χ e a r

/-- Taking the trivial character gives the usual lattice-induced isomorphism. -/
@[simp]
theorem monomialIso_one_hom_left (e : A ≃+ B) :
    (monomialIso (1 : Multiplicative A →* kˣ) e).hom.left = (mapIso k e).hom := by
  apply Spec.preimage_injective
  rw [monomialIso_hom_left, monomialAlgEquiv_one, Spec.preimage_map, mapIso_hom]
  exact CommRingCat.hom_ext (preimage_map k e.toAddMonoidHom).symm

/-- Composition is contravariant in the lattice isomorphisms and pulls the second
character back along the first exponent change. -/
theorem monomialIso_trans (χ : Multiplicative A →* kˣ) (ψ : Multiplicative B →* kˣ)
    (e : A ≃+ B) (f : B ≃+ C) :
    monomialIso ψ f ≪≫ monomialIso χ e =
      monomialIso (χ * ψ.comp e.toAddMonoidHom.toMultiplicative) (e.trans f) := by
  have h := ((algSpec (CommRingCat.of k)).mapIso_trans
    (CommAlgCat.isoMk (monomialAlgEquiv ψ f)).op
    (CommAlgCat.isoMk (monomialAlgEquiv χ e)).op).symm
  calc
    _ = specIsoEquiv ((monomialAlgEquiv χ e).trans (monomialAlgEquiv ψ f)) := h
    _ = _ := congrArg specIsoEquiv (monomialAlgEquiv_trans χ ψ e f)

/-- The inverse uses the inverse lattice map and the transported inverse character. -/
@[simp]
theorem monomialIso_symm (χ : Multiplicative A →* kˣ) (e : A ≃+ B) :
    (monomialIso χ e).symm =
      monomialIso (χ⁻¹.comp e.symm.toAddMonoidHom.toMultiplicative) e.symm := by
  rw [monomialIso, monomialIso, ← monomialAlgEquiv_symm]
  rfl

open scoped MonObj in
/-- With the identity lattice map, the monomial isomorphism is left translation by the
point whose character is `χ`. -/
theorem monomialIso_refl (χ : Multiplicative A →* kˣ) :
    monomialIso χ (AddEquiv.refl A) =
      leftTranslation (Over.homMk ((pointsEquiv k A).symm χ).val
        ((pointsEquiv k A).symm χ).property :
          𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ (scheme k A).asOver _) := by
  let S := Spec (CommRingCat.of k)
  let p := (DiagonalizableGroup.point χ).comp (toMultiplicativeAlgEquiv k k A).toAlgHom
  let x : 𝟙_ (Over S) ⟶ (scheme k A).asOver S :=
    Over.homMk ((pointsEquiv k A).symm χ).val ((pointsEquiv k A).symm χ).property
  have h := specMap_eq_mul_of_groupLike_basis (AddMonoidAlgebra.basis A k)
    (fun a ↦ by simp) p (monomialAlgEquiv χ (AddEquiv.refl A)).toAlgHom
    (fun a ↦ by simp [p, smul_single]) x (pointsEquiv_symm_apply_val k A χ)
  apply Iso.ext
  rw [leftTranslation_hom, ← h]
  exact Over.OverMorphism.ext (monomialIso_hom_left χ (AddEquiv.refl A))

/-- The isomorphism is the lattice-induced isomorphism followed by translation at its target. -/
theorem monomialIso_eq_map_trans (χ : Multiplicative A →* kˣ) (e : A ≃+ B) :
    monomialIso χ e =
      monomialIso (1 : Multiplicative A →* kˣ) e ≪≫ monomialIso χ (AddEquiv.refl A) := by
  rw [monomialIso_trans, MonoidHom.one_comp]
  exact (congrArg (fun ψ ↦ monomialIso ψ e) (mul_one χ)).symm

section Classification

variable [IsDomain k] [Module.Free ℤ A] [Module.Free ℤ B]

local instance {G : Type*} [AddCommGroup G] [Module.Free ℤ G] : HasUniqueDiv G :=
  .of_isTorsionFree ℤ G

/-- Every isomorphism over the base between split tori has a unique translating character
and exponent lattice isomorphism. -/
theorem existsUnique_monomialIso
    (g : (scheme k B).asOver (Spec (CommRingCat.of k)) ≅
      (scheme k A).asOver (Spec (CommRingCat.of k))) :
    ∃! p : (Multiplicative A →* kˣ) × (A ≃+ B), monomialIso p.1 p.2 = g := by
  obtain ⟨p, hp, huniq⟩ := existsUnique_monomialAlgEquiv (specIsoEquiv.symm g)
  have map_eq (q : (Multiplicative A →* kˣ) × (A ≃+ B)) :
      monomialIso q.1 q.2 = g ↔ monomialAlgEquiv q.1 q.2 = specIsoEquiv.symm g :=
    specIsoEquiv.eq_symm_apply.symm
  exact ⟨p, (map_eq p).2 hp, fun q hq ↦ huniq q ((map_eq q).1 hq)⟩

end Classification

end QPainleve.CharacterTorus

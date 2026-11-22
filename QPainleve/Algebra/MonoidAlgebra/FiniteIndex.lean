/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import TauCeti.Algebra.Group.UniqueProds.TorsionFree
public import TauCeti.Algebra.MonoidAlgebra.CharacterTwist

import TauCeti.Algebra.MonoidAlgebra.CosetBasis

/-!
# Finite-index inclusions of torus function fields

The characters of a finite quotient `G ⧸ H` act on `k[G]` by translating the
torus. If the field contains enough roots of unity, the fixed ring is precisely
the image of `k[H]`. For torsion-free `G`, this identifies the automorphisms of
the corresponding function field extension and computes its degree.

The translation action uses Tau Ceti's `MonoidAlgebra.charTwist`. Mathlib's
finite abelian duality separates the quotient classes, and
`IsGaloisGroup.to_isFractionRing` transfers the fixed-ring computation to fields.
The degree calculation uses Tau Ceti's group-algebra coset basis.
-/

public noncomputable section

namespace MonoidAlgebra

variable (k : Type*) {G : Type*} [CommGroup G] (H : Subgroup G)

section Ring

variable [CommSemiring k]

/-- A character of the quotient acts by multiplying each monomial by its value on the
exponent's quotient class. -/
def quotientCharacterTwist : ((G ⧸ H) →* kˣ) →* (MonoidAlgebra k G ≃ₐ[k] MonoidAlgebra k G) where
  toFun χ := charTwist (χ.comp (QuotientGroup.mk' H))
  map_one' := charTwist_one
  map_mul' χ ψ := AlgEquiv.ext fun f ↦ (charTwist_charTwist
    (χ.comp (QuotientGroup.mk' H)) (ψ.comp (QuotientGroup.mk' H)) f).symm

/-- On a monomial, the twist scales the coefficient by the value of the character. -/
@[simp] theorem quotientCharacterTwist_single (χ : (G ⧸ H) →* kˣ) (g : G) (a : k) :
    quotientCharacterTwist k H χ (single g a) =
      single g ((χ (QuotientGroup.mk' H g) : k) * a) :=
  charTwist_single _ _ _

/-- The coefficient at an exponent is scaled by the value on its quotient class. -/
@[simp] theorem coeff_quotientCharacterTwist (χ : (G ⧸ H) →* kˣ) (f : MonoidAlgebra k G) (g : G) :
    (quotientCharacterTwist k H χ f).coeff g =
      (χ (QuotientGroup.mk' H g) : k) * f.coeff g :=
  coeff_charTwist _ _ _

/-- Quotient characters act on the group algebra via their twists. -/
@[instance_reducible]
def quotientCharacterAction : MulSemiringAction ((G ⧸ H) →* kˣ) (MonoidAlgebra k G) :=
  MulSemiringAction.compHom _ (quotientCharacterTwist k H)

/-- The scalar action of a quotient character is its twist on the group algebra. -/
@[simp] theorem quotientCharacterAction_smul (χ : (G ⧸ H) →* kˣ) (f : MonoidAlgebra k G) :
    let := quotientCharacterAction k H
    χ • f = quotientCharacterTwist k H χ f :=
  (rfl)

variable [IsDomain k] [Finite (G ⧸ H)] [HasEnoughRootsOfUnity k (Monoid.exponent (G ⧸ H))]

/-- When characters separate the quotient classes, the elements fixed by every twist are
exactly the image of the subgroup algebra. -/
theorem forall_quotientCharacterTwist_eq_self_iff (f : MonoidAlgebra k G) :
    (∀ χ : (G ⧸ H) →* kˣ, quotientCharacterTwist k H χ f = f) ↔
      f ∈ Set.range (mapDomainRingHom k H.subtype) := by
  classical
  constructor
  · intro h
    have hs : ↑f.coeff.support ⊆ Set.range (H.subtype : H → G) := by
      intro g hg
      have hcoeff : f.coeff g ≠ 0 := Finsupp.mem_support_iff.mp hg
      have hchar (χ : (G ⧸ H) →* kˣ) : χ (QuotientGroup.mk' H g) = 1 := by
        apply Units.ext
        rw [Units.val_one]
        apply mul_right_cancel₀ hcoeff
        simpa only [coeff_quotientCharacterTwist, one_mul] using
          congrArg (fun x : MonoidAlgebra k G ↦ x.coeff g) (h χ)
      have hq : QuotientGroup.mk' H g = 1 :=
        (CommGroup.forall_apply_eq_apply_iff (G ⧸ H) (M := k)).mp
          (fun χ ↦ (hchar χ).trans (map_one χ).symm)
      exact ⟨⟨g, (QuotientGroup.eq_one_iff g).mp hq⟩, rfl⟩
    exact ⟨comapDomain H.subtype Subtype.val_injective f,
      mapDomain_comapDomain hs Subtype.val_injective⟩
  · rintro ⟨f, rfl⟩ χ
    induction f using induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add, hf, hg]
    | single g a =>
      have hg : QuotientGroup.mk' H (g : G) = 1 := (QuotientGroup.eq_one_iff _).mpr g.property
      simp [mapDomainRingHom_apply, hg]

/-- The character group of the quotient acts faithfully with the subgroup algebra as
its fixed ring. -/
theorem isGaloisGroup_quotientCharacterAction :
    let := (mapDomainRingHom k H.subtype).toAlgebra
    let := quotientCharacterAction k H
    IsGaloisGroup ((G ⧸ H) →* kˣ) (MonoidAlgebra k H) (MonoidAlgebra k G) := by
  let := (mapDomainRingHom k H.subtype).toAlgebra
  let := quotientCharacterAction k H
  refine ⟨⟨fun {χ ψ} h ↦ ?_⟩, ⟨fun χ a f ↦ ?_⟩, ⟨fun f hf ↦ ?_⟩⟩
  · apply MonoidHom.ext
    intro q
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective H q
    apply Units.ext
    have he := congrArg (fun f : MonoidAlgebra k G ↦ f.coeff g) (h (single g 1))
    simpa [quotientCharacterAction_smul, hg] using he
  · have hf := (forall_quotientCharacterTwist_eq_self_iff k H _).mpr ⟨a, rfl⟩ χ
    simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, smul_mul',
      quotientCharacterAction_smul] using
      congrArg (· * (χ • f)) hf
  · exact (forall_quotientCharacterTwist_eq_self_iff k H f).mp hf

end Ring

section FractionField

variable [Field k] [HasUniqueRoots G]

local notation "BaseRing" => MonoidAlgebra k H
local notation "CoverRing" => MonoidAlgebra k G
local notation "BaseField" => FractionRing (MonoidAlgebra k H)
local notation "CoverField" => FractionRing (MonoidAlgebra k G)

/-- The inclusion of subgroup algebras induces an algebra structure on their fraction fields. -/
@[implicit_reducible]
def subgroupFractionAlgebra : Algebra BaseField CoverField :=
  (IsFractionRing.map (j := mapDomainRingHom k H.subtype)
    (mapDomain_injective Subtype.val_injective)).toAlgebra

attribute [local instance] subgroupFractionAlgebra

/-- The inclusion of function fields agrees with the inclusion of the coordinate rings. -/
@[simp] theorem algebraMap_subgroupFractionAlgebra (f : BaseRing) :
    algebraMap BaseField CoverField (algebraMap BaseRing BaseField f) =
      algebraMap CoverRing CoverField (mapDomainRingHom k H.subtype f) := by
  exact IsLocalization.map_eq (M := nonZeroDivisors BaseRing) (T := nonZeroDivisors CoverRing)
    (g := mapDomainRingHom k H.subtype)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (mapDomain_injective Subtype.val_injective)) f

/-- The subgroup algebra acts through the inclusion of exponents. -/
local instance subgroupAlgebra : Algebra BaseRing CoverRing :=
  (mapDomainRingHom k H.subtype).toAlgebra

/-- The induced fraction-field map is compatible with the subgroup coordinate algebra. -/
local instance subgroupFractionScalarTower : IsScalarTower BaseRing BaseField CoverField :=
  IsScalarTower.of_algebraMap_eq fun f ↦ (algebraMap_subgroupFractionAlgebra k H f).symm

attribute [local instance] quotientCharacterAction

/-- The quotient character action extends to fractions of the group algebra. -/
local instance quotientCharacterFractionAction : MulSemiringAction ((G ⧸ H) →* kˣ) CoverField :=
  IsFractionRing.mulSemiringAction ((G ⧸ H) →* kˣ) CoverRing CoverField

/-- The finrank of the function-field extension is the subgroup index. -/
theorem finrank_subgroupFractionAlgebra :
    Module.finrank BaseField CoverField = H.index := by
  rw [IsFractionRing.finrank_eq BaseRing BaseField CoverRing CoverField, Subgroup.index_eq_card]
  simpa only [H.range_subtype] using
    Module.finrank_eq_nat_card_basis
      (TauCeti.MonoidAlgebra.basisCosets k H.subtype Subtype.val_injective)

/-- A finite-index inclusion gives a finite extension of function fields. -/
theorem finiteDimensional_subgroupFractionAlgebra [Finite (G ⧸ H)] :
    FiniteDimensional BaseField CoverField := by
  apply FiniteDimensional.of_finrank_pos
  rw [finrank_subgroupFractionAlgebra, Subgroup.index_eq_card]
  exact Nat.card_pos

variable [Finite (G ⧸ H)] [HasEnoughRootsOfUnity k (Monoid.exponent (G ⧸ H))]

omit [HasUniqueRoots G] in
private theorem finite_quotientCharacters : Finite ((G ⧸ H) →* kˣ) :=
  Finite.of_equiv (G ⧸ H) (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
    (G ⧸ H) k).some.symm.toEquiv

private theorem isGaloisGroup_quotientCharacterFraction :
    IsGaloisGroup ((G ⧸ H) →* kˣ) BaseField CoverField := by
  let := finite_quotientCharacters k H
  let := isGaloisGroup_quotientCharacterAction k H
  exact IsGaloisGroup.to_isFractionRing ((G ⧸ H) →* kˣ) BaseRing CoverRing BaseField CoverField

/-- Every automorphism over the subgroup function field is translation by a unique quotient
character. -/
def quotientCharactersMulEquiv :
    ((G ⧸ H) →* kˣ) ≃* (CoverField ≃ₐ[BaseField] CoverField) := by
  letI := finite_quotientCharacters k H
  letI := isGaloisGroup_quotientCharacterFraction k H
  exact IsGaloisGroup.mulEquivAlgEquiv ((G ⧸ H) →* kˣ) BaseField CoverField

/-- The function-field automorphism acts on a Laurent polynomial by the character twist. -/
@[simp] theorem quotientCharactersMulEquiv_algebraMap (χ : (G ⧸ H) →* kˣ)
    (f : CoverRing) :
    quotientCharactersMulEquiv k H χ (algebraMap CoverRing CoverField f) =
      algebraMap CoverRing CoverField (quotientCharacterTwist k H χ f) := by
  rw [quotientCharactersMulEquiv, IsGaloisGroup.mulEquivAlgEquiv_apply_apply]
  exact (algebraMap.smul' (B := CoverRing) (C := CoverField) χ f).symm

/-- An automorphism over the coefficient field that fixes the subgroup monomials acts
on every monomial by a unique character of the quotient. -/
theorem existsUnique_quotient_character_of_fixes_monomials
    (σ : CoverField ≃ₐ[k] CoverField)
    (hσ : ∀ g ∈ H, σ (algebraMap CoverRing CoverField (single g 1)) =
      algebraMap CoverRing CoverField (single g 1)) :
    ∃! χ : (G ⧸ H) →* kˣ, ∀ g : G,
      σ (algebraMap CoverRing CoverField (single g 1)) =
        algebraMap CoverRing CoverField (single g (χ (QuotientGroup.mk' H g) : k)) := by
  have hfix (f : BaseRing) : σ (algebraMap BaseField CoverField (algebraMap BaseRing BaseField f)) =
      algebraMap BaseField CoverField (algebraMap BaseRing BaseField f) := by
    rw [algebraMap_subgroupFractionAlgebra]
    induction f using induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add, hf, hg]
    | single g a =>
      rw [mapDomainRingHom_apply, mapDomain_single, single_eq_algebraMap_mul_of]
      simp only [map_mul, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes, of_apply,
        Subgroup.subtype_apply, hσ _ g.property]
  have hcomm (x : BaseField) :
      σ (algebraMap BaseField CoverField x) = algebraMap BaseField CoverField x := by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective BaseRing x
    simp only [map_div₀, hfix]
  let σ' : CoverField ≃ₐ[BaseField] CoverField :=
    { σ.toRingEquiv with commutes' := hcomm }
  let e := quotientCharactersMulEquiv k H
  have htranslate (g : G) : σ (algebraMap CoverRing CoverField (single g 1)) =
      algebraMap CoverRing CoverField (single g (e.symm σ' (QuotientGroup.mk' H g) : k)) := by
    have he : e (e.symm σ') (algebraMap CoverRing CoverField (single g 1)) =
        algebraMap CoverRing CoverField (quotientCharacterTwist k H (e.symm σ') (single g 1)) :=
      quotientCharactersMulEquiv_algebraMap k H (e.symm σ') (single g 1)
    rw [e.apply_symm_apply, quotientCharacterTwist_single, mul_one] at he
    exact he
  refine ⟨e.symm σ', htranslate, fun χ hχ ↦ MonoidHom.ext fun q ↦ ?_⟩
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective H q
  have hs := (IsFractionRing.injective CoverRing CoverField) ((hχ g).symm.trans (htranslate g))
  apply Units.ext
  simpa [hg] using congrArg (fun f : CoverRing ↦ f.coeff g) hs

/-- The function-field extension is Galois when the characters separate the quotient. -/
theorem isGalois_subgroupFractionAlgebra : IsGalois BaseField CoverField := by
  let := finite_quotientCharacters k H
  let := isGaloisGroup_quotientCharacterFraction k H
  exact IsGaloisGroup.isGalois ((G ⧸ H) →* kˣ) BaseField CoverField

end FractionField

end MonoidAlgebra

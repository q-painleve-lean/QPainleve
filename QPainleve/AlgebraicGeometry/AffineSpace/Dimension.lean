/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.RingTheory.KrullDimension.Polynomial
import TauCeti.AlgebraicGeometry.Birational.KrullDimension
import TauCeti.AlgebraicGeometry.Scheme.FunctionField

/-!
# Dimension and rationality over a field

A scheme locally of finite type over a field that is birational to an affine space
is birational to the affine space indexed by `Fin d`, where `d` is its dimension. Mathlib's
rationality predicate permits an infinite index type, so the finiteness of that type is part of
the proof. We use Tau Ceti's comparison of function fields on affine charts and birational
invariance of Krull dimension.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

namespace AffineSpace

/-- Over a Noetherian ring, the dimension of affine space is the base dimension plus the
extended cardinality of the variable type. -/
theorem topologicalKrullDim_eq (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u) :
    topologicalKrullDim 𝔸(ι; Spec (.of R)) = ringKrullDim R + ENat.card ι := by
  calc
    _ = topologicalKrullDim (PrimeSpectrum (MvPolynomial ι R)) :=
      (SpecIso ι (.of R)).hom.homeomorph.isHomeomorph.topologicalKrullDim_eq
    _ = _ := by
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
        MvPolynomial.ringKrullDim_of_isNoetherianRing]

end AffineSpace

namespace Scheme.BirationalOver

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  [LocallyOfFiniteType f]

/-- A dense open of affine space can be isomorphic over the field to a dense open of an
scheme locally of finite type only if the affine space has finitely many variables. -/
theorem finite_of_affineSpace {ι : Type u} (h : BirationalOver f (𝔸(ι; Spec (.of k)) ↘ _)) :
    Finite ι := by
  let S := Spec (.of k)
  let A := 𝔸(ι; S)
  obtain ⟨e, he⟩ := h
  let : e.source.toScheme.Over S := ⟨e.source.ι ≫ f⟩
  have : Nonempty e.target.toScheme := e.dense_target.nonempty.to_subtype
  have : Nonempty e.source.toScheme := Nonempty.map e.iso.inv ‹Nonempty e.target.toScheme›
  have : LocallyOfFiniteType (e.source.toScheme ↘ S) :=
    inferInstanceAs (LocallyOfFiniteType (e.source.ι ≫ f))
  let g : e.source.toScheme ⟶ A := e.iso.hom ≫ e.target.ι
  have : g.IsOver S := ⟨(Category.assoc _ _ _).trans he⟩
  have : IsOpenImmersion g := inferInstanceAs (IsOpenImmersion (e.iso.hom ≫ e.target.ι))
  have : IsIntegral e.source.toScheme := isIntegral_of_isOpenImmersion g
  have : IsDominant e.target.ι := Opens.isDominant_ι e.dense_target
  have : IsDominant g := inferInstanceAs (IsDominant (e.iso.hom ≫ e.target.ι))
  let R := MvPolynomial ι k
  obtain ⟨E⟩ := Hom.nonempty_functionField_algEquiv_of_isOpenImmersion
    (AffineSpace.SpecIso ι (.of k)).inv (AffineSpace.SpecIso_inv_over (n := ι) (.of k))
    (FractionRing R)
  let φ : R →ₐ[k] e.source.toScheme.functionField :=
    (g.functionFieldAlgHom k).comp (E.symm.toAlgHom.comp (IsScalarTower.toAlgHom k R _))
  have htrdeg := (trdeg_le_of_injective φ <|
    (g.functionFieldAlgHom k).injective.comp <|
      E.symm.injective.comp (IsFractionRing.injective R (FractionRing R))).trans_lt
        (trdeg_lt_aleph0 k e.source.toScheme.functionField)
  rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id] at htrdeg
  exact Cardinal.mk_lt_aleph0_iff.mp htrdeg

/-- For a scheme locally of finite type over a field, a birational affine-space model has
as many variables as the dimension of the scheme. -/
theorem topologicalKrullDim_eq_of_affineSpace {ι : Type u}
    (h : BirationalOver f (𝔸(ι; Spec (.of k)) ↘ _)) :
    topologicalKrullDim X = Nat.card ι := by
  have := h.finite_of_affineSpace
  exact (Birational.topologicalKrullDim_eq_of_locallyOfFiniteType ⟨h.partialIso⟩ f
    (𝔸(ι; Spec (.of k)) ↘ _)).trans (by
      rw [AffineSpace.topologicalKrullDim_eq, ringKrullDim_eq_zero_of_field, zero_add,
        ENat.card_eq_coe_natCard]
      rfl)

end Scheme.BirationalOver

namespace Scheme

/-- For a scheme of dimension `d` locally of finite type over a field, rationality
is equivalent to birationality over the field with affine `d`-space. -/
theorem isRationalOver_iff_birationalOver_affineSpace {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    {d : ℕ} (hd : topologicalKrullDim X = d) :
    IsRationalOver f ↔ BirationalOver f (𝔸(ULift.{u} (Fin d); Spec (.of k)) ↘ _) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨ULift.{u} (Fin d), h⟩⟩
  obtain ⟨ι, hι⟩ := h
  have := hι.finite_of_affineSpace
  have hcard : Nat.card ι = d := by
    exact_mod_cast hι.topologicalKrullDim_eq_of_affineSpace.symm.trans hd
  let e : ι ≃ ULift.{u} (Fin d) := (Finite.equivFinOfCardEq hcard).trans Equiv.ulift.symm
  let S := Spec (.of k)
  let rename : 𝔸(ι; S) ≅ 𝔸(ULift.{u} (Fin d); S) :=
    (AffineSpace.functor.mapIso e.symm.toIso.op).app S
  exact hι.trans (rename.hom.birationalOver _ _ (AffineSpace.reindex_over e.symm S))

end Scheme

end AlgebraicGeometry

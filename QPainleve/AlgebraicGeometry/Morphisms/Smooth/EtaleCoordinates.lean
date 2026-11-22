/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.EtaleCoordinates
import QPainleve.AlgebraicGeometry.Morphisms.Unramified.Fiber
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic

/-!
# Étale coordinates centered at a rational point

On a smooth scheme over a field, an affine étale coordinate neighbourhood can be chosen
so that its fiber over the origin is the specified rational point, scheme-theoretically.
This identifies the point ideal with the pullback of the ideal of the origin, as needed
for local computations on the blowup of the point.

The initial coordinates come from Tau Ceti's
`SmoothOfRelativeDimension.exists_etale_affineSpace`.
-/

public section

open CategoryTheory Limits MvPolynomial

universe u

namespace AlgebraicGeometry.SmoothOfRelativeDimension

variable {k : Type u} [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "P(" n ")" => MvPolynomial (ULift (Fin n)) k
local notation "A(" n ")" => Spec (CommRingCat.of P(n))
local notation "origin(" n ")" => Spec.map (CommRingCat.ofHom (eval (0 : ULift (Fin n) → k)))
local notation "πA(" n ")" => Spec.map (CommRingCat.ofHom (C : k →+* P(n)))

/-- At a rational point of a smooth morphism of relative dimension `n` over a field,
there is an affine étale neighbourhood over affine `n`-space whose fiber over zero is
exactly that point. The pullback describes the scheme structure of the fiber. -/
theorem exists_etale_affineSpace_origin_pullback {X : Scheme.{u}} (π : X ⟶ S) (n : ℕ)
    [SmoothOfRelativeDimension n π] (p : S ⟶ X) (hp : p ≫ π = 𝟙 S) :
    ∃ (U : Scheme.{u}) (j : U ⟶ X) (pU : S ⟶ U) (g : U ⟶ A(n)),
      IsAffine U ∧ IsOpenImmersion j ∧ Etale g ∧ pU ≫ j = p ∧ g ≫ πA(n) = j ≫ π ∧
        IsPullback pU (𝟙 S) g origin(n) := by
  obtain ⟨V, _, hpV, g, _, hg⟩ := exists_etale_affineSpace π n (p (IsLocalRing.closedPoint k))
  have hV : Set.range p ⊆ Set.range V.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y (IsLocalRing.closedPoint k), Scheme.Opens.range_ι]
    exact hpV
  let pV := IsOpenImmersion.lift V.ι p hV
  let e := AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of k)
  let g₀ := g ≫ e.hom
  have : Etale g₀ := inferInstanceAs (Etale (g ≫ e.hom))
  have he : e.inv ≫ 𝔸(ULift (Fin n); S) ↘ S = πA(n) := AffineSpace.SpecIso_inv_over _
  have hg₀ : g₀ ≫ πA(n) = V.ι ≫ π := by
    dsimp only [g₀]
    rw [← he, Category.assoc, Iso.hom_inv_id_assoc, hg]
  -- Translate the image of the chosen point to the origin in polynomial coordinates.
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (pV ≫ g₀)
  let a (i : ULift.{u} (Fin n)) : k := φ (MvPolynomial.X i)
  let t : P(n) ≃ₐ[k] P(n) := AlgEquiv.ofAlgHom
    (aeval fun i ↦ MvPolynomial.X i - C (a i))
    (aeval fun i ↦ MvPolynomial.X i + C (a i))
    (by ext i; simp) (by ext i; simp)
  have htC (r : k) : t (C r) = C r := t.commutes r
  have htX (i : ULift.{u} (Fin n)) : t (MvPolynomial.X i) = MvPolynomial.X i - C (a i) := by
    simp [t]
  let τ := Spec.map (CommRingCat.ofHom t.toRingHom)
  have : IsIso τ := inferInstanceAs (IsIso (Spec.map t.toRingEquiv.toCommRingCatIso.hom))
  have hτ : τ ≫ πA(n) = πA(n) := by
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext htC)
  have hzero : pV ≫ g₀ ≫ τ = origin(n) := by
    have hφC : φ.hom.comp C = RingHom.id k := by
      have h : Spec.map φ ≫ πA(n) = 𝟙 S := by
        rw [hφ, Category.assoc, hg₀, IsOpenImmersion.lift_fac_assoc, hp]
      rw [← Spec.map_comp, ← Spec.map_id, Spec.map_injective.eq_iff] at h
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_id] using
        congrArg CommRingCat.Hom.hom h
    rw [← Category.assoc, ← hφ, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply ringHom_ext'
    · ext r : 1
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
        htC, eval_C, RingHom.id_apply] using RingHom.congr_fun hφC r
    · intro i
      have ha : φ (C (a i)) = a i := RingHom.congr_fun hφC (a i)
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
        htX, map_sub, ha, eval_X, Pi.zero_apply]
      exact sub_self (a i)
  have : IsClosedImmersion origin(n) :=
    IsClosedImmersion.spec_of_surjective _ fun r ↦ ⟨C r, eval_C _⟩
  have : Etale (g₀ ≫ τ) := inferInstance
  -- Shrink the source so the translated fiber consists of the chosen section.
  obtain ⟨U, hU, pU, hpU, hpb⟩ := (g₀ ≫ τ).exists_isAffineOpen_isPullback_of_unramified
    origin(n) pV hzero (IsLocalRing.closedPoint k)
  refine ⟨U.toScheme, U.ι ≫ V.ι, pU, U.ι ≫ g₀ ≫ τ, hU, inferInstance,
    inferInstance, ?_, ?_, hpb⟩
  · rw [← Category.assoc, hpU, IsOpenImmersion.lift_fac]
  · rw [Category.assoc, Category.assoc, hτ, hg₀, Category.assoc]

end AlgebraicGeometry.SmoothOfRelativeDimension

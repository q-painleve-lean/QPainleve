/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import QPainleve.AlgebraicGeometry.Curves.Node.Locus
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import QPainleve.AlgebraicGeometry.Curves.SingularLocus.Stalk
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Syntomic
import QPainleve.AlgebraicGeometry.Modules.Differentials.Stalk
import QPainleve.AlgebraicGeometry.Scheme.ClosedPoint
import QPainleve.RingTheory.Node.Discriminant

/-!
# Nodal points from a tangent discriminant

At a closed point of a Cartier divisor on a smooth surface over a perfect field,
a local equation with nonzero tangent discriminant gives a node. The singular
subscheme has residue-field local ring there. This criterion applies when the
two geometric branches belong to the same irreducible component.

See [Stacks Project, Lemmas 53.20.1 and 53.20.5](https://stacks.math.columbia.edu/tag/0C58)
for the singular-subscheme criterion and the nodal open locus.
-/

public section

open CategoryTheory TopologicalSpace IsLocalRing TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

local notation "S[" K "]" => Spec (CommRingCat.of K)

namespace IdealSheafData.IsEffectiveCartier

variable {X : Scheme.{u}} [X.Over S[k]] [SmoothOfRelativeDimension 2 (X ↘ S[k])]
  {D : X.IdealSheafData}

/-- A Cartier divisor on a smooth surface over a perfect field has a node at a closed
point where its equation in two local parameters has unit tangent discriminant. -/
theorem isNodeAt_of_isUnit_discrim [PerfectField k] (hD : D.IsEffectiveCartier)
    (p : D.subscheme) (hp : IsClosed ({D.subschemeι p} : Set X))
    {x y a b c : X.presheaf.stalk (D.subschemeι p)}
    (hxy : Ideal.span {x, y} = maximalIdeal (X.presheaf.stalk (D.subschemeι p)))
    (hf : D.stalkIdeal (D.subschemeι p) = Ideal.span {a * x ^ 2 + b * x * y + c * y ^ 2})
    (hdisc : IsUnit (discrim a b c)) : (D.subschemeι ≫ (X ↘ S[k])).IsNodeAt p := by
  let s := X ↘ S[k]
  let : D.subscheme.Over S[k] := ⟨D.subschemeι ≫ s⟩
  let : D.subschemeι.IsOver S[k] := ⟨rfl⟩
  have : SyntomicOfRelativeDimension 1 (D.subscheme ↘ S[k]) :=
    hD.syntomicOfRelativeDimension_subschemeι_comp (s := s)
  have : Algebra.EssFiniteType k (D.subscheme.presheaf.stalk p) :=
    D.subscheme.essFiniteType_stalk k p
  let π := D.subschemeι.stalkMapAlgHom (k := k) p
  have hπ : Function.Surjective π := by
    intro b
    obtain ⟨a, ha⟩ := D.subschemeι.stalkMap_surjective p b
    exact ⟨a, (Hom.stalkMapAlgHom_apply _ _ _).trans ha⟩
  have hker : RingHom.ker π = Ideal.span {a * x ^ 2 + b * x * y + c * y ^ 2} := by
    dsimp only [π]
    rw [AlgHom.ker_coe, D.subschemeι.stalkMapAlgHom_toRingHom,
      D.subschemeι.ker_stalkMap_of_isClosedImmersion,
      ker_subschemeι, hf]
  obtain ⟨basis⟩ := X.nonempty_basis_kaehlerDifferential_stalk (k := k) 2 (D.subschemeι p)
  have : Smooth (X ↘ S[k]) := SmoothOfRelativeDimension.smooth 2 _
  have : Module.Finite k (X.residueField (D.subschemeι p)) :=
    X.moduleFinite_residueField_of_isClosed (k := k) hp
  have hsep : Algebra.FormallyUnramified k (X.residueField (D.subschemeι p)) := .of_isSeparable _ _
  have : Algebra.FormallyUnramified k (ResidueField (X.presheaf.stalk (D.subschemeι p))) := hsep
  have hp' : IsClosed ({p} : Set D.subscheme) := by
    have hpre : D.subschemeι ⁻¹' {D.subschemeι p} = {p} := by
      ext q
      simp only [Set.mem_preimage, Set.mem_singleton_iff, D.subschemeι.injective.eq_iff]
    exact hpre ▸ hp.preimage D.subschemeι.continuous
  have := D.subscheme.moduleFinite_residueField_of_isClosed (k := k) hp'
  apply D.subscheme.isNodeAt_of_singularLocus_stalkIdeal_eq_maximalIdeal p
  rw [D.subscheme.singularLocus_stalkIdeal_eq_fittingIdeal p]
  exact (QPainleve.fittingIdeal_eq_maximalIdeal_iff_isUnit_discrim basis π hπ hxy hker rfl).mpr
    hdisc

/-- A nonvanishing discriminant in an affine chart detects a node of a Cartier divisor.
The two affine parameters generate the prime ideal of the closed point. -/
theorem isNodeAt_of_discrim_notMem [PerfectField k] (hD : D.IsEffectiveCartier)
    (p : D.subscheme) (hp : IsClosed ({D.subschemeι p} : Set X))
    (U : X.affineOpens) (hpU : D.subschemeι p ∈ U.val) {x y a b c : Γ(X, U)}
    (hxy : Ideal.span {x, y} = (U.property.primeIdealOf ⟨D.subschemeι p, hpU⟩).asIdeal)
    (hf : D.ideal U = Ideal.span {a * x ^ 2 + b * x * y + c * y ^ 2})
    (hdisc : discrim a b c ∉ (U.property.primeIdealOf ⟨D.subschemeι p, hpU⟩).asIdeal) :
    (D.subschemeι ≫ (X ↘ S[k])).IsNodeAt p := by
  let q := D.subschemeι p
  let J := (U.property.primeIdealOf ⟨q, hpU⟩).asIdeal
  let P := X.presheaf.stalk q
  let g := (X.presheaf.germ U.val q hpU).hom
  let := X.presheaf.algebra_section_stalk ⟨q, hpU⟩
  have hg : algebraMap Γ(X, U) P = g := X.presheaf.stalk_open_algebraMap ⟨q, hpU⟩
  have : IsLocalization.AtPrime P J := U.property.isLocalization_stalk ⟨q, hpU⟩
  have hmax : J.map g = maximalIdeal P :=
    hg ▸ IsLocalization.AtPrime.map_eq_maximalIdeal J P
  apply hD.isNodeAt_of_isUnit_discrim p hp (x := g x) (y := g y)
    (a := g a) (b := g b) (c := g c)
  · have hspan : Ideal.span {x, y} = J := hxy
    rw [← hmax, ← hspan, Ideal.map_span, Set.image_pair]
  · rw [D.stalkIdeal_eq_map U q hpU, hf, Ideal.map_span, Set.image_singleton]
    simp only [map_add, map_mul, map_pow, g]
    rfl
  · have hu := (IsLocalization.AtPrime.isUnit_to_map_iff P J (discrim a b c)).mpr hdisc
    simpa only [hg, discrim, map_sub, map_pow, map_mul, map_ofNat] using hu

end IdealSheafData.IsEffectiveCartier

end AlgebraicGeometry.Scheme

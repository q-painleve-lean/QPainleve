/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import QPainleve.AlgebraicGeometry.Curves.Node.Locus
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import QPainleve.AlgebraicGeometry.Curves.Node.Order
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Syntomic
import QPainleve.AlgebraicGeometry.Modules.Differentials.Stalk
import QPainleve.AlgebraicGeometry.Scheme.ClosedPoint
import QPainleve.RingTheory.Node.Discriminant
import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Etale
import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Smooth
import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
import TauCeti.AlgebraicGeometry.Pullback.Carrier
import TauCeti.AlgebraicGeometry.Scheme.LocalSpectrum

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

open CategoryTheory Limits TopologicalSpace IsLocalRing TauCeti TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (.of k))]

local notation "S[" K "]" => Spec (CommRingCat.of K)

section SingularLocus

variable [SyntomicOfRelativeDimension 1 (C ↘ S[k])]

private theorem exists_nodal_neighbourhood_of_unramified_singularLocus_restriction
    (W : (C.singularLocus k).subscheme.Opens)
    [Unramified (W.ι ≫ (C.singularLocus k).subschemeι ≫ (C ↘ S[k]))] :
    ∃ U : C.Opens, (C.singularLocus k).subschemeι ⁻¹ᵁ U = W ∧
      AtWorstNodalOfRelativeDimensionOne (U.ι ≫ (C ↘ S[k])) := by
  let J := C.singularLocus k
  obtain ⟨V, hV, hpre⟩ := J.subschemeι.isClosedEmbedding.isInducing.isOpen_iff.mp W.isOpen
  let U : C.Opens := ⟨V, hV⟩
  have hW : J.subschemeι ⁻¹ᵁ U = W := SetLike.coe_injective hpre
  refine ⟨U, hW, ?_⟩
  let : U.toScheme.Over S[k] := ⟨U.ι ≫ (C ↘ S[k])⟩
  let : U.ι.IsOver S[k] := ⟨rfl⟩
  have hS : SyntomicOfRelativeDimension 1 (U.toScheme ↘ S[k]) :=
    zero_add 1 ▸ inferInstanceAs (SyntomicOfRelativeDimension (0 + 1) (U.ι ≫ (C ↘ S[k])))
  let : SyntomicOfRelativeDimension 1 (U.ι ≫ (C ↘ S[k])) := hS
  apply (atWorstNodalOfRelativeDimensionOne_iff_of_iso_spec _ (Iso.refl S[k])).mpr
  rw [Iso.refl_hom, Category.comp_id]
  refine AffineAtWorstNodalOfRelativeDimensionOne.mk hS ?_
  let I := U.toScheme.singularLocus k
  let j := I.subschemeMap J U.ι (le_map_iff_comap_le.mpr
    (singularLocus_eq_comap_of_etale (R := k) U.ι).ge)
  have H : IsPullback I.subschemeι j U.ι J.subschemeι :=
    isPullback_singularLocus_subschemeι_of_etale (R := k) U.ι
  have : IsOpenImmersion j := MorphismProperty.of_isPullback (P := @IsOpenImmersion) H inferInstance
  have hr : Set.range j ⊆ Set.range W.ι := by
    rw [Scheme.Pullback.range_snd_of_isPullback H, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι, ← hW]
    exact Set.Subset.rfl
  let g := IsOpenImmersion.lift W.ι j hr
  have : IsOpenImmersion g := IsOpenImmersion.of_comp g W.ι
  rw [← Category.assoc, H.w, ← IsOpenImmersion.lift_fac W.ι j hr]
  simpa only [Category.assoc] using
    (inferInstance : Unramified (g ≫ (W.ι ≫ J.subschemeι ≫ (C ↘ S[k]))))

/-- A point on a syntomic curve over a field is a node if its singular
subscheme has reduced-point stalk there and its residue field is separable over the base. -/
theorem isNodeAt_of_singularLocus_stalkIdeal_eq_maximalIdeal
    (x : C) [Algebra.IsSeparable k (C.residueField x)]
    (hx : (C.singularLocus k).stalkIdeal x = maximalIdeal (C.presheaf.stalk x)) :
    (C ↘ S[k]).IsNodeAt x := by
  let J := C.singularLocus k
  have hxJ : x ∈ J.support :=
    (J.mem_support_iff_stalkIdeal_ne_top x).mpr (hx.symm ▸ Ideal.IsMaximal.ne_top inferInstance)
  have hnot := (C.mem_support_singularLocus_iff_notMem_smoothLocus (R := k) x).mp hxJ
  obtain ⟨z, rfl⟩ := J.range_subschemeι.ge hxJ
  let g := J.subschemeι ≫ (C ↘ S[k])
  let : J.subscheme.Over S[k] := ⟨g⟩
  let : J.subschemeι.IsOver S[k] := ⟨rfl⟩
  let π := J.subschemeι.stalkMapAlgHom (k := k) z
  have hπ : Function.Surjective π := by
    intro b
    obtain ⟨a, ha⟩ := J.subschemeι.stalkMap_surjective z b
    exact ⟨a, (Hom.stalkMapAlgHom_apply _ _ _).trans ha⟩
  have hk : RingHom.ker π = maximalIdeal (C.presheaf.stalk (J.subschemeι z)) := by
    dsimp only [π]
    rw [AlgHom.ker_coe, J.subschemeι.stalkMapAlgHom_toRingHom,
      J.subschemeι.ker_stalkMap_of_isClosedImmersion,
      ker_subschemeι, hx]
  let e : C.residueField (J.subschemeι z) ≃ₐ[k] J.subscheme.presheaf.stalk z :=
    (Ideal.quotientEquivAlgOfEq k hk.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hπ)
  have : Algebra.FormallyUnramified k (C.residueField (J.subschemeι z)) := .of_isSeparable _ _
  have : Algebra.FormallyUnramified k (J.subscheme.presheaf.stalk z) := .of_equiv e
  let t := J.subscheme.fromSpecStalk z
  let w : Spec (J.subscheme.presheaf.stalk z) := closedPoint (J.subscheme.presheaf.stalk z)
  have htcomp : t ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap k (J.subscheme.presheaf.stalk z))) :=
    J.subscheme.fromSpecStalk_comp_over (k := k) z
  have ht : ((t ≫ g).stalkMap w).hom.FormallyUnramified := by
    rw [htcomp]
    have : FormallyUnramified
        (Spec.map (CommRingCat.ofHom (algebraMap k (J.subscheme.presheaf.stalk z)))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.formallyUnramified_algebraMap.mpr inferInstance)
    exact FormallyUnramified.stalkMap _ _
  have hg : (g.stalkMap z).hom.FormallyUnramified := by
    simp only [Scheme.Hom.stalkMap_comp] at ht
    have ht' := (RingHom.FormallyUnramified.respectsIso.cancel_right_isIso _ _).mp ht
    have hw : t w = z := fromSpecStalk_closedPoint
    exact hw ▸ ht'
  obtain ⟨W, hzW, -, hW⟩ := (g.unramifiedAt_iff_stalkMap z).mpr hg
  have : FormallyUnramified (W.ι ≫ J.subschemeι ≫ (C ↘ S[k])) := hW
  have : Unramified (W.ι ≫ J.subschemeι ≫ (C ↘ S[k])) := ⟨⟩
  obtain ⟨U, hUW, hn⟩ := exists_nodal_neighbourhood_of_unramified_singularLocus_restriction W
  have hU : J.subschemeι z ∈ U := (Scheme.Hom.mem_preimage _).mp (hUW.symm ▸ hzW)
  have := hn.syntomic
  let u : U := ⟨_, hU⟩
  apply ((C ↘ S[k]).isNodeAt_comp_iff_of_isOpenImmersion U.ι u).mp
  apply ((U.ι ≫ (C ↘ S[k])).isNodeAt_iff_notMem_smoothLocus hn u).mpr
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  exact hnot

end SingularLocus

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

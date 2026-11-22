/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.ExceptionalFiber
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.EtaleCoordinates
import Mathlib.RingTheory.Regular.Flat
import QPainleve.AlgebraicGeometry.IdealSheaf.Affine
import QPainleve.AlgebraicGeometry.Morphisms.Smooth.EtaleCoordinates
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.RingTheory.MvPolynomial.Ideal
import TauCeti.RingTheory.MvPolynomial.RegularSequence

/-!
# Blowing up a rational point on a smooth surface

Centered étale coordinates give two parameters generating the ideal of a rational
point on an affine neighbourhood in a smooth surface. The pair is regular
in both orders, so the two polynomial charts describe the blowup there.

The fiber computation uses `Scheme.IdealSheafData.isPullback_blowupChart_projectiveLine`,
which identifies the projectivized associated graded ring of a regular pair as in
[The Stacks Project, Lemma 54.3.1](https://stacks.math.columbia.edu/tag/0AGQ).
-/

public section

open CategoryTheory Limits MvPolynomial RingTheory.Sequence
open TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {Y : Scheme.{u}}

local notation "SpecK" => Spec (CommRingCat.of k)
local notation "ι" => ULift (Fin 2)
local notation "P" => MvPolynomial ι k
local notation "q" => Spec.map (CommRingCat.ofHom (eval (0 : ι → k)))

/-- An affine neighbourhood of a rational point of a smooth surface has a pair of parameters
generating the point ideal. Both orders are regular, and the quotient is the coordinate
ring of the given rational point. -/
theorem exists_regular_pair_ker_of_smoothOfRelativeDimension_two (p : SpecK ⟶ Y)
    (π : Y ⟶ SpecK) [SmoothOfRelativeDimension 2 π] (hp : p ≫ π = 𝟙 SpecK) :
    ∃ (U : Y.Opens) (hU : IsAffineOpen U) (a b : Γ(Y, U)),
      RingTheory.Sequence.IsRegular Γ(Y, U) [a, b] ∧
        RingTheory.Sequence.IsRegular Γ(Y, U) [b, a] ∧
        Ideal.ofList [a, b] = p.ker.ideal ⟨U, hU⟩ ∧
          ∃ e : Γ(Y, U) ⧸ p.ker.ideal ⟨U, hU⟩ ≃+* k,
            Spec.map (CommRingCat.ofHom (e.toRingHom.comp (Ideal.Quotient.mk _))) ≫
              hU.fromSpec = p := by
  -- Read the centered fiber square in the coordinate rings of its affine schemes.
  obtain ⟨V, j, pV, g, _, _, _, hpV, _, hg⟩ :=
    SmoothOfRelativeDimension.exists_etale_affineSpace_origin_pullback π 2 p hp
  let U := j.opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange j
  let e := IsOpenImmersion.isoOfRangeEq hU.fromSpec j (by
    rw [hU.range_fromSpec, Scheme.Hom.coe_opensRange])
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (e.hom ≫ g)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (pV ≫ e.inv)
  have hψp : Spec.map ψ ≫ hU.fromSpec = p := by
    rw [hψ, Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac, hpV]
  have hpb : IsPullback (Spec.map ψ) (𝟙 SpecK) (Spec.map φ) q :=
    hg.of_iso' (.refl _) e (.refl _) (.refl _)
      (by simp [hψ]) (by simp) (by simp [hφ]) (by simp)
  have : IsClosedImmersion p := AlgebraicGeometry.isClosedImmersion_of_comp_eq_id π p hp
  have : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ fun r ↦ ⟨C r, eval_C _⟩
  have hI := hU.ideal_ker_eq_of_SpecMap_comp_fromSpec_eq hψp
  rw [← Spec.map_id] at hpb
  have hK := hpb.ker_eq_map_of_SpecMap
  -- The two polynomial variables give regular parameters by étale flatness.
  have : Etale (Spec.map φ) := hφ ▸ (inferInstance : Etale (e.hom ≫ g))
  have hflat : φ.hom.Flat := Flat.SpecMap_iff.mp (inferInstance : Flat (Spec.map φ))
  let : Algebra P Γ(Y, U) := φ.hom.toAlgebra
  have : Module.Flat P Γ(Y, U) := hflat
  let a := φ (MvPolynomial.X (ULift.up 0))
  let b := φ (MvPolynomial.X (ULift.up 1))
  have hreg (i j : ι) (hij : i ≠ j) : IsWeaklyRegular Γ(Y, U)
      [φ (MvPolynomial.X i), φ (MvPolynomial.X j)] := by
    simpa only [List.map_cons, List.map_nil, RingHom.algebraMap_toAlgebra] using
      IsWeaklyRegular.of_flat (S := Γ(Y, U))
        (isWeaklyRegular_map_X (R := k) [i, j] (by simpa using hij))
  have hab : Ideal.ofList [a, b] = p.ker.ideal ⟨U, hU⟩ := by
    rw [Ideal.ofList, hI, hK, CommRingCat.hom_ofHom, ker_eval, Ideal.map_span]
    congr 1
    ext x
    simp [a, b, ← Set.range_comp, Function.comp_def, ULift.exists, Fin.exists_fin_two, eq_comm]
  have hba : Ideal.ofList [b, a] = p.ker.ideal ⟨U, hU⟩ := by
    rw [← hab, Ideal.ofList, Ideal.ofList]
    congr 1
    ext x
    simp [or_comm]
  have hproper : p.ker.ideal ⟨U, hU⟩ ≠ ⊤ := hI ▸ RingHom.ker_ne_top ψ.hom
  refine ⟨U, hU, a, b, ⟨hreg _ _ (by decide), ?_⟩, ⟨hreg _ _ (by decide), ?_⟩, hab, ?_⟩
  · simpa only [Ideal.smul_eq_mul, Ideal.mul_top, hab] using hproper.symm
  · simpa only [Ideal.smul_eq_mul, Ideal.mul_top, hba] using hproper.symm
  -- The structure map supplies a section of the evaluation on coordinate rings.
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (hU.fromSpec ≫ π)
  have hχψ : χ ≫ ψ = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, hχ, ← Category.assoc, hψp, hp, Spec.map_id])
  have hsurj : Function.Surjective ψ.hom := fun r ↦ ⟨χ r, ConcreteCategory.congr_hom hχψ r⟩
  rw [hI]
  refine ⟨ψ.hom.quotientKerEquivOfSurjective hsurj, ?_⟩
  have hquot : CommRingCat.ofHom ((ψ.hom.quotientKerEquivOfSurjective hsurj).toRingHom.comp
      (Ideal.Quotient.mk _)) = ψ :=
    CommRingCat.hom_ext (RingHom.ext (ψ.hom.quotientKerEquivOfSurjective_apply_mk hsurj))
  simpa only [hquot] using hψp

/-- The exceptional closed subscheme of the blowup of a rational point on a smooth surface
is a projective line. Under the isomorphism, the projective line's structure morphism and
its inclusion into the blowup exhibit it as the scheme-theoretic fiber over the point. -/
theorem exists_iso_projectiveLine_exceptional_blowup_ker (p : SpecK ⟶ Y) (π : Y ⟶ SpecK)
    [SmoothOfRelativeDimension 2 π] (hp : p ≫ π = 𝟙 SpecK) :
    let E := p.ker.comap p.ker.blowupToBase
    ∃ e : projectiveLine k ≅ E.subscheme,
      IsPullback (e.hom ≫ E.subschemeι) (projectiveLine k ↘ SpecK) p.ker.blowupToBase p := by
  obtain ⟨U, hU, a, b, hab, _, hI, e, he⟩ :=
    p.exists_regular_pair_ker_of_smoothOfRelativeDimension_two π hp
  let R := Γ(Y, U) ⧸ p.ker.ideal ⟨U, hU⟩
  let : Algebra R k := e.toRingHom.toAlgebra
  have hp' : Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ hU.fromSpec = p := by
    rw [← Category.assoc, ← Spec.map_comp]
    exact he
  have H := (projectiveLine.isPullback_baseChangeProjection R k).paste_horiz
    (p.ker.isPullback_blowupChart_projectiveLine hU hab.toIsWeaklyRegular hI)
  rw [hp'] at H
  have : IsClosedImmersion p := AlgebraicGeometry.isClosedImmersion_of_comp_eq_id π p hp
  let E := p.ker.comap p.ker.blowupToBase
  obtain ⟨i, H⟩ : ∃ i, IsPullback i (projectiveLine k ↘ SpecK) p.ker.blowupToBase p := ⟨_, H⟩
  have hi : IsClosedImmersion i := MorphismProperty.of_isPullback H.flip inferInstance
  have hker : i.ker = E := ker_eq_comap_of_isPullback p H
  let eE : projectiveLine k ≅ E.subscheme :=
    asIso i.toImage ≪≫ eqToIso (congrArg Scheme.IdealSheafData.subscheme hker)
  have heE : eE.hom ≫ E.subschemeι = i := by
    rw [Iso.trans_hom, asIso_hom, eqToIso.hom, Category.assoc,
      ← eqToHom_naturality Scheme.IdealSheafData.subschemeι hker]
    simp
  exact ⟨eE, heE.symm ▸ H⟩

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.SmoothOfRelativeDimension

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}}

/-- The exceptional subscheme of the blowup of the reduced ideal of a closed point on a
smooth surface over an algebraically closed field is a projective line over that point. -/
theorem exists_iso_projectiveLine_exceptional_blowup_closedPoint
    (π : Y ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 π] (x : Y) (hx : IsClosed {x}) :
    letI : Smooth π := SmoothOfRelativeDimension.smooth 2 π
    let I := vanishingIdeal ⟨{x}, hx⟩
    let E := I.comap I.blowupToBase
    ∃ e : projectiveLine k ≅ E.subscheme,
      IsPullback (e.hom ≫ E.subschemeι) (projectiveLine k ↘ Spec (.of k)) I.blowupToBase
        (pointOfClosedPoint π x hx) := by
  dsimp only
  have : Smooth π := SmoothOfRelativeDimension.smooth 2 π
  let p := pointOfClosedPoint π x hx
  have hp : p ≫ π = 𝟙 (Spec (.of k)) := pointOfClosedPoint_comp π x hx
  have : IsClosedImmersion p := AlgebraicGeometry.isClosedImmersion_of_comp_eq_id π p hp
  have hrange : Set.range p = {x} := Set.range_eq_singleton (pointOfClosedPoint_apply π x hx)
  have hsupp : p.ker.support = ⟨{x}, hx⟩ := SetLike.coe_injective (by
    rw [p.support_ker, hrange, hx.closure_eq]
    rfl)
  have hI : p.ker = vanishingIdeal ⟨{x}, hx⟩ := by
    apply le_antisymm
    · rw [← hsupp, vanishingIdeal_support]
      exact le_radical _
    · exact vanishingIdeal_le_ker_of_range_subset p hrange.le
  have H := p.exists_iso_projectiveLine_exceptional_blowup_ker π hp
  dsimp only at H
  rw [hI] at H
  exact H

end AlgebraicGeometry.SmoothOfRelativeDimension

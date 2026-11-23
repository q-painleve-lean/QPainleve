/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.EtaleCoordinates
import Mathlib.RingTheory.Regular.Flat
import QPainleve.AlgebraicGeometry.IdealSheaf.Affine
import QPainleve.AlgebraicGeometry.Morphisms.Unramified.Fiber
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
import TauCeti.RingTheory.MvPolynomial.Ideal
import TauCeti.RingTheory.MvPolynomial.RegularSequence

/-!
# Étale coordinates centered at a rational point

On a smooth scheme over a field, an affine étale coordinate neighbourhood can be chosen
so that its fiber over the origin is the specified rational point, scheme-theoretically.
This identifies the point ideal with the pullback of the ideal of the origin. On a
smooth surface, the two coordinates generate the point ideal and form a regular
sequence in either order.

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

namespace AlgebraicGeometry.Scheme.Hom

open RingTheory.Sequence

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

end AlgebraicGeometry.Scheme.Hom

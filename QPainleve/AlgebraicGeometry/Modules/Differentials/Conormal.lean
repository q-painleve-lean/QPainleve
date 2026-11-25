/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.AlgebraicGeometry.IdealSheaf.Module
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Pullback

import Mathlib.LinearAlgebra.TensorProduct.Quotient
import TauCeti.AlgebraicGeometry.IdealSheaf.Sequence
import TauCeti.AlgebraicGeometry.Modules.Differentials.ClosedImmersion
import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
import TauCeti.RingTheory.Kaehler.Conormal

/-!
# The conormal sequence of a closed subscheme

The first map differentiates a local section of the defining ideal and restricts
the result to the closed subscheme. This is linear by the Leibniz rule because
the section vanishes on the subscheme.

The affine comparison uses the cotangent sequence of the quotient of the
coordinate ring. For a smooth Cartier divisor in a smooth surface, the short
exact sequence gives the adjunction map by taking determinants.

For the sheaf sequence and the smoothness criterion, see
[Stacks, Section 37.63](https://stacks.math.columbia.edu/tag/06BB).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
open Scheme.Modules TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData) (R : Type u) [CommRing R]
  [X.Over (Spec (.of R))]

local notation "i" => I.subschemeι
local notation "Ωₓ" => X.relativeDifferentials R

private def conormalMapAdjointApp (U : X.Opens) :
    Γ(I.sheaf, U) →ₗ[Γ(X, U)] Γ((pushforward i).obj ((pullback i).obj Ωₓ), U) where
  toFun s := (i).pullbackSections Ωₓ U ((X.universalDerivation R).d (I.sheafι.app U s))
  map_add' s t := by
    let d : Γ(X, U) →+ Γ(Ωₓ, U) := (X.universalDerivation R).d
    have h := ((I.sheafι.app U).hom).map_add s t
    have hd : d (I.sheafι.app U (s + t)) = d (I.sheafι.app U s) + d (I.sheafι.app U t) :=
      (congrArg d h).trans (d.map_add _ _)
    exact (congrArg ((i).pullbackSections Ωₓ U) hd).trans (map_add _ _ _)
  map_smul' a s := by
    let x : Γ(X, U) := I.sheafι.app U s
    have hx : (i).app U x = 0 :=
      (I.toPushforwardSubscheme_app _).symm.trans
        (I.subschemeι_app_eq_zero_iff.mpr (I.sheafι_app_mem U s))
    have h : (I.sheafι.app U (a • s) : Γ(X, U)) = a * x :=
      Scheme.Modules.Hom.app_smul I.sheafι (U := U) a s
    let d : Γ(X, U) →+ Γ(Ωₓ, U) := (X.universalDerivation R).d
    let p := (i).pullbackSections Ωₓ U
    -- Scalars on the pushforward act through restriction of functions.
    change p (d (I.sheafι.app U (a • s))) = (i).app U a • p (d x)
    have hd : d (a * x) = a • d x + x • d a :=
      (X.universalDerivation R).d_mul (X := op U) a x
    rw [h, hd, map_add, p.map_smulₛₗ, p.map_smulₛₗ]
    simp [hx]

private def conormalMapAdjoint : I.sheaf ⟶ (pushforward i).obj ((pullback i).obj Ωₓ) where
  val :=
    { app := fun U ↦ ConcreteCategory.ofHom (I.conormalMapAdjointApp R U.unop)
      naturality := fun {U V} f ↦ by
        ext s
        -- Both restriction maps here are the underlying maps of presheaves.
        change (i).pullbackSections Ωₓ V.unop
            ((X.universalDerivation R).d (I.sheafι.app V.unop (I.sheaf.presheaf.map f s))) =
          ((pullback i).obj Ωₓ).presheaf.map ((TopologicalSpace.Opens.map (i).base).map f.unop).op
            ((i).pullbackSections Ωₓ U.unop ((X.universalDerivation R).d (I.sheafι.app U.unop s)))
        symm
        exact (i).pullbackSections_restrict Ωₓ U.unop f.unop _ |>.trans
          (congrArg ((i).pullbackSections Ωₓ V.unop)
            (((X.universalDerivation R).d_map f _).symm.trans
              (congrArg (X.universalDerivation R).d (I.sheafι_app_map f.unop s).symm))) }

/-- The conormal map of a closed subscheme sends the pullback of a local ideal section
to its differential in the restricted ambient cotangent sheaf. -/
def conormalMap : (pullback i).obj I.sheaf ⟶ (pullback i).obj Ωₓ :=
  ((pullbackPushforwardAdjunction i).homEquiv _ _).symm (I.conormalMapAdjoint R)

/-- The conormal map takes the class of a local ideal section to the restricted differential
of its image in the structure sheaf. -/
@[simp]
theorem conormalMap_app_pullbackSections (U : X.Opens) (s : Γ(I.sheaf, U)) :
    (I.conormalMap R).app (i ⁻¹ᵁ U) ((i).pullbackSections I.sheaf U s) =
      (i).pullbackSections Ωₓ U ((X.universalDerivation R).d (I.sheafι.app U s)) := by
  have h := (pullbackPushforwardAdjunction i).homEquiv I.sheaf
    ((pullback i).obj Ωₓ) |>.apply_symm_apply (I.conormalMapAdjoint R)
  rw [Adjunction.homEquiv_unit] at h
  rw [Scheme.Hom.pullbackSections_apply]
  have h' := congrArg (fun f : I.sheaf ⟶ (pushforward i).obj ((pullback i).obj Ωₓ) ↦ f.app U) h
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app] at h'
  exact ConcreteCategory.congr_hom h' s

section Affine

variable (U : X.affineOpens)

local notation3 (prettyPrint := false) "V" => (i ⁻¹ᵁ U.val)
local notation3 (prettyPrint := false) "A" => Γ(X, U.val)
local notation3 (prettyPrint := false) "B" => Γ(I.subscheme, V)
local notation3 (prettyPrint := false) "J" => RingHom.ker (algebraMap A B)

private local instance preimageSectionsAlgebra : Algebra A B :=
  ((i).appLE U.val V le_rfl).hom.toAlgebra
private local instance ambientSectionsBaseAlgebra : Algebra R A :=
  ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
private local instance subschemeSectionsBaseAlgebra : Algebra R B :=
  ((I.subscheme.baseRingToStructurePresheaf R).app (op V)).hom.toAlgebra

private local instance preimageSectionsScalarTower : IsScalarTower R A B :=
  Scheme.Modules.isScalarTower_baseRingToStructurePresheaf_appLE R i U.val V le_rfl

private theorem algebraMap_sections_apply (a : A) : algebraMap A B a = (i).app U.val a := by
  rw [RingHom.algebraMap_toAlgebra, ← Scheme.Hom.app_eq_appLE]

private theorem surjective_algebraMap_sections : Function.Surjective (algebraMap A B) := by
  intro b
  obtain ⟨a, ha⟩ := I.subschemeι_app_surjective U b
  exact ⟨a, (I.algebraMap_sections_apply U a).trans ha⟩

private def idealSectionsEquiv : Γ(I.sheaf, U.val) ≃ₗ[A] J := by
  let f : Γ(I.sheaf, U.val) →ₗ[A] A := ((sectionsFunctor U.val).map I.sheafι).hom
  have hf (s : Γ(I.sheaf, U.val)) : f s ∈ J :=
    RingHom.mem_ker.mpr ((I.algebraMap_sections_apply U (f s)).trans
      ((I.toPushforwardSubscheme_app _).symm.trans
        (I.subschemeι_app_eq_zero_iff.mpr (I.sheafι_app_mem U.val s))))
  refine LinearEquiv.ofBijective (f.codRestrict J hf) ⟨?_, ?_⟩
  · exact fun s t h ↦ I.sheafι_app_injective U.val (congrArg Subtype.val h)
  · intro x
    have hx := (I.algebraMap_sections_apply U x).symm.trans (RingHom.mem_ker.mp x.property)
    have hx' := I.subschemeι_app_eq_zero_iff.mp ((I.toPushforwardSubscheme_app _).trans hx)
    exact ⟨I.sectionMk x.val hx', Subtype.ext (I.sheafι_app_sectionMk _ _)⟩

private def quotientEquivSections : (A ⧸ J) ≃ₗ[A] B :=
  (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B)
    (I.surjective_algebraMap_sections U)).toLinearEquiv

private local instance pullbackIdealSectionsModule : Module A Γ((pullback i).obj I.sheaf, V) :=
  Module.compHom _ (algebraMap A B)
private local instance pullbackIdealSectionsScalarTower :
    IsScalarTower A B Γ((pullback i).obj I.sheaf, V) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

private def affinePullbackIdeal :
    Γ(I.sheaf, U.val) →ₗ[A] Γ((pullback i).obj I.sheaf, V) where
  toFun := (i).pullbackSectionsLE I.sheaf U.val V le_rfl
  map_add' := map_add _
  map_smul' := (i).pullbackSectionsLE I.sheaf U.val V le_rfl |>.map_smulₛₗ

private theorem isBaseChange_affinePullbackIdeal : IsBaseChange B (I.affinePullbackIdeal U) :=
  (i).isBaseChange_pullbackSectionsLE I.sheaf U.property (U.property.preimage i) le_rfl
    (fun _ ↦ rfl) _ (fun _ ↦ rfl)

private def affineConormalEquiv :
    Ideal.Cotangent J ≃ₗ[A] Γ((pullback i).obj I.sheaf, V) :=
  (TensorProduct.quotTensorEquivQuotSMul J J).symm.trans
    ((TensorProduct.congr (I.quotientEquivSections U) (I.idealSectionsEquiv U).symm).trans
      ((I.isBaseChange_affinePullbackIdeal U).equiv.restrictScalars A))

private theorem affineConormalEquiv_toCotangent (s : Γ(I.sheaf, U.val)) :
    I.affineConormalEquiv U (Ideal.toCotangent J (I.idealSectionsEquiv U s)) =
      (i).pullbackSections I.sheaf U.val s := by
  have h₁ : I.quotientEquivSections U 1 = 1 :=
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B)
      (I.surjective_algebraMap_sections U)).map_one
  have h₂ (y : J) :
      (TensorProduct.quotTensorEquivQuotSMul J J).symm (Ideal.toCotangent J y) = 1 ⊗ₜ[A] y :=
    TensorProduct.quotTensorEquivQuotSMul_symm_mk J y
  simp only [affineConormalEquiv, LinearEquiv.trans_apply, h₂, TensorProduct.congr_tmul, h₁,
    LinearEquiv.restrictScalars_apply, LinearEquiv.symm_apply_apply, IsBaseChange.equiv_tmul,
    one_smul]
  exact Scheme.Hom.pullbackSectionsLE_self i I.sheaf U.val s

private theorem conormalMap_app_affineConormalEquiv (x : Ideal.Cotangent J) :
    (I.conormalMap R).app V (I.affineConormalEquiv U x) =
      pullbackRelativeDifferentialsSectionsEquiv R i U ⟨V, U.property.preimage i⟩ le_rfl
        (KaehlerDifferential.kerCotangentToTensor R A B x) := by
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective J x
  obtain ⟨s, rfl⟩ := (I.idealSectionsEquiv U).surjective x
  rw [affineConormalEquiv_toCotangent, conormalMap_app_pullbackSections,
    KaehlerDifferential.kerCotangentToTensor_toCotangent,
    pullbackRelativeDifferentialsSectionsEquiv_tmul_D, one_smul]
  exact (Scheme.Hom.pullbackSectionsLE_self i Ωₓ U.val
    ((X.universalDerivation R).d (X := op U.val) (I.sheafι.app U.val s))).symm

private theorem conormalMap_exact_on_affine :
    Function.Exact ((I.conormalMap R).app V) ((cotangentMap R i).app V) := by
  intro y
  let e := pullbackRelativeDifferentialsSectionsEquiv R i U ⟨V, U.property.preimage i⟩ le_rfl
  obtain ⟨ω, rfl⟩ := e.surjective y
  rw [cotangentMap_app_pullbackRelativeDifferentialsSectionsEquiv R i U
    ⟨V, U.property.preimage i⟩ le_rfl, ← map_zero (relativeDifferentialsSectionsEquiv R _
    ⟨V, U.property.preimage i⟩), (relativeDifferentialsSectionsEquiv R _
    ⟨V, U.property.preimage i⟩).injective.eq_iff,
    KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B
      (I.surjective_algebraMap_sections U) ω]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨I.affineConormalEquiv U x, I.conormalMap_app_affineConormalEquiv R U x⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := (I.affineConormalEquiv U).surjective y
    rw [conormalMap_app_affineConormalEquiv] at hy
    exact ⟨x, e.injective hy⟩

private theorem conormalMap_injective_on_affine [Smooth (I.subscheme ↘ Spec (.of R))] :
    Function.Injective ((I.conormalMap R).app V) := by
  have hSmooth : Algebra.Smooth R B := by
    rw [← RingHom.smooth_algebraMap, RingHom.algebraMap_toAlgebra,
      Scheme.baseRingToStructurePresheaf_app_eq_appLE, CommRingCat.hom_comp]
    exact (RingHom.Smooth.of_bijective (f := (Scheme.ΓSpecIso (.of R)).inv.hom)
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv)).comp
        ((I.subscheme ↘ Spec (.of R)).smooth_appLE (isAffineOpen_top _)
          (U.property.preimage i) le_top)
  let := hSmooth.formallySmooth
  intro x y h
  obtain ⟨a, rfl⟩ := (I.affineConormalEquiv U).surjective x
  obtain ⟨b, rfl⟩ := (I.affineConormalEquiv U).surjective y
  rw [conormalMap_app_affineConormalEquiv, conormalMap_app_affineConormalEquiv] at h
  exact congrArg (I.affineConormalEquiv U)
    (KaehlerDifferential.kerCotangentToTensor_injective_of_formallySmooth
      (I.surjective_algebraMap_sections U)
      ((pullbackRelativeDifferentialsSectionsEquiv R i U
        ⟨V, U.property.preimage i⟩ le_rfl).injective h))

end Affine

/-- Differentiating a section of the ideal gives zero in the differentials of its
closed subscheme. -/
@[reassoc (attr := simp)]
theorem conormalMap_comp_cotangentMap :
    I.conormalMap R ≫ cotangentMap R i = 0 := by
  let adj := pullbackPushforwardAdjunction i
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  have hzero : adj.homEquiv I.sheaf (I.subscheme.relativeDifferentials R) 0 = 0 := by
    rw [Adjunction.homEquiv_unit, Functor.map_zero, CategoryTheory.Limits.comp_zero]
  rw [hzero]
  have hAdj : adj.homEquiv I.sheaf ((pullback i).obj Ωₓ) (I.conormalMap R) =
      I.conormalMapAdjoint R := Equiv.apply_symm_apply _ _
  rw [hAdj]
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  -- A section of the pushforward over U is a section over the inverse image of U.
  change (cotangentMap R i).app (i ⁻¹ᵁ U) ((i).pullbackSections Ωₓ U
    ((X.universalDerivation R).d (I.sheafι.app U s))) = 0
  have hs := (I.toPushforwardSubscheme_app _).symm.trans
    (I.subschemeι_app_eq_zero_iff.mpr (I.sheafι_app_mem U s))
  let d : Γ(I.subscheme, i ⁻¹ᵁ U) →+ Γ(I.subscheme.relativeDifferentials R, i ⁻¹ᵁ U) :=
    (I.subscheme.universalDerivation R).d
  exact (cotangentMap_app_pullbackSections_d R i U (I.sheafι.app U s)).trans
    ((congrArg d hs).trans d.map_zero)

/-- The conormal sequence of a closed subscheme over the base ring. -/
abbrev conormalSequence : ShortComplex I.subscheme.Modules :=
  ShortComplex.mk (I.conormalMap R) (cotangentMap R i) (I.conormalMap_comp_cotangentMap R)

private theorem isBasis_preimage_affineOpens :
    TopologicalSpace.Opens.IsBasis (Set.range fun U : X.affineOpens ↦ i ⁻¹ᵁ U.val) := by
  have h := X.isBasis_affineOpens.of_isInducing (i).isEmbedding.isInducing
  exact (Set.image_eq_range _ _ ▸ h)

open CategoryTheory.Limits in
private theorem surjective_conormalKernelLift_app (U : X.affineOpens) :
    Function.Surjective ((kernel.lift (cotangentMap R i) (I.conormalMap R)
      (I.conormalMap_comp_cotangentMap R)).app (i ⁻¹ᵁ U.val)) := by
  let V := i ⁻¹ᵁ U.val
  let g := cotangentMap R i
  intro y
  have hy : g.app V ((kernel.ι g).app V y) = 0 := by
    have h := congrArg (fun f ↦ f.app V) (kernel.condition g)
    rw [Scheme.Modules.Hom.comp_app, Hom.zero_app] at h
    have h' : (0 : Γ(kernel g, V) ⟶
        Γ(I.subscheme.relativeDifferentials R, V)) y = 0 := rfl
    exact (ConcreteCategory.congr_hom h y).trans h'
  obtain ⟨x, hx⟩ := (I.conormalMap_exact_on_affine R U _).mp hy
  refine ⟨x, ?_⟩
  apply (ModuleCat.mono_iff_injective ((sectionsFunctor V).map (kernel.ι g))).mp inferInstance
  have h := congrArg (fun f ↦ f.app V) (kernel.lift_ι g (I.conormalMap R)
    (I.conormalMap_comp_cotangentMap R))
  exact (ConcreteCategory.congr_hom h x).trans hx

/-- The conormal sequence of a closed subscheme is exact at the restricted ambient
differentials, without a smoothness assumption. -/
theorem exact_conormalSequence : (I.conormalSequence R).Exact := by
  apply (I.conormalSequence R).exact_iff_epi_kernel_lift.mpr
  exact Scheme.Modules.Hom.epi_of_surjective_app_of_isBasis _
    I.isBasis_preimage_affineOpens (I.surjective_conormalKernelLift_app R)

open CategoryTheory.Limits in
/-- When the closed subscheme is smooth over the base, its conormal sequence is short
exact. The ambient scheme need not be smooth. -/
theorem shortExact_conormalSequence [Smooth (I.subscheme ↘ Spec (.of R))] :
    (I.conormalSequence R).ShortExact := by
  let g := cotangentMap R i
  let l := kernel.lift g (I.conormalMap R) (I.conormalMap_comp_cotangentMap R)
  have : IsIso l := by
    apply Scheme.Modules.Hom.isIso_of_isBasis l I.isBasis_preimage_affineOpens
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine ⟨fun x y h ↦ I.conormalMap_injective_on_affine R U ?_,
      I.surjective_conormalKernelLift_app R U⟩
    have hl := congrArg (fun f ↦ f.app (i ⁻¹ᵁ U.val))
      (kernel.lift_ι g (I.conormalMap R) (I.conormalMap_comp_cotangentMap R))
    exact (ConcreteCategory.congr_hom hl x).symm.trans
      ((congrArg ((kernel.ι g).app _) h).trans (ConcreteCategory.congr_hom hl y))
  refine ShortComplex.ShortExact.mk' (I.exact_conormalSequence R) ?_ ?_
  · -- The first arrow is the kernel lift followed by the kernel inclusion.
    change Mono (I.conormalMap R)
    rw [← kernel.lift_ι g (I.conormalMap R) (I.conormalMap_comp_cotangentMap R)]
    exact inferInstanceAs (Mono (l ≫ kernel.ι g))
  · exact epi_cotangentMap_of_isClosedImmersion R i

end AlgebraicGeometry.Scheme.IdealSheafData

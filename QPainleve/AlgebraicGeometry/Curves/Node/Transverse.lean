/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Relative
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk

import Mathlib.RingTheory.Etale.Locus
import QPainleve.AlgebraicGeometry.Modules.Differentials.Stalk
import QPainleve.AlgebraicGeometry.Scheme.ClosedPoint
import QPainleve.RingTheory.Kaehler.LocalCoordinates
import TauCeti.AlgebraicGeometry.AffineScheme.Basic
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
import TauCeti.AlgebraicGeometry.Pullback.Carrier
import TauCeti.RingTheory.Kaehler.FormallyEtale
import TauCeti.RingTheory.Node.EtaleChart

/-!
# Nodal charts for transverse Cartier divisors

At a closed point of a smooth surface where two Cartier equations generate
the maximal ideal, their product cuts out a curve étale locally modeled on
the split node. The coordinate map uses the Jacobian criterion for étaleness
from `TauCeti.formallyEtale_of_bijective_mapBaseChange`.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry
open MvPolynomial KaehlerDifferential

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

variable (U : X.affineOpens) {x : X} (hxU : x ∈ U.val)

local notation "L" => X.presheaf.stalk x
local notation "Poly" => MvPolynomial (Fin 2) k

/-- The base-field algebra on the sections of the affine chart. -/
noncomputable local instance sectionAlgebra : Algebra k Γ(X, U) :=
  ((X.baseRingToStructurePresheaf k).app (op U.val)).hom.toAlgebra

private theorem smooth_base_sections : Algebra.Smooth k Γ(X, U) := by
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  rw [← RingHom.smooth_algebraMap, RingHom.algebraMap_toAlgebra]
  rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE, CommRingCat.hom_comp]
  exact (RingHom.Smooth.of_bijective (f := (Scheme.ΓSpecIso (.of k)).inv.hom)
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv)).comp
      ((X ↘ Spec (.of k)).smooth_appLE (isAffineOpen_top _) U.property le_top)

private theorem exists_etale_aeval_of_span_germ_eq_maximalIdeal [PerfectField k]
    (hx : IsClosed ({x} : Set X)) (a : Fin 2 → Γ(X, U))
    (ha : Ideal.span (Set.range (fun j ↦ X.presheaf.germ U.val x hxU (a j))) =
      IsLocalRing.maximalIdeal L) :
    ∃ d ∉ (U.property.primeIdealOf ⟨x, hxU⟩).asIdeal,
      (aeval (R := k)
        (fun j ↦ algebraMap Γ(X, U) (Localization.Away d) (a j))).toRingHom.Etale := by
  let q := (U.property.primeIdealOf ⟨x, hxU⟩).asIdeal
  let : Algebra Γ(X, U) L := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let : IsScalarTower k Γ(X, U) L := isScalarTower_base_section_stalk k X ⟨x, hxU⟩
  let : Algebra Poly Γ(X, U) := (aeval a : Poly →ₐ[k] Γ(X, U)).toRingHom.toAlgebra
  let : Algebra Poly L := RingHom.toAlgebra ((algebraMap Γ(X, U) L).comp (algebraMap Poly Γ(X, U)))
  let : IsScalarTower Poly Γ(X, U) L := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower k Poly L := .of_algebraMap_eq fun r ↦
    (IsScalarTower.algebraMap_apply k Γ(X, U) L r).trans
      (congrArg (algebraMap Γ(X, U) L) ((aeval a : Poly →ₐ[k] Γ(X, U)).commutes r).symm)
  -- The coordinate differentials form a basis because the residue field is separable.
  have : IsLocalization q.primeCompl L := U.property.isLocalization_stalk ⟨x, hxU⟩
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : Algebra.FormallySmooth k L := by
    have : Algebra.Smooth k Γ(X, U) := smooth_base_sections (k := k) U
    have : Algebra.FormallyEtale Γ(X, U) L := .of_isLocalization q.primeCompl
    exact .comp k Γ(X, U) L
  have := X.moduleFinite_residueField_of_isClosed (k := k) hx
  have hsep : Algebra.FormallyUnramified k (X.residueField x) := .of_isSeparable _ _
  have hquot : Algebra.FormallyUnramified k
      (L ⧸ Ideal.span (Set.range (fun j ↦ X.presheaf.germ U.val x hxU (a j)))) := ha ▸ hsep
  obtain ⟨b⟩ := X.nonempty_basis_kaehlerDifferential_stalk (k := k) 2 x
  obtain ⟨c, hc⟩ := b.exists_basis_kaehlerDifferential_of_formallyUnramified_quotient
    (fun j ↦ X.presheaf.germ U.val x hxU (a j)) (fun j ↦ ha ▸ Ideal.subset_span ⟨j, rfl⟩)
  have : Algebra.FormallyEtale Poly L := formallyEtale_of_bijective_mapBaseChange
    (bijective_mapBaseChange_of_basis (mvPolynomialBasis k (Fin 2)) c fun j ↦ by
      rw [mvPolynomialBasis_apply, map_D, hc]
      congr 1
      exact (congrArg (algebraMap Γ(X, U) L) (aeval_X a j)))
  -- Shrink the affine chart so the coordinate map is étale on the whole chart.
  have : Algebra.IsEtaleAt Poly q := .of_equiv
    ((IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) L).restrictScalars Poly).symm
  have : Algebra.FiniteType k Γ(X, U) := finiteType_sections_of_locallyOfFiniteType k X U
  have : Algebra.FiniteType Poly Γ(X, U) := by
    let : IsScalarTower k Poly Γ(X, U) := .of_algebraMap_eq fun r ↦
      (aeval a : Poly →ₐ[k] Γ(X, U)).commutes r |>.symm
    exact .of_restrictScalars_finiteType k _ _
  have : Algebra.FinitePresentation Poly Γ(X, U) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨d, hd, het⟩ := Algebra.exists_etale_of_isEtaleAt (R := Poly) q
  refine ⟨d, hd, ?_⟩
  let B := Localization.Away d
  let f := IsScalarTower.toAlgHom k Γ(X, U) B
  have he' : aeval (fun j ↦ algebraMap Γ(X, U) B (a j)) = f.comp (aeval a) := by
    ext j
    simp [f]
  have he : (aeval (R := k) (fun j ↦ algebraMap Γ(X, U) B (a j))).toRingHom =
      algebraMap Poly B := congrArg AlgHom.toRingHom he'
  exact he.symm ▸ RingHom.etale_algebraMap.mpr het

variable {U hxU}

omit [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] in
private theorem atWorstNodalOfRelativeDimensionOne_comap_of_etale_aeval
    (V : X.affineOpens) {I J : X.IdealSheafData} (a b d : Γ(X, V))
    (ha : I.ideal V = Ideal.span {a}) (hb : J.ideal V = Ideal.span {b})
    (het : (aeval (R := k) (fun j : Fin 2 ↦
      algebraMap Γ(X, V) (Localization.Away d) (![a, b] j))).toRingHom.Etale) :
    let ι := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) (Localization.Away d))) ≫
      V.property.fromSpec
    AtWorstNodalOfRelativeDimensionOne
      (((I * J).comap ι).subschemeι ≫ ι ≫ X ↘ Spec (.of k)) := by
  let hV : IsAffineOpen V.val := V.property
  let A := Γ(X, V)
  let B := Localization.Away d
  let ι := Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hV.fromSpec
  let a' := algebraMap A B a
  let b' := algebraMap A B b
  let K : Ideal B := Ideal.span {a' * b' - algebraMap k B 0}
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))
  let η := NodeAlgebra.lift (0 : k) _ _ (NodeAlgebra.quotient_mk_mul_mk 0 a' b')
  let t := Spec.map (CommRingCat.ofHom η.toRingHom)
  have het' : (aeval (R := k) ![a', b']).toRingHom.Etale := by
    convert het using 3
    funext j
    fin_cases j <;> rfl
  have : Etale t :=
    HasRingHomProperty.Spec_iff.mpr (NodeAlgebra.etale_lift_of_etale_aeval (0 : k) a' b' het')
  have : IsClosedImmersion q := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hker : (I * J).comap ι = q.ker := by
    dsimp only [ι, q]
    rw [comap_SpecMap_fromSpec_eq_ofIdealTop _ hV, Scheme.Hom.ker_Spec_map]
    congr 2
    -- The product ideal on the affine open extends to the defining ideal of the quotient.
    change ((I * J).ideal V).map (algebraMap A B) = RingHom.ker (Ideal.Quotient.mk K)
    rw [Ideal.mk_ker, ideal_mul, Pi.mul_apply, ha, hb, Ideal.span_singleton_mul_span_singleton,
      Ideal.map_span, Set.image_singleton, map_mul]
    simp only [K, a', b', map_zero, sub_zero]
  let s := ((I * J).comap ι).subschemeι
  have hs : s.ker = q.ker := (ker_subschemeι _).trans hker
  let e := IsClosedImmersion.lift s q hs.le
  have he : IsIso e := IsClosedImmersion.isIso_lift s q hs
  suffices hn : AtWorstNodalOfRelativeDimensionOne (s ≫ ι ≫ X ↘ Spec (.of k)) from hn
  apply (MorphismProperty.cancel_left_of_respectsIso (P := @AtWorstNodalOfRelativeDimensionOne)
    e _).mp
  rw [IsClosedImmersion.lift_fac_assoc]
  have hbase : q ≫ ι ≫ X ↘ Spec (.of k) =
      t ≫ Spec.map (CommRingCat.ofHom (algebraMap k (NodeAlgebra k 0))) := by
    dsimp only [ι, q, t]
    rw [Category.assoc (Spec.map _), hV.fromSpec_comp_eq_SpecMap,
      ← Scheme.baseRingToStructurePresheaf_app_eq_appLE, ← Spec.map_comp, ← Spec.map_comp,
      ← Spec.map_comp]
    congr 1
    ext r
    exact (η.commutes r).symm
  rw [hbase]
  exact (NodeAlgebra.atWorstNodalOfRelativeDimensionOne (0 : k)).comp_of_etale t

/-- At a closed point where the two Cartier equations generate the maximal ideal,
the product divisor admits an open nodal neighbourhood. -/
theorem exists_nodal_neighbourhood_mul_of_stalkIdeal_sup_eq [PerfectField k]
    {I J : X.IdealSheafData} (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier)
    (p : (I * J).subscheme) (hp : IsClosed ({(I * J).subschemeι p} : Set X))
    (htrans : I.stalkIdeal ((I * J).subschemeι p) ⊔ J.stalkIdeal ((I * J).subschemeι p) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk ((I * J).subschemeι p))) :
    ∃ (W : Scheme.{u}) (j : W ⟶ (I * J).subscheme), IsOpenImmersion j ∧ p ∈ Set.range j ∧
      AtWorstNodalOfRelativeDimensionOne (j ≫ (I * J).subschemeι ≫ X ↘ Spec (.of k)) := by
  let x := (I * J).subschemeι p
  obtain ⟨V, -, hxV, a, b, -, -, ha, hb⟩ :=
    hI.exists_eq_span_singleton_pair_le hJ ⊤ (Opens.mem_top x)
  let hV : IsAffineOpen V.val := V.property
  let A := Γ(X, V)
  let : Algebra k A := ((X.baseRingToStructurePresheaf k).app (op V.val)).hom.toAlgebra
  let eqns : Fin 2 → A := ![a, b]
  have heq : Ideal.span (Set.range (fun j ↦ X.presheaf.germ V.val x hxV (eqns j))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [← htrans, I.stalkIdeal_eq_map V x hxV, J.stalkIdeal_eq_map V x hxV, ha, hb,
      Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, ← Ideal.span_union]
    congr 1
    ext y
    rw [Set.mem_range, Fin.exists_fin_two, Set.mem_union, Set.mem_singleton_iff]
    exact or_congr eq_comm eq_comm
  obtain ⟨d, hd, het⟩ := exists_etale_aeval_of_span_germ_eq_maximalIdeal (k := k) V hxV hp eqns heq
  let B := Localization.Away d
  let ι := Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hV.fromSpec
  let Z := ((I * J).comap ι).subscheme
  let s := ((I * J).comap ι).subschemeι
  let j := subschemeMap ((I * J).comap ι) (I * J) ι (le_map_comap _ _)
  have hj : IsPullback s j ι (I * J).subschemeι :=
    isPullback_of_isClosedImmersion s (I * J).subschemeι j ι
      (subschemeMap_subschemeι _ _ _ _).symm (by rw [ker_subschemeι, ker_subschemeι])
  have hjOpen : IsOpenImmersion j := MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    hj inferInstance
  refine ⟨Z, j, hjOpen, ?_, ?_⟩
  · rw [Scheme.Pullback.range_snd_of_isPullback hj]
    have hq : hV.primeIdealOf ⟨x, hxV⟩ ∈
        Set.range (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
      -- On spectra the affine localization inclusion is contraction of primes.
      change hV.primeIdealOf ⟨x, hxV⟩ ∈
        Set.range (PrimeSpectrum.comap (algebraMap A B))
      rw [PrimeSpectrum.localization_away_comap_range B d]
      exact hd
    obtain ⟨q, hq⟩ := hq
    exact ⟨q, (congrArg hV.fromSpec hq).trans (hV.fromSpec_primeIdealOf _)⟩
  · rw [← hj.w_assoc, Category.assoc]
    exact atWorstNodalOfRelativeDimensionOne_comap_of_etale_aeval V a b d ha hb het

end AlgebraicGeometry.Scheme.IdealSheafData

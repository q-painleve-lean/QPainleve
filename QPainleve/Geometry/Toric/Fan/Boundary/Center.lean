/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import QPainleve.Geometry.Toric.Fan.Boundary.Basic
public import QPainleve.Geometry.Toric.Fan.Separated
public import TauCeti.Algebra.Polynomial.Laurent.Basic
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import QPainleve.Algebra.MonoidAlgebra.Smooth
import QPainleve.Algebra.Polynomial.Laurent
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Equiv
import TauCeti.Algebra.MonoidAlgebra.Face
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Section
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# Binomial centers on toric boundary rays

In a rank-two fan, the boundary in a ray's affine chart is the one-dimensional torus.
A primitive character annihilating the ray gives a Laurent coordinate on this torus.
For a nonzero complex parameter `c`, the equation `1 + c * z^m = 0` cuts out a single
reduced point. Its ideal in the ray chart includes the ray ideal and the binomial equation.

This uses the affine orbit description in Fulton, *Introduction to Toric Varieties*, §3.1,
for the smooth boundary centers of Gross, Hacking and Keel, *Moduli of surfaces with an
anti-canonical cycle*, Definition 1.2. The scheme structure comes from Tau Ceti's
`AddSubmonoid.faceRestriction` and `ker_laurentEval_neg_inv`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative LaurentPolynomial TopologicalSpace

namespace TauCeti.Toric.Fan.Ray

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (ρ : Φ.Ray)

local notation "S" => dualSemigroup Φ.lattice ρ.toCone.val
local notation "R" => affineCoordinateRing Φ.lattice ρ.toCone.val
local notation "v" => ρ.primitiveGenerator

private def rayDualFace : AddSubmonoid S :=
  AddMonoidHom.mker ((AddMonoidHom.eval v).comp (dualSemigroup Φ.lattice ρ.toCone.val).subtype)

private theorem rayDualFace_saturated : (rayDualFace ρ).AddSaturated := by
  intro a b hab
  have ha := (mem_rayDualSemigroup_iff ρ _).mp a.property
  have hb := (mem_rayDualSemigroup_iff ρ _).mp b.property
  have hzero : (a : N →+ ℤ) v + (b : N →+ ℤ) v = 0 := hab
  have ha0 : (a : N →+ ℤ) v = 0 := by omega
  have hb0 : (b : N →+ ℤ) v = 0 := by omega
  exact ⟨ha0, hb0⟩

private theorem isRegularCone_toCone : IsRegularCone i ρ.toCone.val := by
  rw [ρ.toCone_eq_hull_primitiveGenerator]
  apply isRegularCone_hull_singleton Φ.lattice
  rw [Ray.primitiveGenerator_def]
  exact primitiveGenerator_isPrimitive Φ.lattice (Φ.isToricCone ρ.toCone.property) _

variable {m : N →+ ℤ}

/-- A character pairing to zero with a ray's primitive generator is regular on its affine chart. -/
def chartCharacter (hm : m v = 0) : S :=
  ⟨m, (mem_rayDualSemigroup_iff ρ m).2 hm.ge⟩

/-- The regular character has the stated exponent in the ambient character lattice. -/
@[simp]
theorem coe_chartCharacter (hm : m v = 0) : (ρ.chartCharacter hm : N →+ ℤ) = m := (rfl)

private def rayDualFaceHom (hm : m v = 0) : ℤ →+ rayDualFace ρ where
  toFun n := ⟨ρ.chartCharacter (show (n • m) v = 0 by simp [hm]), by simp [rayDualFace, hm]⟩
  map_zero' := by ext x; simp [chartCharacter]
  map_add' a b := by ext x; simp [chartCharacter, add_zsmul]

private theorem bijective_rayDualFaceHom (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    Function.Bijective (rayDualFaceHom ρ hm) := by
  constructor
  · intro a b hab
    obtain ⟨x, hx⟩ := hprim 1
    simpa [rayDualFaceHom, hx] using congrArg (fun f : rayDualFace ρ ↦
      (f.val : N →+ ℤ) x) hab
  · intro a
    obtain ⟨n, hn⟩ := ρ.exists_zsmul_eq_of_apply_primitiveGenerator_eq_zero hdim hm hprim
      (show (a.val : N →+ ℤ) v = 0 from a.property)
    exact ⟨n, Subtype.ext (Subtype.ext hn)⟩

private def rayDualFaceEquiv (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) : ℤ ≃+ rayDualFace ρ :=
  AddEquiv.ofBijective (rayDualFaceHom ρ hm) (bijective_rayDualFaceHom ρ hdim hm hprim)

/-- Restriction from the affine ray chart to its boundary torus, in the Laurent coordinate
given by the primitive character `m`. -/
def orbitCoordinateMap (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) : R →ₐ[ℂ] LaurentPolynomial ℂ :=
  (AddMonoidAlgebra.domCongr ℂ ℂ (rayDualFaceEquiv ρ hdim hm hprim).symm).toAlgHom.comp
    (((rayDualFace ρ).faceRestriction (rayDualFace_saturated ρ) ℂ).comp
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ S).symm.toAlgHom)

/-- Every Laurent polynomial on the ray orbit extends to the ray chart. -/
theorem orbitCoordinateMap_surjective (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    Function.Surjective (ρ.orbitCoordinateMap hdim hm hprim) := by
  unfold orbitCoordinateMap
  exact (AddMonoidAlgebra.domCongr ℂ ℂ (rayDualFaceEquiv ρ hdim hm hprim).symm).surjective.comp
    (((rayDualFace ρ).faceRestriction_surjective (rayDualFace_saturated ρ)).comp
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ S).symm.surjective)

/-- Restriction to the orbit kills precisely the ray ideal. -/
@[simp]
theorem ker_orbitCoordinateMap (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    RingHom.ker (ρ.orbitCoordinateMap hdim hm hprim) =
      rayIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property)
        (Ray.toToricRay Φ ρ ρ.toCone le_rfl) := by
  let e := AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ S
  let F := (rayDualFace ρ).faceRestriction (rayDualFace_saturated ρ) ℂ
  have hker : RingHom.ker (ρ.orbitCoordinateMap hdim hm hprim) =
      Ideal.comap e.symm.toRingEquiv (RingHom.ker F) := by
    ext x
    simp [orbitCoordinateMap, F, e, RingHom.mem_ker]
  rw [hker]
  dsimp only [F]
  rw [AddSubmonoid.ker_faceRestriction, AlgEquiv.symm_toRingEquiv, Ideal.comap_symm,
    AddSubmonoid.faceIdeal_def, Ideal.map_span]
  refine le_antisymm (Ideal.span_le.mpr ?_) ((rayIdeal_le_iff _ _ _ _).2 ?_)
  · rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    have hpos : 0 < (b : N →+ ℤ) v :=
      lt_of_le_of_ne ((mem_rayDualSemigroup_iff ρ _).mp b.property) (Ne.symm hb)
    rw [Ray.primitiveGenerator_def] at hpos
    simpa [e, MonoidAlgebra.of_apply] using
      monomial_mem_rayIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property) _ b hpos
  · intro b hb
    rw [← Ray.primitiveGenerator_def] at hb
    refine Ideal.subset_span ⟨_, ⟨b, ne_of_gt hb, rfl⟩, ?_⟩
    simp [e, MonoidAlgebra.of_apply]

/-- A multiple of the primitive character restricts to the corresponding Laurent monomial. -/
@[simp]
theorem orbitCoordinateMap_zsmul_chartCharacter (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (n : ℤ) :
    ρ.orbitCoordinateMap hdim hm hprim
      (MonoidAlgebra.single (ofAdd (ρ.chartCharacter (m := n • m)
        (by simp [hm]))) 1) = T n := by
  let a := rayDualFaceHom ρ hm n
  have ha : a.val = ρ.chartCharacter (m := n • m) (by simp [hm]) := (rfl)
  simp only [orbitCoordinateMap, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AddMonoidAlgebra.toMultiplicativeAlgEquiv_symm_single, toAdd_ofAdd]
  rw [← ha, AddSubmonoid.faceRestriction_single_mem, AddMonoidAlgebra.domCongr_single]
  congr 1
  exact (rayDualFaceEquiv ρ hdim hm hprim).symm_apply_apply n

/-- The primitive annihilating character becomes the Laurent variable on restriction. -/
@[simp]
theorem orbitCoordinateMap_character (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    ρ.orbitCoordinateMap hdim hm hprim
      (MonoidAlgebra.single (ofAdd (ρ.chartCharacter hm)) 1) = T 1 := by
  simpa only [one_zsmul] using ρ.orbitCoordinateMap_zsmul_chartCharacter hdim hm hprim 1

/-- Evaluation on the ray chart at the boundary center with Laurent coordinate `-c⁻¹`. -/
def binomialCenterEval (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) : R →ₐ[ℂ] ℂ :=
  (laurentEval ((-1 : ℂˣ) * c⁻¹)).comp (ρ.orbitCoordinateMap hdim hm hprim)

/-- Binomial evaluation is Laurent evaluation after restricting to the ray orbit. -/
theorem binomialCenterEval_def (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    ρ.binomialCenterEval hdim hm hprim c =
      (laurentEval ((-1 : ℂˣ) * c⁻¹)).comp (ρ.orbitCoordinateMap hdim hm hprim) :=
  (rfl)

local notation "χ" => MonoidAlgebra.of ℂ (Multiplicative S)

/-- Monomials of positive degree along the ray vanish at a binomial center. -/
theorem binomialCenterEval_single_eq_zero (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) (a : S) (r : ℂ)
    (ha : (a : N →+ ℤ) v ≠ 0) :
    ρ.binomialCenterEval hdim hm hprim c (MonoidAlgebra.single (ofAdd a) r) = 0 := by
  have hn : a ∉ rayDualFace ρ := ha
  simp [binomialCenterEval, orbitCoordinateMap, AddSubmonoid.faceRestriction_single_of_notMem, hn]

/-- A monomial of exponent `n • m` evaluates to the corresponding Laurent power. -/
theorem binomialCenterEval_single_zsmul (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) (n : ℤ) (r : ℂ) :
    ρ.binomialCenterEval hdim hm hprim c
      (MonoidAlgebra.single (ofAdd (ρ.chartCharacter (m := n • m) (by simp [hm]))) r) =
      r * (-(↑c⁻¹ : ℂ)) ^ n := by
  let a := rayDualFaceEquiv ρ hdim hm hprim n
  have he : a.val = ρ.chartCharacter (m := n • m) (by simp [hm]) := (rfl)
  simp only [← he, binomialCenterEval, orbitCoordinateMap, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AddMonoidAlgebra.toMultiplicativeAlgEquiv_symm_single, toAdd_ofAdd,
    AddSubmonoid.faceRestriction_single_mem, AddMonoidAlgebra.domCongr_single]
  rw [(rayDualFaceEquiv ρ hdim hm hprim).symm_apply_apply]
  rw [single_eq_C_mul_T, map_mul, laurentEval_T, C_eq_algebraMap]
  simp

/-- The primitive character evaluates at the unique root of the boundary binomial. -/
@[simp]
theorem binomialCenterEval_character (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    ρ.binomialCenterEval hdim hm hprim c
      (MonoidAlgebra.single (ofAdd (ρ.chartCharacter hm)) 1) = -(↑c⁻¹ : ℂ) := by
  simpa only [one_zsmul, zpow_one, one_mul] using
    ρ.binomialCenterEval_single_zsmul hdim hm hprim c 1 1

/-- The center ideal on the ray chart is generated by the ray ideal and the binomial. -/
theorem ker_binomialCenterEval (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    RingHom.ker (ρ.binomialCenterEval hdim hm hprim c) =
      rayIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property)
        (Ray.toToricRay Φ ρ ρ.toCone le_rfl) ⊔
      Ideal.span {1 + algebraMap ℂ R (c : ℂ) * χ (ofAdd (ρ.chartCharacter hm))} := by
  let f := ρ.orbitCoordinateMap hdim hm hprim
  let J : Ideal R :=
    Ideal.span {1 + algebraMap ℂ R (c : ℂ) * χ (ofAdd (ρ.chartCharacter hm))}
  have hJ : Ideal.map f J = RingHom.ker (laurentEval ((-1 : ℂˣ) * c⁻¹)) := by
    dsimp only [J]
    rw [Ideal.map_span, Set.image_singleton, ker_laurentEval_neg_inv]
    have hf : f (χ (ofAdd (ρ.chartCharacter hm))) = T 1 := by
      simpa only [MonoidAlgebra.of_apply] using ρ.orbitCoordinateMap_character hdim hm hprim
    rw [map_add, map_one, map_mul, f.commutes, hf, ← C_eq_algebraMap]
  calc
    _ = Ideal.comap f (RingHom.ker (laurentEval ((-1 : ℂˣ) * c⁻¹))) := by
      ext x
      rfl
    _ = J ⊔ RingHom.ker f := by
      rw [← hJ, Ideal.comap_map_of_surjective _ (ρ.orbitCoordinateMap_surjective hdim hm hprim),
        RingHom.ker_eq_comap_bot]
    _ = _ := by
      dsimp only [f, J]
      rw [ρ.ker_orbitCoordinateMap, sup_comm]

/-- A character strictly positive on the ray vanishes at every binomial center on that ray. -/
theorem binomialCenterEval_monomial_of_pos
    (hdim : Module.finrank ℤ N = 2) (hmρ : m ρ.primitiveGenerator = 0)
    (hsurj : Function.Surjective m) (c : ℂˣ)
    (a : dualSemigroup Φ.lattice ρ.toCone.val)
    (ha : 0 < (a : N →+ ℤ) ρ.primitiveGenerator) :
    ρ.binomialCenterEval hdim hmρ hsurj c (MonoidAlgebra.of ℂ _ (ofAdd a)) = 0 := by
  apply RingHom.mem_ker.mp
  rw [ρ.ker_binomialCenterEval]
  exact le_sup_left (a := rayIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property)
    (ρ.toToricRay Φ ρ.toCone le_rfl))
    (monomial_mem_rayIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property)
      (ρ.toToricRay Φ ρ.toCone le_rfl) a (by simpa only [Ray.primitiveGenerator_def] using ha))

/-- The boundary point with parameter `c`, included into the entire fan scheme. -/
def binomialCenter (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    Spec (.of ℂ) ⟶ Φ.algebraicRealization :=
  Spec.map (CommRingCat.ofHom (ρ.binomialCenterEval hdim hm hprim c).toRingHom) ≫
    Φ.affineToricChartι ρ.toCone

/-- The center is the point of the ray chart defined by the binomial evaluation map. -/
theorem binomialCenter_def (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    ρ.binomialCenter hdim hm hprim c =
      Spec.map (CommRingCat.ofHom (ρ.binomialCenterEval hdim hm hprim c).toRingHom) ≫
        Φ.affineToricChartι ρ.toCone := (rfl)

/-- Negating the primitive orbit character inverts the center parameter. The resulting
sections coincide as morphisms from the coefficient field. -/
theorem binomialCenter_neg_inv (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hs : Function.Surjective m) (c : ℂˣ) :
    ρ.binomialCenter hdim (m := -m) (by simp [hm])
        (neg_involutive.surjective.comp hs) c⁻¹ =
      ρ.binomialCenter hdim hm hs c := by
  suffices h : ∀ hs' : Function.Surjective (-m),
      ρ.binomialCenter hdim (m := -m) (by simp [hm]) hs' c⁻¹ =
        ρ.binomialCenter hdim hm hs c from h (neg_involutive.surjective.comp hs)
  intro hs'
  rw [binomialCenter, binomialCenter]
  congr 3
  apply congrArg AlgHom.toRingHom
  apply (MonoidAlgebra.lift ℂ ℂ (Multiplicative S)).symm.injective
  apply MonoidHom.ext
  intro a
  rw [MonoidAlgebra.lift_symm_apply, MonoidAlgebra.lift_symm_apply, ← ofAdd_toAdd a]
  by_cases ha : (a.toAdd : N →+ ℤ) v = 0
  · obtain ⟨n, hn⟩ := ρ.exists_zsmul_eq_of_apply_primitiveGenerator_eq_zero hdim hm hs ha
    have h₁ : ρ.chartCharacter (m := n • m) (by simp [hm]) = a.toAdd := Subtype.ext hn
    have h₂ : ρ.chartCharacter (m := (-n) • (-m)) (by simp [hm]) = a.toAdd :=
      Subtype.ext (by simpa using hn)
    rw [← h₂, binomialCenterEval_single_zsmul, h₂, ← h₁, binomialCenterEval_single_zsmul]
    simp only [inv_inv, zpow_neg, Units.val_inv_eq_inv_val]
    rw [← inv_zpow, inv_neg]
  · rw [binomialCenterEval_single_eq_zero _ _ _ _ _ _ _ ha,
      binomialCenterEval_single_eq_zero _ _ _ _ _ _ _ ha]

/-- A binomial center is a section of the structural morphism. -/
@[reassoc, simp]
theorem binomialCenter_comp_structureMap (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    ρ.binomialCenter hdim hm hprim c ≫ Φ.algebraicRealizationStructureMap = 𝟙 _ := by
  rw [binomialCenter, Category.assoc, Φ.affineToricChartι_comp_algebraicRealizationStructureMap,
    ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext a
  exact (ρ.binomialCenterEval hdim hm hprim c).commutes a

/-- A binomial center is a reduced closed complex point of the fan scheme. -/
instance isClosedImmersion_binomialCenter (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    IsClosedImmersion (ρ.binomialCenter hdim hm hprim c) :=
  isClosedImmersion_of_comp_eq_id _ _ (ρ.binomialCenter_comp_structureMap hdim hm hprim c)

open Scheme.IdealSheafData in
/-- The ideal sheaf of the ambient center restricts to the binomial and ray equations. -/
theorem comap_ker_binomialCenter_rayChart (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    (ρ.binomialCenter hdim hm hprim c).ker.comap (Φ.affineToricChartι ρ.toCone) =
      ofIdealTop ((
        rayIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property)
          (Ray.toToricRay Φ ρ ρ.toCone le_rfl) ⊔
        Ideal.span {1 + algebraMap ℂ R (c : ℂ) * χ (ofAdd (ρ.chartCharacter hm))}).map
          (Scheme.ΓSpecIso (.of R)).inv.hom) := by
  let j := Φ.affineToricChartι ρ.toCone
  let t := Spec.map (CommRingCat.ofHom (ρ.binomialCenterEval hdim hm hprim c).toRingHom)
  let s := ρ.binomialCenter hdim hm hprim c
  have hcomp : t ≫ j = s := rfl
  have hrange : Set.range s ⊆ Set.range j := by
    rw [← hcomp, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact Set.range_comp_subset_range _ _
  have H : IsPullback t (𝟙 _) j s := by
    rw [IsOpenImmersion.lift_uniq j s hrange t hcomp]
    exact IsOpenImmersion.isPullback_lift_id s j hrange
  rw [← ker_eq_comap_of_isPullback_of_isOpenImmersion j H]
  exact (Scheme.Hom.ker_Spec_map _).trans (congrArg
    (fun I : Ideal R ↦ ofIdealTop (I.map (Scheme.ΓSpecIso (.of R)).inv.hom))
    (ρ.ker_binomialCenterEval hdim hm hprim c))

/-- Two parameters give the same center on a fixed ray exactly when they are equal. -/
theorem binomialCenter_injective (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    Function.Injective (ρ.binomialCenter hdim hm hprim) := by
  intro c d h
  rw [binomialCenter, binomialCenter, cancel_mono, Spec.map_injective.eq_iff] at h
  have heq := congrArg (fun g : CommRingCat.of R ⟶ CommRingCat.of ℂ ↦
    g (χ (ofAdd (ρ.chartCharacter hm)))) h
  have heval : ρ.binomialCenterEval hdim hm hprim c (χ (ofAdd (ρ.chartCharacter hm))) =
      ρ.binomialCenterEval hdim hm hprim d (χ (ofAdd (ρ.chartCharacter hm))) := heq
  simp only [MonoidAlgebra.of_apply, ρ.binomialCenterEval_character, neg_inj] at heval
  exact inv_injective (Units.ext heval)

private theorem exists_rayChartEquation :
    ∃ q : S, (q : N →+ ℤ) v = 1 ∧
      rayIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property)
          (Ray.toToricRay Φ ρ ρ.toCone le_rfl) = Ideal.span {χ (ofAdd q)} := by
  let r := Ray.toToricRay Φ ρ ρ.toCone le_rfl
  let hσ := Φ.isToricCone ρ.toCone.property
  obtain ⟨l, b, hb⟩ := (isRegularCone_toCone ρ).exists_basis_sum
  let q := dualSemigroupCoord Φ.lattice hσ hb (Sum.inl r)
  refine ⟨q, ?_, rayIdeal_eq_span _ _ hb r⟩
  rw [Ray.primitiveGenerator_def, ← (hb r).eq_primitiveGenerator Φ.lattice hσ]
  simp [q]

private theorem inf_ker_eq_bot_of_rayChartEquation (q : S) (hq : (q : N →+ ℤ) v = 1) :
    ρ.toCone.val ⊓ PointedCone.ofSubmodule (LinearMap.ker (Φ.lattice.realCharacter q)) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨hx, hxker⟩ := hx
  rw [ρ.toCone_eq_hull_primitiveGenerator] at hx
  obtain ⟨r, _, rfl⟩ := PointedCone.mem_hull_singleton.mp hx
  have hzero := LinearMap.mem_ker.mp hxker
  rw [map_smul, smul_eq_mul, Φ.lattice.realCharacter_apply, hq, Int.cast_one, mul_one] at hzero
  simp [hzero]

private theorem preimage_compl_range_denseTorusι :
    Φ.affineToricChartι ρ.toCone ⁻¹' (Set.range (Φ.denseTorusι ⟨ρ.toCone⟩))ᶜ =
      PrimeSpectrum.zeroLocus (rayIdeal Φ.lattice (Φ.isToricCone ρ.toCone.property)
        (Ray.toToricRay Φ ρ ρ.toCone le_rfl) : Set R) := by
  let j := Φ.affineToricChartι ρ.toCone
  obtain ⟨q, hq, heq⟩ := exists_rayChartEquation ρ
  let P (τ : PointedCone ℝ V) := ∀ h : τ.IsFaceOf ρ.toCone.val,
    Set.range (faceAffineToricSchemeMap Φ.lattice h) =
      (PrimeSpectrum.basicOpen (MonoidAlgebra.single (ofAdd q) (1 : ℂ)) : Set (PrimeSpectrum R))
  have hP : P (ρ.toCone.val ⊓
      PointedCone.ofSubmodule (LinearMap.ker (Φ.lattice.realCharacter q))) :=
    fun _ ↦ range_faceAffineToricSchemeMap Φ.lattice (Φ.isToricCone ρ.toCone.property).fg q
  rw [inf_ker_eq_bot_of_rayChartEquation ρ q hq] at hP
  have hrange := hP (Φ.isToricCone ρ.toCone.property).salient.bot_isFaceOf
  rw [Φ.denseTorusι_face ρ.toCone, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.preimage_compl, j.isOpenEmbedding.injective.preimage_image, hrange, heq,
    PrimeSpectrum.zeroLocus_span]
  rw [MonoidAlgebra.of_apply, PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
  exact compl_compl _

/-- The affine ray orbit, parametrized by the primitive character, embeds as the closed
boundary in the affine ray chart. -/
def orbitToRayChart (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    Spec (.of (LaurentPolynomial ℂ)) ⟶ Φ.affineToricChart ρ.toCone :=
  Spec.map (CommRingCat.ofHom (ρ.orbitCoordinateMap hdim hm hprim).toRingHom)

/-- The ray orbit immersion is induced by restriction to Laurent coordinates. -/
theorem orbitToRayChart_def (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    ρ.orbitToRayChart hdim hm hprim =
      Spec.map (CommRingCat.ofHom (ρ.orbitCoordinateMap hdim hm hprim).toRingHom) :=
  (rfl)

/-- The orbit is a closed subscheme of the ray chart. -/
instance isClosedImmersion_orbitToRayChart (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    IsClosedImmersion (ρ.orbitToRayChart hdim hm hprim) :=
  IsClosedImmersion.spec_of_surjective _ (ρ.orbitCoordinateMap_surjective hdim hm hprim)

private theorem range_orbitToRayChart (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    Set.range (ρ.orbitToRayChart hdim hm hprim) =
      Φ.affineToricChartι ρ.toCone ⁻¹' (Set.range (Φ.denseTorusι ⟨ρ.toCone⟩))ᶜ := by
  rw [orbitToRayChart, preimage_compl_range_denseTorusι]
  exact (range_comap_of_surjective _ _ (ρ.orbitCoordinateMap_surjective
    hdim hm hprim)).trans (congrArg (fun I : Ideal R ↦ PrimeSpectrum.zeroLocus (I : Set R))
      (ρ.ker_orbitCoordinateMap hdim hm hprim))

open Scheme.IdealSheafData in
private theorem boundaryIdeal_comap_rayChart (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    (Φ.boundaryIdeal ⟨ρ.toCone⟩).comap (Φ.affineToricChartι ρ.toCone) =
      (ρ.orbitToRayChart hdim hm hprim).ker := by
  let f := ρ.orbitToRayChart hdim hm hprim
  rw [boundaryIdeal_def, comap_vanishingIdeal_of_isOpenImmersion]
  have hclosed := (Φ.denseTorusι ⟨ρ.toCone⟩).isOpenEmbedding.isOpen_range.isClosed_compl.preimage
    (Φ.affineToricChartι ρ.toCone).continuous
  have hZ : (⟨Φ.affineToricChartι ρ.toCone ⁻¹'
      (Set.range (Φ.denseTorusι ⟨ρ.toCone⟩))ᶜ, hclosed⟩ : Closeds (Φ.affineToricChart ρ.toCone)) =
      f.ker.support := by
    ext1
    rw [f.support_ker, f.isClosedEmbedding.isClosed_range.closure_eq, range_orbitToRayChart]
    rfl
  exact (congrArg vanishingIdeal hZ).trans f.ker_eq_vanishingIdeal_support.symm

private theorem boundaryIdeal_le_ker_orbit_comp (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    Φ.boundaryIdeal ⟨ρ.toCone⟩ ≤
      (ρ.orbitToRayChart hdim hm hprim ≫ Φ.affineToricChartι ρ.toCone).ker := by
  rw [boundaryIdeal_def]
  apply Scheme.IdealSheafData.vanishingIdeal_le_ker_of_range_subset
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_orbitToRayChart]
  exact Set.image_preimage_subset _ _

/-- The orbit is a chart of the reduced boundary, obtained by restricting the affine ray chart. -/
def orbitToBoundary (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    Spec (.of (LaurentPolynomial ℂ)) ⟶ (Φ.boundaryIdeal ⟨ρ.toCone⟩).subscheme :=
  IsClosedImmersion.lift (Φ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι
    (ρ.orbitToRayChart hdim hm hprim ≫ Φ.affineToricChartι ρ.toCone)
    (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact boundaryIdeal_le_ker_orbit_comp ρ hdim hm hprim)

/-- The ray orbit in the boundary has its original inclusion into the fan scheme. -/
@[reassoc, simp]
theorem orbitToBoundary_comp_subschemeι (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    ρ.orbitToBoundary hdim hm hprim ≫ (Φ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι =
      ρ.orbitToRayChart hdim hm hprim ≫ Φ.affineToricChartι ρ.toCone :=
  IsClosedImmersion.lift_fac _ _ _

/-- The toric structure map on the ray orbit is the structure map of the Laurent ring. -/
theorem orbitToBoundary_comp_algebraicRealizationStructureMap
    (hdim : Module.finrank ℤ N = 2) (hm : m v = 0) (hprim : Function.Surjective m) :
    ρ.orbitToBoundary hdim hm hprim ≫ (Φ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι ≫
        Φ.algebraicRealizationStructureMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (LaurentPolynomial ℂ))) := by
  rw [orbitToBoundary_comp_subschemeι_assoc,
    Φ.affineToricChartι_comp_algebraicRealizationStructureMap, orbitToRayChart_def, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (ρ.orbitCoordinateMap hdim hm hprim).commutes a

/-- The affine ray orbit is the scheme-theoretic restriction of the boundary to the ray chart. -/
theorem isPullback_orbitToBoundary (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    IsPullback (ρ.orbitToRayChart hdim hm hprim) (ρ.orbitToBoundary hdim hm hprim)
      (Φ.affineToricChartι ρ.toCone) (Φ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι := by
  apply isPullback_of_isClosedImmersion
  · exact (ρ.orbitToBoundary_comp_subschemeι hdim hm hprim).symm
  · rw [Scheme.IdealSheafData.ker_subschemeι]
    exact boundaryIdeal_comap_rayChart ρ hdim hm hprim

/-- The ray orbit is an open subscheme of the reduced boundary. -/
instance isOpenImmersion_orbitToBoundary (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    IsOpenImmersion (ρ.orbitToBoundary hdim hm hprim) :=
  MorphismProperty.of_isPullback (ρ.isPullback_orbitToBoundary hdim hm hprim)
    (Φ.isOpenImmersion_affineToricChartι ρ.toCone)

/-- The binomial point as a complex point of the reduced boundary. -/
def binomialCenterOnBoundary (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    Spec (.of ℂ) ⟶ (Φ.boundaryIdeal ⟨ρ.toCone⟩).subscheme :=
  Spec.map (CommRingCat.ofHom (laurentEval ((-1 : ℂˣ) * c⁻¹)).toRingHom) ≫
    ρ.orbitToBoundary hdim hm hprim

/-- On the ray orbit, a binomial center is Laurent evaluation at `-c⁻¹`. -/
theorem binomialCenterOnBoundary_def (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    ρ.binomialCenterOnBoundary hdim hm hprim c =
      Spec.map (CommRingCat.ofHom (laurentEval ((-1 : ℂˣ) * c⁻¹)).toRingHom) ≫
        ρ.orbitToBoundary hdim hm hprim :=
  (rfl)

/-- Including the binomial point from the boundary gives the same point of the fan scheme. -/
@[reassoc, simp]
theorem binomialCenterOnBoundary_comp_subschemeι (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    ρ.binomialCenterOnBoundary hdim hm hprim c ≫ (Φ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι =
      ρ.binomialCenter hdim hm hprim c := by
  rw [binomialCenterOnBoundary, Category.assoc, orbitToBoundary_comp_subschemeι, ← Category.assoc,
    orbitToRayChart, ← Spec.map_comp, binomialCenter, binomialCenterEval]
  rfl

/-- The binomial point is a reduced closed point of the boundary. -/
instance isClosedImmersion_binomialCenterOnBoundary (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    IsClosedImmersion (ρ.binomialCenterOnBoundary hdim hm hprim c) := by
  have : IsClosedImmersion (ρ.binomialCenterOnBoundary hdim hm hprim c ≫
      (Φ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι) := by
    rw [binomialCenterOnBoundary_comp_subschemeι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (Φ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι

/-- The ray chart of the reduced boundary is a smooth relative curve over `ℂ`. -/
theorem smoothOfRelativeDimension_orbitToBoundary (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) :
    SmoothOfRelativeDimension 1
      (ρ.orbitToBoundary hdim hm hprim ≫ (Φ.boundaryIdeal ⟨ρ.toCone⟩).subschemeι ≫
        Φ.algebraicRealizationStructureMap) := by
  rw [orbitToBoundary_comp_algebraicRealizationStructureMap,
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)
    (Q := RingHom.Locally (@RingHom.IsStandardSmoothOfRelativeDimension 1)),
    CommRingCat.hom_ofHom]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)]
  have hSmooth := AddMonoidAlgebra.isStandardSmoothOfRelativeDimension_finsupp_int ℂ (Fin 1)
  rw [Nat.card_fin] at hSmooth
  let e : (Fin 1 →₀ ℤ) ≃+ ℤ := Finsupp.uniqueAddEquiv 0
  have hLaurent : Algebra.IsStandardSmoothOfRelativeDimension 1 ℂ (LaurentPolynomial ℂ) :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
      (AddMonoidAlgebra.domCongr ℂ ℂ e)
  exact hLaurent

/-- The binomial point on the boundary lies in the open ray orbit. -/
theorem range_binomialCenterOnBoundary_subset_range_orbitToBoundary
    (hdim : Module.finrank ℤ N = 2) (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    Set.range (ρ.binomialCenterOnBoundary hdim hm hprim c) ⊆
      Set.range (ρ.orbitToBoundary hdim hm hprim) := by
  rw [binomialCenterOnBoundary, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  exact Set.image_subset_range _ _

/-- The binomial point is an effective Cartier divisor on the reduced toric boundary. -/
theorem isEffectiveCartier_ker_binomialCenterOnBoundary (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    (ρ.binomialCenterOnBoundary hdim hm hprim c).ker.IsEffectiveCartier := by
  let D := Φ.boundaryIdeal ⟨ρ.toCone⟩
  let f := D.subschemeι ≫ Φ.algebraicRealizationStructureMap
  let j := ρ.orbitToBoundary hdim hm hprim
  let U := j.opensRange
  let s := ρ.binomialCenterOnBoundary hdim hm hprim c
  have hs : s ≫ f = 𝟙 _ := by
    dsimp only [s, f, D]
    rw [← Category.assoc, binomialCenterOnBoundary_comp_subschemeι,
      binomialCenter_comp_structureMap]
  have hU : Set.range s ⊆ U := by
    simpa only [U, Scheme.Hom.coe_opensRange] using
      ρ.range_binomialCenterOnBoundary_subset_range_orbitToBoundary hdim hm hprim c
  let e := IsOpenImmersion.isoOfRangeEq j U.ι U.range_ι.symm
  have he : e.hom ≫ U.ι = j :=
    IsOpenImmersion.isoOfRangeEq_hom_fac j U.ι U.range_ι.symm
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{0} 1) :=
    @MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ _
      (smoothOfRelativeDimension_isStableUnderBaseChange 1)
  have : SmoothOfRelativeDimension 1 (U.ι ≫ f) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) e.hom,
      ← Category.assoc, he]
    exact smoothOfRelativeDimension_orbitToBoundary ρ hdim hm hprim
  exact Scheme.Hom.isEffectiveCartier_ker_of_comp_eq_id s hs U hU

/-- The ideal of the boundary center is the residue-field ideal of its closed point. -/
theorem exists_closedPoint_ker_binomialCenterOnBoundary (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ) :
    ∃ p : (Φ.boundaryIdeal ⟨ρ.toCone⟩).subscheme, IsClosed ({p} : Set _) ∧
      (ρ.binomialCenterOnBoundary hdim hm hprim c).ker = (Scheme.fromSpecResidueField _ p).ker := by
  let s := ρ.binomialCenterOnBoundary hdim hm hprim c
  let p := s (IsLocalRing.closedPoint ℂ)
  refine ⟨p, ?_, s.ker_eq_ker_fromSpecResidueField⟩
  have hrange : Set.range s = {p} :=
    Set.range_eq_singleton fun z ↦ congrArg s (Subsingleton.elim z _)
  rw [← hrange]
  exact s.isClosedEmbedding.isClosed_range

/-- Two binomial centers can coincide only if their rays agree. Distinct ray charts
intersect in the dense torus, whereas these centers lie on the boundary. -/
theorem eq_of_binomialCenter_eq {τ : Φ.Ray} {m' : N →+ ℤ} (hdim : Module.finrank ℤ N = 2)
    (hm : m v = 0) (hprim : Function.Surjective m) (c : ℂˣ)
    (hm' : m' τ.primitiveGenerator = 0) (hprim' : Function.Surjective m') (d : ℂˣ)
    (h : ρ.binomialCenter hdim hm hprim c = τ.binomialCenter hdim hm' hprim' d) : ρ = τ := by
  let pt : Spec (.of ℂ) := IsLocalRing.closedPoint ℂ
  let p := ρ.binomialCenter hdim hm hprim c pt
  let σ := ρ.toCone ⊓ τ.toCone
  have hpρ : p ∈ Set.range (Φ.affineToricChartι ρ.toCone) := by
    dsimp only [p]
    rw [binomialCenter_def, Scheme.Hom.comp_apply]
    exact Set.mem_range_self _
  have hpτ : p ∈ Set.range (Φ.affineToricChartι τ.toCone) := by
    dsimp only [p]
    rw [h, binomialCenter_def, Scheme.Hom.comp_apply]
    exact Set.mem_range_self _
  have hp : p ∈ Set.range (Φ.affineToricChartι σ) := by
    rw [← Φ.range_affineToricChartι_inter_range_affineToricChartι]
    exact ⟨hpρ, hpτ⟩
  have hD : p ∈ ((Φ.boundaryIdeal ⟨ρ.toCone⟩).support : Set Φ.algebraicRealization) := by
    dsimp only [p]
    rw [← (Φ.boundaryIdeal ⟨ρ.toCone⟩).range_subschemeι,
      ← binomialCenterOnBoundary_comp_subschemeι, Scheme.Hom.comp_apply]
    exact Set.mem_range_self _
  have hσ : σ.val ≠ ⊥ := by
    intro hbot
    have heq : σ = ⟨⊥, Φ.bot_mem ρ.toCone.property⟩ := Subtype.ext hbot
    rw [heq, ← Φ.denseTorusι_eq_affineToricChartι ⟨ρ.toCone⟩ _] at hp
    exact (Φ.support_boundaryIdeal ⟨ρ.toCone⟩ ▸ hD) hp
  have hρ : σ.val.IsFaceOf ρ.toCone.val :=
    Φ.isFaceOf_of_le ρ.toCone.property σ.property inf_le_left
  have hτ : σ.val.IsFaceOf τ.toCone.val :=
    Φ.isFaceOf_of_le τ.toCone.property σ.property inf_le_right
  rw [ρ.toCone_eq_hull_primitiveGenerator] at hρ
  rw [τ.toCone_eq_hull_primitiveGenerator] at hτ
  apply Subtype.ext
  apply Subtype.ext
  exact ((hρ.eq_bot_or_eq_of_hull_singleton _).resolve_left hσ |>.trans
    ρ.toCone_eq_hull_primitiveGenerator.symm).symm.trans
    ((hτ.eq_bot_or_eq_of_hull_singleton _).resolve_left hσ |>.trans
      τ.toCone_eq_hull_primitiveGenerator.symm)

end TauCeti.Toric.Fan.Ray

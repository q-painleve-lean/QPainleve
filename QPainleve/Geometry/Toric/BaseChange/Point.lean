/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.BaseChange.Fan.Basic
public import QPainleve.Geometry.Toric.BaseChange.Fan.Map
public import QPainleve.Geometry.Toric.Fan.Equiv

import TauCeti.AlgebraicGeometry.IdealSheaf.Section
import TauCeti.AlgebraicGeometry.RationalPoint.Basic

/-!
# Distinguished sections of toric schemes

For any face of a cone, the associated distinguished section evaluates monomials
at one when their characters vanish on the face and at zero otherwise.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra Multiplicative
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V} (hi : IsIntegralLattice i) (F : σ.Face)

private theorem vanishesOnFace_add_iff (m n : dualSemigroup hi σ) :
    (∀ y ∈ F, hi.realCharacter ((m + n : dualSemigroup hi σ) : N →+ ℤ) y = 0) ↔
      (∀ y ∈ F, hi.realCharacter m.val y = 0) ∧ (∀ y ∈ F, hi.realCharacter n.val y = 0) := by
  have h (m : dualSemigroup hi σ) (y : V) (hy : y ∈ F) :
      0 ≤ hi.realCharacter m.val y :=
    (mem_dualSemigroup hi m.val).mp m.property (F.isFaceOf.le hy)
  simp only [AddSubmonoid.coe_add, map_add, LinearMap.add_apply]
  constructor
  · intro hsum
    exact ⟨fun y hy ↦ (add_eq_zero_iff_of_nonneg (h m y hy) (h n y hy)).mp (hsum y hy) |>.1,
      fun y hy ↦ (add_eq_zero_iff_of_nonneg (h m y hy) (h n y hy)).mp (hsum y hy) |>.2⟩
  · rintro ⟨hm, hn⟩ y hy
    simp [hm y hy, hn y hy]

variable (R : Type*) [CommSemiring R]

open Classical in
/-- The evaluation on the affine chart of a cone at the distinguished point of a face. -/
def facePointAlgebraHom : affineChartRing R hi σ →ₐ[R] R :=
  AddMonoidAlgebra.lift R R (dualSemigroup hi σ)
    { toFun m := if ∀ y ∈ F, hi.realCharacter (toAdd m).val y = 0 then 1 else 0
      map_one' := by simp
      map_mul' m n := by
        rw [toAdd_mul, vanishesOnFace_add_iff]
        split_ifs <;> simp_all }

open Classical in
/-- Monomials supported on characters vanishing on the face retain their coefficient. -/
@[simp]
theorem facePointAlgebraHom_single (m : dualSemigroup hi σ) (r : R) :
    facePointAlgebraHom hi F R (single m r) =
      if ∀ y ∈ F, hi.realCharacter m.val y = 0 then r else 0 := by
  rw [facePointAlgebraHom, AddMonoidAlgebra.lift_single]
  change r • (if ∀ y ∈ F, hi.realCharacter m.val y = 0 then (1 : R) else 0) = _
  split_ifs <;> simp

namespace Fan

universe u

variable {R N : Type u} [CommRing R] {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (Φ : Fan i)

/-- The distinguished section of a cone lands in its affine chart. -/
def distinguishedSection (σ : Φ.cones) : Spec (.of R) ⟶ Φ.finiteFanScheme R :=
  Spec.map (CommRingCat.ofHom (facePointAlgebraHom Φ.lattice (⊤ : σ.val.Face) R).toRingHom) ≫
    Φ.affineChartι R σ

/-- The distinguished section is the affine evaluation followed by the chart inclusion. -/
theorem distinguishedSection_def (σ : Φ.cones) :
    Φ.distinguishedSection (R := R) σ =
      Spec.map (CommRingCat.ofHom (facePointAlgebraHom Φ.lattice (⊤ : σ.val.Face) R).toRingHom) ≫
        Φ.affineChartι R σ :=
  (rfl)

/-- The distinguished point is a section of the structure morphism over the coefficient ring. -/
@[reassoc (attr := simp)]
theorem distinguishedSection_comp_finiteFanSchemeToSpec (σ : Φ.cones) :
    Φ.distinguishedSection (R := R) σ ≫ Φ.finiteFanSchemeToSpec R = 𝟙 _ := by
  rw [distinguishedSection_def, Category.assoc, affineChartι_finiteFanSchemeToSpec,
    Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (facePointAlgebraHom Φ.lattice (⊤ : σ.val.Face) R).commutes

/-- The distinguished section is a closed immersion. -/
instance isClosedImmersion_distinguishedSection (σ : Φ.cones) :
    IsClosedImmersion (Φ.distinguishedSection (R := R) σ) :=
  (Φ.distinguishedSection (R := R) σ).isClosedImmersion_of_comp_eq_id
    (Φ.distinguishedSection_comp_finiteFanSchemeToSpec σ)

/-- Over a field, the distinguished section determines a closed point. -/
theorem isClosed_singleton_distinguishedSection (K : Type u) [Field K] (σ : Φ.cones) :
    IsClosed {Φ.distinguishedSection (R := K) σ (IsLocalRing.closedPoint K)} :=
  isClosed_singleton_of_section (Φ.distinguishedSection_comp_finiteFanSchemeToSpec σ)

private theorem notMem_range_faceAffineChartMap_distinguishedSection
    {σ τ : PointedCone ℝ V} (hσ : IsToricCone i σ) (h : τ.IsFaceOf σ) (hne : τ ≠ σ)
    (x : Spec (.of R)) :
    Spec.map (CommRingCat.ofHom (facePointAlgebraHom Φ.lattice (⊤ : σ.Face) R).toRingHom) x ∉
      Set.range (faceAffineChartMap R Φ.lattice h) := by
  obtain ⟨m, hm, he⟩ := hσ.rational.exists_mem_dualSemigroup_inf_ker_eq Φ.lattice h
  have hmem : ¬ ∀ y, y ∈ (⊤ : σ.Face) → Φ.lattice.realCharacter m y = 0 := by
    intro han
    apply hne
    rw [← he]
    exact inf_eq_left.mpr fun y hy ↦ LinearMap.mem_ker.mpr (han y hy)
  have heval := facePointAlgebraHom_single Φ.lattice (⊤ : σ.Face) R ⟨m, hm⟩ 1
  simp only [hmem, ite_false] at heval
  subst τ
  rw [range_faceAffineChartMap R Φ.lattice hσ.fg ⟨m, hm⟩]
  intro hx
  have hy := (PrimeSpectrum.mem_basicOpen _ _).mp hx
  apply hy
  rw [Spec.map_apply]
  change (facePointAlgebraHom Φ.lattice (⊤ : σ.Face) R) (AddMonoidAlgebra.single ⟨m, hm⟩ 1) ∈
    x.asIdeal
  rw [heval]
  exact x.asIdeal.zero_mem

/-- A distinguished section lies in a cone chart precisely when that cone contains its cone. -/
theorem distinguishedSection_mem_range_affineChartι_iff (σ τ : Φ.cones) (x : Spec (.of R)) :
    Φ.distinguishedSection σ x ∈ Set.range (Φ.affineChartι R τ) ↔ σ ≤ τ := by
  let p := Spec.map
    (CommRingCat.ofHom (facePointAlgebraHom Φ.lattice (⊤ : σ.val.Face) R).toRingHom)
  constructor
  · rintro ⟨y, hy⟩
    rw [distinguishedSection_def, Scheme.Hom.comp_apply] at hy
    obtain ⟨z, hz, -⟩ := (Φ.affineChartι_apply_eq_affineChartι_apply_iff R
      (σ := σ) (τ := τ) (p x) y).mp hy.symm
    by_contra h
    have hne : σ.val ⊓ τ.val ≠ σ.val := fun he ↦ h (inf_eq_left.mp he : σ.val ≤ τ.val)
    exact (Φ.notMem_range_faceAffineChartMap_distinguishedSection (Φ.isToricCone σ.property)
      (Φ.inf_isFaceOf_left σ.property τ.property) hne x) ⟨z, hz⟩
  · intro h
    let hf := Φ.isFaceOf_of_le τ.property σ.property h
    refine ⟨faceAffineChartMap R Φ.lattice hf (p x), ?_⟩
    rw [← Scheme.Hom.comp_apply, Φ.faceAffineChartMap_comp_affineChartι R (τ := σ) (σ := τ) hf,
      distinguishedSection_def, Scheme.Hom.comp_apply]

end Fan

end TauCeti.Toric

namespace TauCeti.Toric.FanHom

universe u

variable (R : Type u) [CommRing R] {N N' : Type u} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}

/-- A toric morphism sends the distinguished section of a source cone to that of
a target cone if the image of the source cone spans the same subspace. -/
@[reassoc]
theorem distinguishedSection_comp_finiteFanSchemeHom_of_span_eq (f : FanHom Φ Ψ)
    (σ : Φ.cones) (τ : Ψ.cones) (hm : Set.MapsTo f.realMap σ.val τ.val)
    (hspan : Submodule.span ℝ (f.realMap '' (σ.val : Set V)) =
      Submodule.span ℝ (τ.val : Set V')) :
    Φ.distinguishedSection (R := R) σ ≫ f.finiteFanSchemeHom R =
      Ψ.distinguishedSection (R := R) τ := by
  classical
  let A := _root_.AddMonoidAlgebra.mapDomainAlgHom R R
    (dualSemigroupMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice hm)
  have h (m : dualSemigroup Ψ.lattice τ.val) :
      (∀ x ∈ (⊤ : σ.val.Face), Φ.lattice.realCharacter
        (dualSemigroupMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice hm m) x = 0) ↔
      (∀ y ∈ (⊤ : τ.val.Face), Ψ.lattice.realCharacter m y = 0) := by
    simp only [coe_dualSemigroupMap, Φ.lattice.realCharacter_comp Ψ.lattice f.latticeMap
      f.realMap f.map_lattice, LinearMap.comp_apply]
    let χ := Ψ.lattice.realCharacter m
    -- Top-face membership is cone membership on both sides.
    change (∀ x ∈ (σ.val : Set V), χ (f.realMap x) = 0) ↔ ∀ y ∈ (τ.val : Set V'), χ y = 0
    have hχ (s : Set V') : (∀ y ∈ s, χ y = 0) ↔ Submodule.span ℝ s ≤ LinearMap.ker χ := by
      rw [Submodule.span_le]
      exact ⟨fun h y hy ↦ LinearMap.mem_ker.mpr (h y hy),
        fun h y hy ↦ LinearMap.mem_ker.mp (h hy)⟩
    have himage : (∀ x ∈ (σ.val : Set V), χ (f.realMap x) = 0) ↔
        ∀ y ∈ f.realMap '' (σ.val : Set V), χ y = 0 := by
      constructor
      · intro hz
        exact Set.forall_mem_image.mpr fun x hx ↦ hz x hx
      · intro hz x hx
        exact Set.forall_mem_image.mp hz hx
    rw [himage, hχ, hχ, hspan]
  have he : (facePointAlgebraHom Φ.lattice (⊤ : σ.val.Face) R).comp A =
      facePointAlgebraHom Ψ.lattice (⊤ : τ.val.Face) R := by
    apply _root_.AddMonoidAlgebra.algHom_ext
    · intro m
      have hm' : A (single m 1) = single
          (dualSemigroupMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice hm m) 1 :=
        _root_.AddMonoidAlgebra.mapDomain_single
      rw [AlgHom.comp_apply, hm', facePointAlgebraHom_single, facePointAlgebraHom_single, h]
    · exact Subsingleton.elim _ _
  rw [Fan.distinguishedSection_def, Fan.distinguishedSection_def, Category.assoc,
    f.affineChartι_comp_finiteFanSchemeHom R _ _ hm,
    affineChartMap_def, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hr : (facePointAlgebraHom Φ.lattice (⊤ : σ.val.Face) R).toRingHom.comp A.toRingHom =
      (facePointAlgebraHom Ψ.lattice (⊤ : τ.val.Face) R).toRingHom :=
    congrArg AlgHom.toRingHom he
  exact congrArg (fun g ↦ Spec.map (CommRingCat.ofHom g) ≫ Ψ.affineChartι R τ) hr

end TauCeti.Toric.FanHom

namespace TauCeti.Toric.FanEquiv

universe u

variable (R : Type u) [CommRing R] {N N' : Type u} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'} (e : FanEquiv Φ Ψ)

/-- The scheme map of a fan equivalence sends the distinguished section of a cone
to the distinguished section of the image cone. -/
@[reassoc (attr := simp)]
theorem distinguishedSection_comp_finiteFanSchemeHom (σ : Φ.cones) :
    Φ.distinguishedSection (R := R) σ ≫ e.toFanHom.finiteFanSchemeHom R =
      Ψ.distinguishedSection (R := R) (e.coneEquiv σ) := by
  apply e.toFanHom.distinguishedSection_comp_finiteFanSchemeHom_of_span_eq R σ _
    (e.mapsTo_coneEquiv σ)
  rw [e.coneEquiv_apply_coe, PointedCone.coe_map, toFanHom_realMap]

end TauCeti.Toric.FanEquiv

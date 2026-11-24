/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import QPainleve.Geometry.Toric.Fan.Scheme
public import TauCeti.Geometry.Toric.Algebraic.Fan.Over
public import TauCeti.Geometry.Toric.Analytic.Cone.Orbit.Basic
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField

/-!
# Distinguished points of fan schemes

The distinguished complex point of a cone defines a scheme morphism into the fan scheme.
Its membership in the open cone charts follows from Tau Ceti's localization of a face
chart at a monomial. The point is a section of the structure morphism to `Spec ℂ`
and is a closed immersion with reduced image.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.Toric

/-- The distinguished point of a cone kills monomials positive on one of its rays. -/
theorem distinguishedPoint_top_single_eq_zero_of_pos
    {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
    {i : N →+ V} {σ : PointedCone ℝ V}
    (hi : IsIntegralLattice i) (hσ : IsToricCone i σ) (r : ToricRay σ)
    (m : dualSemigroup hi σ)
    (hm : 0 < (m : N →+ ℤ) (primitiveGenerator hi hσ r)) :
    distinguishedPoint hi (⊤ : σ.Face) (MonoidAlgebra.single (ofAdd m) 1) = 0 := by
  rw [distinguishedPoint_apply_single]
  split_ifs with h
  · exfalso
    have hx : i (primitiveGenerator hi hσ r) ∈ (⊤ : σ.Face) :=
      r.val.isFaceOf.le (primitiveGenerator_mem hi hσ r)
    have hz := h _ hx
    rw [hi.realCharacter_apply] at hz
    exact hm.ne' (Int.cast_eq_zero.mp hz)
  · rfl

end TauCeti.Toric

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

/-- The rational point of a fan scheme given by the distinguished point of a cone in its
affine chart. -/
def distinguishedPointHom (σ : Φ.cones) : Spec (.of ℂ) ⟶ Φ.algebraicRealization :=
  Spec.map (CommRingCat.ofHom (distinguishedPoint Φ.lattice (⊤ : σ.val.Face)).toRingHom) ≫
    Φ.affineToricChartι σ

/-- The distinguished point is the composite of its affine point with the cone chart. -/
theorem distinguishedPointHom_def (σ : Φ.cones) :
    Φ.distinguishedPointHom σ =
      Spec.map (CommRingCat.ofHom (distinguishedPoint Φ.lattice (⊤ : σ.val.Face)).toRingHom) ≫
        Φ.affineToricChartι σ := (rfl)

private theorem notMem_range_faceAffineToricSchemeMap_distinguishedPoint
    {σ τ : PointedCone ℝ V} (hσ : IsToricCone i σ) (h : τ.IsFaceOf σ) (hne : τ ≠ σ)
    (x : Spec (.of ℂ)) :
    Spec.map (CommRingCat.ofHom (distinguishedPoint Φ.lattice (⊤ : σ.Face)).toRingHom) x ∉
      Set.range (faceAffineToricSchemeMap Φ.lattice h) := by
  obtain ⟨m, hm, he⟩ := hσ.rational.exists_mem_dualSemigroup_inf_ker_eq Φ.lattice h
  have hmem : ¬ ∀ y, y ∈ (⊤ : σ.Face) → Φ.lattice.realCharacter m y = 0 := by
    intro han
    apply hne
    rw [← he]
    exact inf_eq_left.mpr fun y hy ↦ LinearMap.mem_ker.mpr (han y hy)
  -- The face chart inverts a character that vanishes at the distinguished point.
  have heval := distinguishedPoint_apply_single Φ.lattice (⊤ : σ.Face) ⟨m, hm⟩
  simp only [hmem, ite_false] at heval
  subst τ
  rw [range_faceAffineToricSchemeMap Φ.lattice hσ.fg ⟨m, hm⟩]
  intro hx
  have hy := (PrimeSpectrum.mem_basicOpen _ _).mp hx
  apply hy
  rw [Spec.map_apply]
  -- The comap on prime ideals uses the evaluation of the inverted monomial.
  change distinguishedPoint Φ.lattice (⊤ : σ.Face) (MonoidAlgebra.single (ofAdd ⟨m, hm⟩) 1) ∈
    x.asIdeal
  rw [heval]
  exact x.asIdeal.zero_mem

private theorem notMem_chart_distinguishedPointHom (σ τ : Φ.cones)
    (hστ : ¬ σ ≤ τ) (x : Spec (.of ℂ)) :
    Φ.distinguishedPointHom σ x ∉ Set.range (Φ.affineToricChartι τ) := by
  intro hx
  let p := Spec.map
    (CommRingCat.ofHom (distinguishedPoint Φ.lattice (⊤ : σ.val.Face)).toRingHom)
  have hinter : Φ.affineToricChartι σ (p x) ∈ Set.range (Φ.affineToricChartι (σ ⊓ τ)) := by
    rw [← Φ.range_affineToricChartι_inter_range_affineToricChartι]
    exact ⟨⟨_, rfl⟩, by simpa only [distinguishedPointHom_def, Scheme.Hom.comp_apply] using hx⟩
  let h := Φ.inf_isFaceOf_left σ.property τ.property
  rw [← Φ.faceAffineToricSchemeMap_comp_affineToricChartι h] at hinter
  obtain ⟨y, hy⟩ := hinter
  have hne : σ.val ⊓ τ.val ≠ σ.val := fun he ↦ hστ ((inf_eq_left.mp he : σ.val ≤ τ.val))
  exact Φ.notMem_range_faceAffineToricSchemeMap_distinguishedPoint
    (Φ.isToricCone σ.property) h hne x
      ⟨y, (Φ.affineToricChartι σ).isOpenEmbedding.injective (by
        simpa only [Scheme.Hom.comp_apply] using hy)⟩

/-- The distinguished point attached to `σ` belongs to the chart of `τ` exactly when
`σ` is a face of `τ`. -/
theorem distinguishedPointHom_mem_range_affineToricChartι_iff (σ τ : Φ.cones)
    (x : Spec (.of ℂ)) :
    Φ.distinguishedPointHom σ x ∈ Set.range (Φ.affineToricChartι τ) ↔ σ ≤ τ := by
  refine ⟨fun hx ↦ by_contra fun hn ↦ Φ.notMem_chart_distinguishedPointHom σ τ hn x hx,
    fun h ↦ ?_⟩
  let hface := Φ.isFaceOf_of_le τ.property σ.property h
  let p := Spec.map
    (CommRingCat.ofHom (distinguishedPoint Φ.lattice (⊤ : σ.val.Face)).toRingHom)
  refine ⟨faceAffineToricSchemeMap Φ.lattice hface (p x), ?_⟩
  rw [← Scheme.Hom.comp_apply, Φ.faceAffineToricSchemeMap_comp_affineToricChartι hface,
    distinguishedPointHom_def, Scheme.Hom.comp_apply]

/-- The distinguished point is a section of the toric structure morphism. -/
@[simp]
theorem distinguishedPointHom_comp_algebraicRealizationStructureMap (σ : Φ.cones) :
    Φ.distinguishedPointHom σ ≫ Φ.algebraicRealizationStructureMap = 𝟙 _ := by
  rw [Φ.distinguishedPointHom_def, Category.assoc,
    Φ.affineToricChartι_comp_algebraicRealizationStructureMap, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext a
  exact (distinguishedPoint Φ.lattice (⊤ : σ.val.Face)).commutes a

/-- The distinguished point of a cone is a closed subscheme with residue field `ℂ`. -/
theorem isClosedImmersion_distinguishedPointHom (σ : Φ.cones) :
    IsClosedImmersion (Φ.distinguishedPointHom σ) :=
  isClosedImmersion_of_comp_eq_id Φ.algebraicRealizationStructureMap (Φ.distinguishedPointHom σ)
    (Φ.distinguishedPointHom_comp_algebraicRealizationStructureMap σ)

/-- The distinguished point of a cone is closed. -/
theorem isClosed_singleton_distinguishedPoint (σ : Φ.cones) :
    IsClosed ({Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ)} :
      Set Φ.algebraicRealization) := by
  let q := Φ.distinguishedPointHom σ
  have := Φ.isClosedImmersion_distinguishedPointHom σ
  have hr : Set.range q = {q (IsLocalRing.closedPoint ℂ)} :=
    Set.range_eq_singleton fun x ↦ congrArg q (Subsingleton.elim x _)
  exact hr ▸ q.isClosedEmbedding.isClosed_range

/-- The closed immersion of a cone's distinguished point cuts out its reduced vanishing ideal. -/
theorem ker_distinguishedPointHom_eq_vanishingIdeal (σ : Φ.cones) :
    let _ := Φ.isClosedImmersion_distinguishedPointHom σ
    (Φ.distinguishedPointHom σ).ker =
      vanishingIdeal ⟨_, (Φ.distinguishedPointHom σ).isClosedEmbedding.isClosed_range⟩ := by
  dsimp only
  let p := Φ.distinguishedPointHom σ
  have := Φ.isClosedImmersion_distinguishedPointHom σ
  have hs : (p.ker.support : Set Φ.algebraicRealization) = Set.range p :=
    p.support_ker.trans p.isClosedEmbedding.isClosed_range.closure_eq
  have he : p.ker.support = ⟨_, p.isClosedEmbedding.isClosed_range⟩ :=
    SetLike.coe_injective hs
  rw [← he]
  exact p.ker_eq_vanishingIdeal_support

end TauCeti.Toric.Fan

namespace TauCeti.Toric.FanEquiv

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'} (e : FanEquiv Φ Ψ)

/-- The scheme map of a fan equivalence sends the distinguished point of a cone
to the distinguished point of the image cone. -/
@[reassoc (attr := simp)]
theorem distinguishedPointHom_comp_algebraicMap (σ : Φ.cones) :
    Φ.distinguishedPointHom σ ≫ e.toFanHom.algebraicMap =
      Ψ.distinguishedPointHom (e.coneEquiv σ) := by
  classical
  let f := e.toFanHom
  let τ := e.coneEquiv σ
  let hm := e.mapsTo_coneEquiv σ
  let A := affineCoordinateRingMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice hm
  have hset : f.realMap '' (σ.val : Set V) = (τ.val : Set V') := by
    rw [e.coneEquiv_apply_coe, PointedCone.coe_map, toFanHom_realMap]
  have h (m : dualSemigroup Ψ.lattice τ.val) :
      (∀ x ∈ (⊤ : σ.val.Face), Φ.lattice.realCharacter
        (dualSemigroupMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice hm m) x = 0) ↔
      (∀ y ∈ (⊤ : τ.val.Face), Ψ.lattice.realCharacter m y = 0) := by
    simp only [coe_dualSemigroupMap, Φ.lattice.realCharacter_comp Ψ.lattice f.latticeMap
      f.realMap f.map_lattice, LinearMap.comp_apply]
    -- The top face is the cone itself, so its points are the image of the source cone.
    change (∀ x ∈ (σ.val : Set V), _) ↔ ∀ y ∈ (τ.val : Set V'), _
    simp only [← hset, Set.forall_mem_image]
  have he : (distinguishedPoint Φ.lattice (⊤ : σ.val.Face)).comp A =
      distinguishedPoint Ψ.lattice (⊤ : τ.val.Face) := by
    apply MonoidAlgebra.algHom_ext
    · intro m
      rw [← ofAdd_toAdd m, AlgHom.comp_apply, affineCoordinateRingMap_single,
        distinguishedPoint_apply_single, distinguishedPoint_apply_single, h]
    · exact Subsingleton.elim _ _
  rw [Fan.distinguishedPointHom_def, Fan.distinguishedPointHom_def, Category.assoc,
    e.toFanHom.affineToricChartι_comp_algebraicMap_of_mapsTo _ _ hm,
    affineToricSchemeMap_def, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hr : (distinguishedPoint Φ.lattice (⊤ : σ.val.Face)).toRingHom.comp A.toRingHom =
      (distinguishedPoint Ψ.lattice (⊤ : τ.val.Face)).toRingHom :=
    congrArg AlgHom.toRingHom he
  dsimp only [A, f, τ] at hr
  rw [hr]

end TauCeti.Toric.FanEquiv

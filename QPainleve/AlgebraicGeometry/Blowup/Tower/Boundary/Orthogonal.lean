/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Quotient
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
public import QPainleve.AlgebraicGeometry.Chow.SurfaceIntersection
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Boundary orthogonal complements of nodal blowup towers

In the Picard marking of a nodal blowup tower, the span of the reduced total
boundary is the direct sum of the original boundary span and the full
exceptional summand. Pullback thus identifies the orthogonal complements of the
two boundaries, with their integral intersection forms. The comparison
includes self-nodes and infinitely near centers.

The calculation uses the Picard splitting for point blowups and Picard excision
on the common boundary complement.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open LineBundleClass LinearMap.BilinForm

universe u

namespace QPainleve.BlowupTower.IsNodalBoundaryTower

variable {S K X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}
  {D : S.IdealSheafData} {s : S ⟶ K} {π : X ⟶ S}

private theorem pullback_exceptionalClass_eq_one (hT : IsNodalBoundaryTower D s π T)
    (j : Fin n) {Z : Scheme.{u}} (g : Z ⟶ Y) (hg : D.comap (g ≫ T.toBase ≫ π) = ⊤) :
    pullback g (T.exceptionalClass j) = 1 := by
  induction hT with
  | nil => exact j.elim0
  | @snoc d W R I _ p hp hI hnode ih =>
    have hg' : D.comap ((g ≫ I.blowupToBase) ≫ R.toBase ≫ π) = ⊤ := by
      rwa [toBase_snoc, Category.assoc I.blowupToBase R.toBase π,
        ← Category.assoc g I.blowupToBase] at hg
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · rw [exceptionalClass_snoc_last, ← I.blowupExceptionalClass_def]
      apply I.pullback_blowupExceptionalClass_eq_one
      rw [D.comap_comp (g ≫ I.blowupToBase), Scheme.IdealSheafData.comap_eq_top_iff] at hg'
      rw [I.comap_eq_top_iff, ← top_le_iff, ← hg']
      apply Scheme.Hom.preimage_mono
      have hsupport : (I.support : Set W) ⊆ (D.comap (R.toBase ≫ π)).support := by
        rw [hI, Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hp.closure_eq,
          Set.singleton_subset_iff]
        exact Scheme.IdealSheafData.mem_support_of_isNodeOfReducedBoundary hnode
      exact Set.compl_subset_compl.mpr hsupport
    · rw [exceptionalClass_snoc_castSucc, pullback_comp]
      exact ih i (g ≫ I.blowupToBase) hg'

local notation "Pic(" A ")" => Additive (LineBundleClass A)

variable {B : X.IdealSheafData} {f : X ⟶ K}

local notation "U" => Closeds.compl (Scheme.IdealSheafData.support B)
local notation "V" => Closeds.compl (Scheme.IdealSheafData.support (B.comap T.toBase))
local notation "M" => Scheme.Opens.primeDivisorSpanCompl U
local notation "N" => Scheme.Opens.primeDivisorSpanCompl V

section Span

variable [IsIntegral Y] [IsNoetherian Y] [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]

/-- Every total exceptional divisor class lies in the span of the final reduced boundary. -/
theorem exceptionalClass_mem_primeDivisorSpanCompl
    (hT : IsNodalBoundaryTower B f (𝟙 X) T) (j : Fin n) :
    Additive.ofMul (T.exceptionalClass j) ∈ N := by
  apply (Scheme.Opens.mem_primeDivisorSpanCompl_iff V _).mpr
  apply hT.pullback_exceptionalClass_eq_one
  rw [Category.comp_id, B.comap_comp, Scheme.IdealSheafData.comap_eq_top_iff,
    Scheme.Opens.ι_preimage_self]

variable [IsIntegral X] [IsNoetherian X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

/-- In the Picard coordinates of a nodal blowup tower, membership in the span of the
final boundary is exactly membership of the base coordinate in the original boundary span. -/
theorem picardHom_mem_primeDivisorSpanCompl_iff
    (hT : IsNodalBoundaryTower B f (𝟙 X) T) (a : Pic(X)) (b : Fin n → ℤ) :
    T.picardHom (a, b) ∈ N ↔ a ∈ M := by
  have hb : (∑ j, b j • Additive.ofMul (T.exceptionalClass j)) ∈ N :=
    Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (hT.exceptionalClass_mem_primeDivisorSpanCompl j)
  have ha : Additive.ofMul (pullback T.toBase a.toMul) ∈ N ↔ a ∈ M := by
    rw [← Submodule.Quotient.mk_eq_zero, ← hT.boundaryQuotientEquiv_mk a.toMul, ofMul_toMul,
      LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
  rw [picardHom_apply, Submodule.add_mem_iff_left _ hb, ha]

end Span

section Isometry

variable (k : Type u) [Field k] [IsAlgClosed k] [X.Over (Spec (.of k))]
  [X.IsProjectiveOver k] [IsIntegral X] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  (hT : IsNodalBoundaryTower B (X ↘ Spec (.of k)) (𝟙 X) T)

local notation "f₀" => (X ↘ Spec (CommRingCat.of k))
local notation "f₁" => (T.toBase ≫ f₀)

local notation "A₀" => Chow.intersectionBilinForm k X
local notation "A₁" => Chow.intersectionBilinForm k Y

/-- A class in the Picard marking is orthogonal to the final boundary exactly when its base
class is orthogonal to the original boundary and every exceptional coefficient is zero. -/
theorem picardHom_mem_boundaryOrthogonal_iff (a : Pic(X)) (b : Fin n → ℤ) :
    let : IsNoetherian X := isNoetherian_of_finiteType f₀
    let : IsNoetherian Y := T.isNoetherian
    let : Y.Over (Spec (.of k)) := ⟨f₁⟩
    let : Y.IsProjectiveOver k := T.isProjectiveOver k
    let : IsIntegral Y := hT.isClosedPointTower.isIntegral f₀
    let : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
      hT.isClosedPointTower.smoothOfRelativeDimension f₀
    let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      Scheme.Hom.uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two f₀
    let : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y) :=
      (Y ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    T.picardHom (a, b) ∈ (A₁).orthogonal N ↔ a ∈ (A₀).orthogonal M ∧ b = 0 := by
  intro _ _ _ _ _ _ _ _
  classical
  have hpair (x y : Pic(X) × (Fin n → ℤ)) :
      A₁ (T.picardHom x) (T.picardHom y) = A₀ x.1 y.1 - ∑ j, x.2 j * y.2 j := by
    simpa only [Chow.intersectionBilinForm_apply, picardMarking_apply] using
      classIntersectionNumber_picardMarking k hT.isClosedPointTower x y
  constructor
  · intro h
    refine ⟨mem_orthogonal_iff.mpr fun a' ha' ↦ ?_, funext fun j ↦ ?_⟩
    · have hz := mem_orthogonal_iff.mp h _
        ((hT.picardHom_mem_primeDivisorSpanCompl_iff a' 0).mpr ha')
      simpa [hpair] using hz
    · have hz := mem_orthogonal_iff.mp h _
        ((hT.picardHom_mem_primeDivisorSpanCompl_iff 0 (Pi.single j 1)).mpr (Submodule.zero_mem _))
      rw [hpair, ← dotProduct, single_dotProduct] at hz
      simpa using hz
  · rintro ⟨ha, rfl⟩
    refine mem_orthogonal_iff.mpr fun z hz ↦ ?_
    obtain ⟨⟨a', b'⟩, rfl⟩ := (hT.isClosedPointTower.bijective_picardHom f₀).surjective z
    have h := mem_orthogonal_iff.mp ha _ ((hT.picardHom_mem_primeDivisorSpanCompl_iff a' b').mp hz)
    simpa [hpair] using h

/-- Pullback along a nodal blowup tower is an integral isometry of the boundary orthogonal
complements, including when the restricted forms are degenerate. -/
def boundaryOrthogonalIsometry :
    let : IsNoetherian X := isNoetherian_of_finiteType f₀
    let : IsNoetherian Y := T.isNoetherian
    let : Y.Over (Spec (.of k)) := ⟨f₁⟩
    let : Y.IsProjectiveOver k := T.isProjectiveOver k
    let : IsIntegral Y := hT.isClosedPointTower.isIntegral f₀
    let : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
      hT.isClosedPointTower.smoothOfRelativeDimension f₀
    let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      Scheme.Hom.uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two f₀
    let : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y) :=
      (Y ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    ((A₀).restrict ((A₀).orthogonal M)).IsometryEquiv ((A₁).restrict ((A₁).orthogonal N)) := by
  intro _ _ _ _ _ _ _ _
  let e : (A₀).orthogonal M →ₗ[ℤ] (A₁).orthogonal N :=
    ((T.picardHom.comp (LinearMap.inl ℤ (Pic(X)) (Fin n → ℤ))).domRestrict
      ((A₀).orthogonal M)).codRestrict ((A₁).orthogonal N)
        (fun a ↦ (picardHom_mem_boundaryOrthogonal_iff k hT a 0).mpr ⟨a.property, rfl⟩)
  have hmark := hT.isClosedPointTower.bijective_picardHom f₀
  refine { LinearEquiv.ofBijective e ⟨?_, ?_⟩ with map_app' := ?_ }
  · intro a b h
    exact Subtype.ext (congrArg Prod.fst (hmark.injective (congrArg Subtype.val h)))
  · intro y
    obtain ⟨⟨a, b⟩, hab⟩ := hmark.surjective y.val
    have h : T.picardHom (a, b) ∈ (A₁).orthogonal N := hab.symm ▸ y.property
    obtain ⟨ha, rfl⟩ := (picardHom_mem_boundaryOrthogonal_iff k hT a b).mp h
    exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
  · intro a b
    -- The restricted pairings evaluate on the classes in their ambient Picard groups.
    change A₁ (T.picardHom (a.val, 0)) (T.picardHom (b.val, 0)) = A₀ a.val b.val
    simpa only [Chow.intersectionBilinForm_apply, picardMarking_apply, Prod.fst, Prod.snd,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero] using
      classIntersectionNumber_picardMarking k hT.isClosedPointTower (a.val, 0) (b.val, 0)

/-- The isometry is induced by line-bundle pullback on the ambient Picard groups. -/
@[simp] theorem boundaryOrthogonalIsometry_apply :
    let : IsNoetherian X := isNoetherian_of_finiteType f₀
    let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      Scheme.Hom.uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two f₀
    ∀ a : (A₀).orthogonal M,
      (boundaryOrthogonalIsometry k hT a : Pic(Y)) =
        Additive.ofMul (pullback T.toBase a.val.toMul) := by
  intro _ _ a
  -- Coercion into the Picard group forgets the membership proof of the restricted map.
  change T.picardHom (a.val, 0) = Additive.ofMul (pullback T.toBase a.val.toMul)
  exact congrArg Additive.ofMul (T.picardHom_apply_zero _)

end Isometry

end QPainleve.BlowupTower.IsNodalBoundaryTower

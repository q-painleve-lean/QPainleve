/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Boundary

/-!
# Recovering boundary actions from Picard pullbacks

When the marked source boundary classes distinguish the components, the Picard
pullback determines the inverse component permutation. The orientation then
recovers the full action on the numbered branches, even for a self-node or a
two-component boundary. These comparisons apply to realizations with different
center maps and domains.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup
open AlgebraicGeometry.Scheme

universe u

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

section Rotations

open AlgebraicGeometry.Scheme.PartialMap

variable {k : Type u} [Field k] [IsSepClosed k] [Infinite k] {n : ℕ} [NeZero n]
  {L₀ L₁ : Type u} [AddCommGroup L₀] [AddCommGroup L₁]
  {B₀ : LinearMap.BilinForm ℤ L₀} {B₁ : LinearMap.BilinForm ℤ L₁}
  {X₀ X₁ : Scheme.{u}} [IsIntegral X₀] [X₀.IsSeparated] [X₁.IsSeparated]
  {T₀ T₁ : Over (Spec (CommRingCat.of k))} [Nonempty T₀.left] [Smooth T₀.hom]
  {P₀ : Point T₀ → MarkedSurface k n B₀ X₀} {P₁ : Point T₁ → MarkedSurface k n B₁ X₁}
  {C : T₀.left.PartialMap T₁.left} [IsDominant C.hom] [C.IsOver T₀.hom T₁.hom]
  {F : X₀ ⤏ X₁} [F.IsDominant]

/-- Fiber realizations with a common Picard pullback and positive orientation assemble
into a geometric realization when the fixed marked boundary classes determine the image
of component zero. The source only needs a constant class for that one component. -/
theorem exists_of_fiber_rotations
    (I : B₁.IsometryEquiv B₀) (d₀ : L₀) (d₁ : ZMod n → L₁) (hinj : Function.Injective d₁)
    (h₀ : ∀ c : CenterPoint C, (P₀ (c ≫ C.domainSource)).pair.hom.left.ker.IsEffectiveCartier)
    (h₁ : ∀ c : CenterPoint C, (P₁ (c ≫ C.domainTarget)).pair.hom.left.ker.IsEffectiveCartier)
    (hmark₀ : ∀ c, (P₀ (c ≫ C.domainSource)).boundaryClass (h₀ c) 0 = d₀)
    (hmark₁ : ∀ c j, (P₁ (c ≫ C.domainTarget)).boundaryClass (h₁ c) j = d₁ j)
    (hf : ∀ c : CenterPoint C, ∃ j : ZMod n, Nonempty
      (FiberRealization (P₀ (c ≫ C.domainSource)) (P₁ (c ≫ C.domainTarget)) F I (r j))) :
    ∃ (R : GeometricRealization P₀ P₁ C F) (j : ZMod n),
      R.picard = I ∧ R.boundaryAction = r j ∧ I (d₁ j) = d₀ := by
  have hclass (c : CenterPoint C) (j : ZMod n)
      (R : FiberRealization (P₀ (c ≫ C.domainSource)) (P₁ (c ≫ C.domainTarget)) F I (r j)) :
      I (d₁ j) = d₀ := by
    simpa only [inv_r, cycleVertexPerm_r_apply, add_neg_cancel, hmark₀, hmark₁] using
      R.picard_boundaryClass (h₀ c) (h₁ c) j
  obtain ⟨c₀⟩ := nonempty_centerPoint C
  obtain ⟨j, ⟨R₀⟩⟩ := hf c₀
  have hj := hclass c₀ j R₀
  have fibers (c : CenterPoint C) : Nonempty
      (FiberRealization (P₀ (c ≫ C.domainSource)) (P₁ (c ≫ C.domainTarget)) F I (r j)) := by
    obtain ⟨j', ⟨R⟩⟩ := hf c
    have he := hinj (I.injective ((hclass c j' R).trans hj.symm))
    exact ⟨he ▸ R⟩
  exact ⟨⟨I, r j, fun c ↦ Classical.choice (fibers c)⟩, j, rfl, rfl, hj⟩

end Rotations

variable {k : Type u} [Field k] [IsSepClosed k] [Infinite k] {n : ℕ} [NeZero n]
  {L₀ L₁ : Type u} [AddCommGroup L₀] [AddCommGroup L₁]
  {B₀ : LinearMap.BilinForm ℤ L₀} {B₁ : LinearMap.BilinForm ℤ L₁}
  {X₀ X₁ : Scheme.{u}} [IsIntegral X₀] [X₀.IsSeparated] [X₁.IsSeparated]
  {T₀ T₁ : Over (Spec (CommRingCat.of k))} [Nonempty T₀.left] [Smooth T₀.hom]
  {P₀ : Point T₀ → MarkedSurface k n B₀ X₀} {P₁ : Point T₁ → MarkedSurface k n B₁ X₁}
  {C C' : T₀.left.PartialMap T₁.left} [IsDominant C.hom] [IsDominant C'.hom]
  [C.IsOver T₀.hom T₁.hom] [C'.IsOver T₀.hom T₁.hom]
  {F G : X₀ ⤏ X₁} [F.IsDominant] [G.IsDominant]
  (R : GeometricRealization P₀ P₁ C F) (R' : GeometricRealization P₀ P₁ C' G)
  {D₀ : ZMod n → L₀} {D₁ : ZMod n → L₁}
  {h₀ : ∀ c, (P₀ c).pair.hom.left.ker.IsEffectiveCartier}
  {h₁ : ∀ c, (P₁ c).pair.hom.left.ker.IsEffectiveCartier}

/-- Equal Picard pullbacks give the same component permutation when the boundary
classes are constant in the markings and the source classes distinguish the components. -/
theorem cycleVertexPerm_eq_of_picard_eq
    (hmark₀ : ∀ c j, (P₀ c).boundaryClass (h₀ c) j = D₀ j)
    (hmark₁ : ∀ c j, (P₁ c).boundaryClass (h₁ c) j = D₁ j)
    (hinj : Function.Injective D₀) (hI : R.picard = R'.picard) :
    cycleVertexPerm R.boundaryAction = cycleVertexPerm R'.boundaryAction := by
  obtain ⟨c⟩ := nonempty_centerPoint C
  obtain ⟨c'⟩ := nonempty_centerPoint C'
  -- Pullback compares the inverse permutations on any center in each domain.
  have hi : cycleVertexPerm R.boundaryAction⁻¹ = cycleVertexPerm R'.boundaryAction⁻¹ := by
    apply Equiv.ext
    intro j
    apply hinj
    have h := R.picard_boundaryClass c (h₀ _) (h₁ _) j
    have h' := R'.picard_boundaryClass c' (h₀ _) (h₁ _) j
    rw [hmark₁, hmark₀, hI] at h
    rw [hmark₁, hmark₀] at h'
    exact h.symm.trans h'
  exact inv_injective (by simpa only [map_inv] using hi)

/-- Equal Picard pullbacks and equal orientations give the same action on all numbered
branches, provided the boundary classes are constant in the markings and the source
classes distinguish the components. -/
theorem boundaryAction_eq_of_picard_eq_of_orientation_eq
    (hmark₀ : ∀ c j, (P₀ c).boundaryClass (h₀ c) j = D₀ j)
    (hmark₁ : ∀ c j, (P₁ c).boundaryClass (h₁ c) j = D₁ j)
    (hinj : Function.Injective D₀) (hI : R.picard = R'.picard)
    (horient : R.orientation = R'.orientation) : R.boundaryAction = R'.boundaryAction := by
  have hperm := R.cycleVertexPerm_eq_of_picard_eq R' hmark₀ hmark₁ hinj hI
  let g := R.boundaryAction / R'.boundaryAction
  have hg : cycleOrientationSign g = 1 := by
    dsimp only [g]
    rw [map_div, ← R.orientation_def, ← R'.orientation_def, horient, div_self']
  have hzero : cycleVertexPerm g 0 = 0 := by
    dsimp only [g]
    rw [map_div, hperm, div_self', Equiv.Perm.one_apply]
  exact eq_of_div_eq_one (((eq_r_iff_cycleVertexPerm_zero_eq hg).mpr hzero).trans one_def.symm)

end QPainleve.SignedClusterModularGroup.GeometricRealization

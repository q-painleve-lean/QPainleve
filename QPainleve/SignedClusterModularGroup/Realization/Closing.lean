/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.Basic
public import QPainleve.SignedClusterModularGroup.Realization.Iteration

import QPainleve.SignedClusterModularGroup.Realization.BranchAction

/-!
# Closing marked toric realizations

At a reached center, an oriented common toric refinement identifies two ordered
models with matching charges. Pullback to the common refinement describes the
graph of the Picard isometry independently of the center. Composing the fiber
comparisons closes a realization on its original center domain. Its orientation
and the image of the first component determine the action on the ordered branches.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open DihedralGroup
open Module (Basis)
open QPainleve.CharacterTorus
open Scheme Scheme.PartialMap Scheme.IdealSheafData
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open LineBundleClass (IsNef pullback)

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "Dtor[" Φ "," h "]" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h)
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {m n : ℕ} [NeZero n]
  {L₀ L₁ L₂ : Type} [AddCommGroup L₀] [AddCommGroup L₁] [AddCommGroup L₂]
  {B₀ : LinearMap.BilinForm ℤ L₀} {B₁ : LinearMap.BilinForm ℤ L₁}
  {B₂ : LinearMap.BilinForm ℤ L₂}

local notation "Centers[" j "]" => Over.mk (structureMap ℂ (Fin j → ℤ))
local notation "XTor" => scheme ℂ (Fin m →₀ ℤ)

variable {P₀ : Point Centers[m] → MarkedSurface ℂ n B₀ (scheme ℂ (Fin m →₀ ℤ))}
  {P₁ : Point Centers[m] → MarkedSurface ℂ n B₁ (scheme ℂ (Fin m →₀ ℤ))}
  {P₂ : Point Centers[m] → MarkedSurface ℂ n B₂ (scheme ℂ (Fin m →₀ ℤ))}
  {C : (scheme ℂ (Fin m → ℤ)).PartialMap (scheme ℂ (Fin m → ℤ))}
  [IsDominant C.hom] [C.IsOver (Centers[m]).hom (Centers[m]).hom]
  {F : scheme ℂ (Fin m →₀ ℤ) ⤏ scheme ℂ (Fin m →₀ ℤ)} [F.IsDominant]

local notation "PointC" => CenterPoint (U := Centers[m]) (V := Centers[m]) C
local notation "src(" c ")" => (c) ≫ domainSource (X := Centers[m]) (Y := Centers[m]) C
local notation "dst(" c ")" => (c) ≫ domainTarget (X := Centers[m]) (Y := Centers[m]) C

private theorem exists_comp_fiber_rotations
    (R : GeometricRealization P₀ P₁ C F)
    (d₀ : L₀) (d : ZMod n → L₂) (hd : Function.Injective d)
    (hcart₀ : ∀ c : PointC, D[P₀ (src(c))].IsEffectiveCartier)
    (hcart₂ : ∀ c : PointC, D[P₂ (dst(c))].IsEffectiveCartier)
    (hmark₀ : ∀ c : PointC, (P₀ (src(c))).boundaryClass (hcart₀ c) 0 = d₀)
    (hmark₂ : ∀ (c : PointC) j, (P₂ (dst(c))).boundaryClass (hcart₂ c) j = d j)
    (compare : L₁ → L₂ → Prop)
    (h : ∀ c : PointC, ∃ (I : B₂.IsometryEquiv B₁) (j : ZMod n),
      Nonempty (FiberRealization (P₁ (dst(c))) (P₂ (dst(c))) (RationalMap.id XTor)
        I (DihedralGroup.r j)) ∧ ∀ x y, I y = x ↔ compare x y) :
    ∃ (I : B₂.IsometryEquiv B₁) (T : GeometricRealization P₀ P₂ C F),
      T.picard = I.trans R.picard ∧ T.orientation = R.orientation ∧
      (∀ x y, I y = x ↔ compare x y) ∧ T.picard (d (T.boundaryPerm 0)) = d₀ := by
  obtain ⟨c₀⟩ := nonempty_centerPoint (T₀ := Centers[m]) (T₁ := Centers[m]) C
  obtain ⟨I, _, _, hI⟩ := h c₀
  have hf (c : PointC) :
      ∃ g : DihedralGroup n, cycleOrientationSign g = R.orientation ∧
        Nonempty (FiberRealization (P₀ (src(c))) (P₂ (dst(c))) F (I.trans R.picard) g) := by
    obtain ⟨I', l, ⟨T⟩, hI'⟩ := h c
    have he : I = I' := DFunLike.ext _ _ fun y ↦ (hI (I' y) y).mpr ((hI' (I' y) y).mp rfl)
    subst I'
    refine ⟨DihedralGroup.r l * R.boundaryAction, by simp [R.orientation_def], ⟨?_⟩⟩
    simpa only [F.comp_id] using FiberRealization.comp (M := P₀ (src(c)))
      (N := P₁ (dst(c))) (O := P₂ (dst(c))) (F := F) (G := RationalMap.id XTor)
      (I := R.picard) (J := I) (g := R.boundaryAction) (h := DihedralGroup.r l) (R.fiber c) T
  obtain ⟨U, hpic, hsign, hfirst⟩ :=
    exists_of_fiber_boundary_actions (I.trans R.picard) R.orientation
      d₀ d hd hcart₀ hcart₂ hmark₀ hmark₂ hf
  exact ⟨I, U, hpic, hsign, hI, hpic.symm ▸ hfirst⟩

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {b : Basis (Fin 2) ℤ N} {b' : Basis (Fin 2) ℤ N'}
  {α α' : Type}
  (Q : CompleteToricPresentation i b m L₁ α) (Q' : CompleteToricPresentation i' b' m L₂ α')

local notation "Q₀" => Q.complete.nonempty_cones
local notation "Q₀'" => Q'.complete.nonempty_cones

variable (e : N ≃ₗ[ℤ] N') {Δ : Fan i}
  (hΔQ : Δ.IsSubdivision Q.fan) (hΔQ' : Δ.IsSubdivision (Q'.fan.mapEquiv Q.fan.lattice e.symm))

local notation "g" => Fan.mapEquivIso Q'.fan Q.fan.lattice e.symm
local notation "hΩ" => Nonempty.map (FanEquiv.coneEquiv g) Q₀'
local notation "hΔ₀" => Fan.IsSubdivision.nonempty_cones_of_nonempty hΔQ Q₀
local notation "leftBoundary" => Fan.IsSubdivision.boundaryMap hΔQ hΔ₀ Q₀
local notation "rightBoundary" =>
  Fan.IsSubdivision.boundaryMap hΔQ' hΔ₀ hΩ ≫ Iso.inv (FanEquiv.boundaryIso g Q₀' hΩ)

private theorem rename_refl_toRationalMap :
    (Spec.map (CommRingCat.ofHom (LaurentRing.rename (R := ℂ)
      (Equiv.refl (Fin m)).toFun).toRingHom)).toRationalMap = RationalMap.id XTor := by
  have he : (Equiv.refl (Fin m)).toFun = id := rfl
  rw [he, LaurentRing.rename_id]
  exact congrArg Scheme.Hom.toRationalMap (Spec.map_id _)

/-- Close a geometric realization by identifying its reached toric models with the
desired endpoint models at the same centers. The charge identification and oriented
common refinement are fixed across the fibers. The new realization is defined on
the entire original center domain, with the same rational X map and orientation.
Its marked pullback composes with the isometry computed in the common refinement
and sends the class of the image of component zero to its original class. -/
theorem exists_comp_marked_toric_endpoint_comparison
    (R : GeometricRealization P₀ P₁ C F)
    (hΔ : Δ.IsRegular)
    (hcharge : ∀ j, e (Q.rays j).primitiveGenerator = (Q'.rays j).primitiveGenerator)
    (hdet : ∀ x y, b'.detDualEquiv (e x) (e y) = b.detDualEquiv x y)
    [PrestableFamily (Dtor[Δ,hΔ₀] ↘ S)] {k : ℕ} [NeZero k] {β : Type*}
    {a : β → (Dtor[Δ,hΔ₀] ↘ S).smoothLocus} (U : Scheme.NodalCycleNumbering a k)
    (hleft : letI := Q.prestable; letI := Q.neZero
      (leftBoundary).IsOrientedCycleSubdivision U Q.cycle)
    (hright : letI := Q'.prestable; letI := Q'.neZero
      (rightBoundary).IsOrientedCycleSubdivision U Q'.cycle)
    (hmodel₁ : ∀ c : PointC, Q.HasNodalModel (dst(c)) (P₁ (dst(c))))
    (hmodel₂ : ∀ c : PointC, Q'.HasNodalModel (dst(c)) (P₂ (dst(c))))
    (hcart₀ : ∀ c : PointC, D[P₀ (src(c))].IsEffectiveCartier)
    (hcart₂ : ∀ c : PointC, D[P₂ (dst(c))].IsEffectiveCartier)
    (hnef₀ : ∀ c : PointC, IsNef ℂ ((P₀ (src(c))).surface ↘ S) classOf(hcart₀ c))
    (hnef₂ : ∀ c : PointC, IsNef ℂ ((P₂ (dst(c))).surface ↘ S) classOf(hcart₂ c))
    (hsq₀ : ∀ c : PointC, Chow.classIntersectionNumber ℂ (P₀ (src(c))).surface
      classOf(hcart₀ c) classOf(hcart₀ c) = 0)
    (hsq₂ : ∀ c : PointC, Chow.classIntersectionNumber ℂ (P₂ (dst(c))).surface
      classOf(hcart₂ c) classOf(hcart₂ c) = 0)
    (d₀ : L₀) (d : ZMod n → L₂) (hd : Function.Injective d)
    (hmark₀ : ∀ c : PointC, (P₀ (src(c))).boundaryClass (hcart₀ c) 0 = d₀)
    (hmark₂ : ∀ (c : PointC) j, (P₂ (dst(c))).boundaryClass (hcart₂ c) j = d j) :
    ∃ (I : B₂.IsometryEquiv B₁) (T : GeometricRealization P₀ P₂ C F),
      T.picard = I.trans R.picard ∧ T.orientation = R.orientation ∧
      (∀ (x : L₁) (y : L₂), I y = x ↔
        (Additive.ofMul (pullback hΔQ.toFanHom.algebraicMap (Q.inclusion x).1.toMul),
          (Q.inclusion x).2) =
        (Additive.ofMul (pullback (hΔQ'.toFanHom.algebraicMap ≫ (g).symm.toFanHom.algebraicMap)
            (Q'.inclusion y).1.toMul), (Q'.inclusion y).2)) ∧
      T.picard (d (T.boundaryPerm 0)) = d₀ := by
  let : Nonempty Q.fan.cones := Q₀
  let : Nonempty Q'.fan.cones := Q₀'
  let : PrestableFamily (Dtor[Q.fan,Q₀] ↘ S) := Q.prestable
  let : PrestableFamily (Dtor[Q'.fan,Q₀'] ↘ S) := Q'.prestable
  let : NeZero Q.length := Q.neZero
  let : NeZero Q'.length := Q'.neZero
  refine exists_comp_fiber_rotations R d₀ d hd hcart₀ hcart₂ hmark₀ hmark₂ _ fun c ↦ ?_
  obtain ⟨p, _, _, _, u, hp, hpu⟩ := (Q.hasNodalModel_iff _ _).mp (hmodel₁ c)
  obtain ⟨q, _, _, _, v, hq, hqv⟩ := (Q'.hasNodalModel_iff _ _).mp (hmodel₂ c)
  obtain ⟨hcart₁, hnef₁, hsq₁⟩ := MarkedSurface.exists_nef_square_zero_boundary_of_pairIso
    (R.fiber c).iso (hcart₀ c) (hnef₀ c) (hsq₀ c)
  obtain ⟨comparison⟩ := p.nonempty_markedToricEndpointComparison q e hΔQ hΔQ' hΔ
    (Equiv.refl _) (Function.comp_id _) (fun j ↦ hcharge j) hdet
    (fun j l hj hl ↦ (not_lt_of_gt hj hl).elim) hp hq u v hpu.symm hqv.symm
    hcart₁ (hcart₂ c) hnef₁ (hnef₂ c) hsq₁ (hsq₂ c) U hleft hright
  refine ⟨comparison.picard, comparison.rotation, ⟨?_⟩, ?_⟩
  · simpa only [Equiv.refl_symm, rename_refl_toRationalMap] using comparison.fiber
  · intro x y
    simpa only [Equiv.coe_refl, Function.comp_id] using comparison.picard_apply_eq_iff x y

end QPainleve.SignedClusterModularGroup.GeometricRealization

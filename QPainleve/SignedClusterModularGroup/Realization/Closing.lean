/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.Basic
public import QPainleve.SignedClusterModularGroup.Realization.Iteration

import QPainleve.AlgebraicGeometry.Chow.Isomorphism
import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef.Pullback
import QPainleve.SignedClusterModularGroup.Realization.BranchAction

/-!
# Closing marked toric realizations

At a reached center, an oriented common toric refinement identifies two ordered
models with matching charges. Pullback to the common refinement describes the
graph of the Picard isometry independently of the center. The class of the first
boundary component then determines the common branch rotation. Composing the
fiber comparisons closes a realization on its original center domain.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open DihedralGroup (cycleVertexPerm eq_r_iff_cycleVertexPerm_zero_eq r_mul_r)
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
    (R : GeometricRealization P₀ P₁ C F) (hR : R.orientation = 1)
    (d₀ : L₀) (d : ZMod n → L₂) (hd : Function.Injective d)
    (hcart₀ : ∀ c : PointC, D[P₀ (src(c))].IsEffectiveCartier)
    (hcart₂ : ∀ c : PointC, D[P₂ (dst(c))].IsEffectiveCartier)
    (hmark₀ : ∀ c : PointC, (P₀ (src(c))).boundaryClass (hcart₀ c) 0 = d₀)
    (hmark₂ : ∀ (c : PointC) j, (P₂ (dst(c))).boundaryClass (hcart₂ c) j = d j)
    (compare : L₁ → L₂ → Prop)
    (h : ∀ c : PointC, ∃ (I : B₂.IsometryEquiv B₁) (j : ZMod n),
      Nonempty (FiberRealization (P₁ (dst(c))) (P₂ (dst(c))) (RationalMap.id XTor)
        I (DihedralGroup.r j)) ∧ ∀ x y, I y = x ↔ compare x y) :
    ∃ (I : B₂.IsometryEquiv B₁) (j : ZMod n) (T : GeometricRealization P₀ P₂ C F),
      T.picard = I.trans R.picard ∧ T.boundaryAction = DihedralGroup.r j ∧
      (∀ x y, I y = x ↔ compare x y) ∧ T.picard (d j) = d₀ := by
  obtain ⟨c₀⟩ := nonempty_centerPoint (T₀ := Centers[m]) (T₁ := Centers[m]) C
  obtain ⟨I, _, _, hI⟩ := h c₀
  let j₀ := cycleVertexPerm R.boundaryAction 0
  have hr : R.boundaryAction = DihedralGroup.r j₀ := by
    rw [orientation_def] at hR
    exact (eq_r_iff_cycleVertexPerm_zero_eq (j := j₀) hR).mpr rfl
  have hf (c : PointC) :
      ∃ j : ZMod n, Nonempty (FiberRealization (P₀ (src(c))) (P₂ (dst(c))) F
        (I.trans R.picard) (DihedralGroup.r j)) := by
    obtain ⟨I', l, ⟨T⟩, hI'⟩ := h c
    have he : I = I' := DFunLike.ext _ _ fun y ↦ (hI (I' y) y).mpr ((hI' (I' y) y).mp rfl)
    subst I'
    let j := l + j₀
    have hmap : F.comp (RationalMap.id XTor) = F := F.comp_id
    have hact : DihedralGroup.r l * R.boundaryAction = DihedralGroup.r j := by
      rw [hr, r_mul_r]
    refine ⟨j, ⟨?_⟩⟩
    simpa only [hmap, hact] using FiberRealization.comp (M := P₀ (src(c)))
      (N := P₁ (dst(c))) (O := P₂ (dst(c))) (F := F) (G := RationalMap.id XTor)
      (I := R.picard) (J := I) (g := R.boundaryAction) (h := DihedralGroup.r l) (R.fiber c) T
  obtain ⟨U, j, hpic, hact, hj⟩ :=
    exists_of_fiber_rotations (I.trans R.picard) d₀ d hd hcart₀ hcart₂ hmark₀ hmark₂ hf
  exact ⟨I, j, U, hpic, hact, hI, hpic.symm ▸ hj⟩

private theorem exists_nef_square_zero_boundary_of_pairIso
    {M : MarkedSurface ℂ n B₀ XTor} {M' : MarkedSurface ℂ n B₁ XTor}
    (f : M.pair ≅ M'.pair) (h : D[M].IsEffectiveCartier)
    (hnef : IsNef ℂ (M.surface ↘ S) classOf(h))
    (hsq : Chow.classIntersectionNumber ℂ M.surface classOf(h) classOf(h) = 0) :
    ∃ h' : D[M'].IsEffectiveCartier, IsNef ℂ (M'.surface ↘ S) classOf(h') ∧
      Chow.classIntersectionNumber ℂ M'.surface classOf(h') classOf(h') = 0 := by
  let e := MarkedSurface.surfaceIso f.symm
  let : e.hom.IsOver S := inferInstanceAs ((MarkedSurface.surfaceIso f.symm).hom.IsOver S)
  have hker : D[M].comap e.hom = D[M'] := by
    have hb := congrArg Scheme.Hom.ker (MarkedSurface.boundaryIso_hom_comp f.symm)
    rw [Scheme.Hom.ker_comp_of_isIso] at hb
    rw [hb, Scheme.Hom.comap_ker_comp_of_isClosedImmersion]
  have hc := h.comap e.hom
  let h' : D[M'].IsEffectiveCartier := hker ▸ hc
  have hclass : pullback e.hom classOf(h) = classOf(h') := by
    rw [LineBundleClass.pullback_inv, h.pullback_mk_toInvertibleSheaf hc,
      LineBundleClass.mk_toInvertibleSheaf_congr hc h' hker]
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : Smooth (M.surface ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : M.surface.IsProjectiveOver ℂ := M.projective
  refine ⟨h', hclass ▸ hnef.pullback e.hom, ?_⟩
  rw [← hclass, Chow.classIntersectionNumber_pullback_of_isIso, hsq]

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
the entire original center domain, with the same rational X map. Its marked pullback
composes with the isometry computed in the common refinement and its branch rotation
sends component zero to the unique component with the required pullback class. -/
theorem exists_comp_marked_toric_endpoint_comparison
    (R : GeometricRealization P₀ P₁ C F) (hR : R.orientation = 1)
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
    ∃ (I : B₂.IsometryEquiv B₁) (j : ZMod n) (T : GeometricRealization P₀ P₂ C F),
      T.picard = I.trans R.picard ∧ T.boundaryAction = DihedralGroup.r j ∧
      (∀ (x : L₁) (y : L₂), I y = x ↔
        (Additive.ofMul (pullback hΔQ.toFanHom.algebraicMap (Q.inclusion x).1.toMul),
          (Q.inclusion x).2) =
        (Additive.ofMul (pullback (hΔQ'.toFanHom.algebraicMap ≫ (g).symm.toFanHom.algebraicMap)
          (Q'.inclusion y).1.toMul), (Q'.inclusion y).2)) ∧ T.picard (d j) = d₀ := by
  let : Nonempty Q.fan.cones := Q₀
  let : Nonempty Q'.fan.cones := Q₀'
  let : PrestableFamily (Dtor[Q.fan,Q₀] ↘ S) := Q.prestable
  let : PrestableFamily (Dtor[Q'.fan,Q₀'] ↘ S) := Q'.prestable
  let : NeZero Q.length := Q.neZero
  let : NeZero Q'.length := Q'.neZero
  refine exists_comp_fiber_rotations R hR d₀ d hd hcart₀ hcart₂ hmark₀ hmark₂ _ fun c ↦ ?_
  obtain ⟨p, _, _, _, u, hp, hpu⟩ := (Q.hasNodalModel_iff _ _).mp (hmodel₁ c)
  obtain ⟨q, _, _, _, v, hq, hqv⟩ := (Q'.hasNodalModel_iff _ _).mp (hmodel₂ c)
  obtain ⟨hcart₁, hnef₁, hsq₁⟩ := exists_nef_square_zero_boundary_of_pairIso (R.fiber c).iso
    (hcart₀ c) (hnef₀ c) (hsq₀ c)
  obtain ⟨I, j, E, -, hI, -⟩ := p.exists_marked_toric_endpoint_comparison q e hΔQ hΔQ' hΔ
    (Equiv.refl _) (Function.comp_id _) (fun j ↦ hcharge j) hdet
    (fun j l hj hl ↦ (not_lt_of_gt hj hl).elim) hp hq u v hpu.symm hqv.symm
    hcart₁ (hcart₂ c) hnef₁ (hnef₂ c) hsq₁ (hsq₂ c) U hleft hright
  refine ⟨I, j, ⟨?_⟩, ?_⟩
  · simpa only [Equiv.refl_symm, rename_refl_toRationalMap] using E
  · simpa only [Equiv.coe_refl, Function.comp_id] using hI

end QPainleve.SignedClusterModularGroup.GeometricRealization

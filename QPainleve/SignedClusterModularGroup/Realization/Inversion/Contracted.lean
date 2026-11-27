/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.SignedClusterModularGroup.Realization.Agreement
public import QPainleve.SignedClusterModularGroup.Realization.Inversion.Basic

import QPainleve.Geometry.Toric.Fan.TorusAction.Orientation.Reversal

/-!
# Signed inversion of ordered toric presentations

Reversing the oriented lattice basis and inverting the center character gives
the same ordered centers. The identity of the underlying marked surface realizes
signed inversion and carries its specified nodal contraction to the opposite
frame. Both the toric and contracted boundary numberings reverse, so the boundary
map still respects the ordered branches of the subdivision.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open QPainleve.BlowupTower QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric TauCeti.Toric.Fan
open Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup

variable {k : Type} [Field k] [IsAlgClosed k]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  {r m n : ℕ} [NeZero m] [NeZero n] {L : Type} [AddCommGroup L]
  {B : LinearMap.BilinForm ℤ L}
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}

local notation "S" => Spec (CommRingCat.of k)
local notation "D[" Φ "," h "]" => Scheme.IdealSheafData.subscheme (Fan.toricBoundaryIdeal k Φ h)
local notation "XTor[" r "]" => Spec (CommRingCat.of (TauCeti.LaurentRing k (Fin r)))
local notation "Pic[" Φ "," r "]" =>
  Additive (LineBundleClass (Fan.finiteFanScheme k Φ)) × (Fin r → ℤ)
local notation "opBasis" b:arg => Module.Basis.reindex b (Equiv.swap 0 1)
local notation "centers" c:arg => (fun j ↦ c (ofAdd (Pi.single j 1)))
local notation "tower(" b "," s "," c ")" => internalBlowupTower k b s (centers c)

variable [PrestableFamily ((Φ.toricBoundaryIdeal k h₀).subscheme ↘ Spec (.of k))]
  {γ : Type*} {a : γ → ((Φ.toricBoundaryIdeal k h₀).subscheme ↘ Spec (.of k)).smoothLocus}
  {T : Scheme.NodalCycleNumbering a m} {o : ZMod m}
  {J : L →ₗ[ℤ] Additive (LineBundleClass (Φ.finiteFanScheme k)) × (Fin r → ℤ)}

local notation "modelIso(" b "," s "," c ")" => eqToIso (congrArg Sigma.fst
  (@id (tower(opBasis b,s,c⁻¹) = tower(b,s,c))
    (internalBlowupTower_reindex_swap k b s (centers c))))

namespace ContractedToricFiber

variable {c : Multiplicative (Fin r → ℤ) →* kˣ}
  {M : MarkedSurface k n B (Spec (.of (TauCeti.LaurentRing k (Fin r))))}
  (p : ContractedToricFiber (h₀ := h₀) b s hΦ T o J c M)

private theorem marked_pullback_invert
    (e : (tower(opBasis b,s,c⁻¹)).1 ≅ (tower(b,s,c)).1)
    (hpic : ∀ a, LineBundleClass.pullback e.inv
        (internalBlowupPicardMarking k (opBasis b) s (centers(c⁻¹)) hΦ a).toMul =
        (internalBlowupPicardMarking k b s (centers c) hΦ a).toMul)
    (x : L) :
    (internalBlowupPicardMarking k (opBasis b) s (centers(c⁻¹)) hΦ).symm
      (Additive.ofMul (LineBundleClass.pullback (e.hom ≫ p.projection)
        (M.picardMarking x).toMul)) = J x := by
  have hx := congrArg (fun a ↦ (internalBlowupPicardMarking k b s (centers c) hΦ a).toMul)
    (p.marked_pullback x)
  have hx' : LineBundleClass.pullback p.projection (M.picardMarking x).toMul =
      (internalBlowupPicardMarking k b s (centers c) hΦ (J x)).toMul := by
    simpa only [LinearEquiv.apply_symm_apply, toMul_ofMul] using hx
  have hm : LineBundleClass.pullback (e.hom ≫ p.projection) (M.picardMarking x).toMul =
      (internalBlowupPicardMarking k (opBasis b) s (centers(c⁻¹)) hΦ (J x)).toMul := by
    rw [← LineBundleClass.pullback_comp, hx', ← hpic, LineBundleClass.pullback_comp,
      Iso.hom_inv_id, LineBundleClass.pullback_id]
  rw [LinearEquiv.symm_apply_eq, hm, ofMul_toMul]

/-- Read a contracted ordered toric model in the opposite frame. The auxiliary
origin is reindexed by negation and the Picard inclusion is the same. This
construction also applies to repeated and infinitely near centers. -/
def invert : ContractedToricFiber (h₀ := h₀) (opBasis b) s hΦ T.reverse (-o) J c⁻¹
    (M.invert (ι := Fin r)) := by
  let e : (tower(opBasis b,s,c⁻¹)).1 ≅ (tower(b,s,c)).1 := modelIso(b,s,c)
  obtain ⟨hbase, hboundary, hpic⟩ := internalBlowupTower_reindex_swap_iso k b s (centers c) hΦ
  have hbase_inv : e.inv ≫ (tower(opBasis b,s,c⁻¹)).2.toTower.toBase =
      (tower(b,s,c)).2.toTower.toBase := hbase
  have hboundary_inv : (tower(b,s,c)).2.boundaryι ≫ e.inv =
      (tower(opBasis b,s,c⁻¹)).2.boundaryι := hboundary
  have hbase_forward : e.hom ≫ (tower(b,s,c)).2.toTower.toBase =
      (tower(opBasis b,s,c⁻¹)).2.toTower.toBase := by
    rw [← hbase_inv, Iso.hom_inv_id_assoc]
  have hboundary_forward : (tower(opBasis b,s,c⁻¹)).2.boundaryι ≫ e.hom =
      (tower(b,s,c)).2.boundaryι := by
    rw [← hboundary_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let : PrestableFamily (M.boundary ↘ S) := M.prestable
  refine {
    projection := e.hom ≫ p.projection
    modification := inferInstanceAs (IsModification (e.hom ≫ p.projection))
    projection_over := ?_
    support_comap := ?_
    boundaryMap := p.boundaryMap
    boundary_comp := ?_
    boundary_over := inferInstanceAs (p.boundaryMap.IsOver S)
    orientedSubdivision := p.orientedSubdivision.reverse
    component_zero := ?_
    marked_pullback := ?_
    evaluation_eq := ?_ }
  · exact (Category.assoc _ _ _).trans
      ((congrArg (e.hom ≫ ·) p.projection_over).trans
        ((reassoc_of% hbase_forward) (Φ.finiteFanSchemeToSpec k)))
  · have hker : (tower(b,s,c)).2.boundaryι.ker.comap e.hom =
        (tower(opBasis b,s,c⁻¹)).2.boundaryι.ker := by
      rw [← hboundary_forward, Scheme.Hom.comap_ker_comp_of_isClosedImmersion]
    have hD := congrArg (·.preimage e.hom.continuous) p.support_comap
    rw [← Scheme.IdealSheafData.support_comap, ← Scheme.IdealSheafData.support_comap,
      ← Scheme.IdealSheafData.comap_comp, hker] at hD
    exact hD
  · exact p.boundary_comp.trans ((reassoc_of% hboundary_forward) p.projection).symm
  · have hzero : p.boundaryMap (T.reverse.componentGenericPoint (-o)) =
        M.cycle.reverse.componentGenericPoint 0 := by
      rw [T.reverse_componentGenericPoint, M.cycle.reverse_componentGenericPoint, neg_neg, neg_zero]
      exact p.component_zero
    exact hzero
  · intro x
    rw [MarkedSurface.invert_picardMarking]
    exact marked_pullback_invert p e (fun a ↦ hpic a) x
  · rw [MarkedSurface.invert_evaluation, p.evaluation_eq]
    exact (contractedXEvaluation_reindex_swap k b s c hΦ p.projection
      (e.hom ≫ p.projection) rfl).symm

/-- Inversion transports the contraction by the canonical identification of the
ordered models. The marked surface itself is fixed. -/
@[simp]
theorem invert_projection : p.invert.projection = (modelIso(b,s,c)).hom ≫ p.projection := (rfl)

/-- The boundary restriction of the inverted contraction is the original map. -/
@[simp]
theorem invert_boundaryMap : p.invert.boundaryMap = p.boundaryMap := (rfl)

end ContractedToricFiber

namespace GeometricRealization

local notation "Centers[" r "]" => Over.mk (structureMap k (Fin r → ℤ))
local notation "χ[" r "](" y ")" => pointsEquiv k (Fin r → ℤ)
  (Subtype.mk (CommaMorphism.left y) (Over.w y))

variable (E : SkewExchangeMatrix (Fin r))

local notation "invCenters" E:arg =>
  Quiver.Path.centerIsoOver k (Quiver.Hom.toPath (Generator.toStep Generator.invert E))

omit [IsAlgClosed k] in
private theorem character_comp_invert_inv (y : Point Centers[r]) :
    χ[r](y ≫ (invCenters E).inv)⁻¹ = χ[r](y) := by
  apply (pointsEquiv k (Fin r → ℤ)).symm.injective
  apply Subtype.ext
  rw [← Quiver.Path.pointsEquiv_symm_comp_centerIso_hom_invert k,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← Quiver.Path.centerIsoOver_hom_left,
    ← Over.comp_left, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The target family of the inversion realization has the opposite ordered toric
presentation at the actual image center. The same nodal tower presents the
target, with all Picard coordinates and all of its centers in the original order.
Only the source fiber at the inverse center is needed. -/
theorem exists_invert_contracted
    (P : Point Centers[r] → MarkedSurface k n B XTor[r]) (y : Point Centers[r])
    (p : ContractedToricFiber (h₀ := h₀) b s hΦ T o J χ[r](y ≫ (invCenters E).inv)
      (P (y ≫ (invCenters E).inv)))
    {Y : Scheme} {j : ℕ}
    (R : BlowupTower (P (y ≫ (invCenters E).inv)).surface j Y)
    (d : Y ≅ (tower(b,s,χ[r](y ≫ (invCenters E).inv))).1)
    (hR : IsNodalBoundaryTower (P (y ≫ (invCenters E).inv)).pair.hom.left.ker
      ((P (y ≫ (invCenters E).inv)).surface ↘ S) (𝟙 _) R)
    (hp : p.projection = d.inv ≫ R.toBase) :
    ∃ (q : ContractedToricFiber (h₀ := h₀) (opBasis b) s hΦ T.reverse (-o) J χ[r](y)
        ((P (y ≫ (invCenters E).inv)).invert (ι := Fin r)))
      (d' : Y ≅ (tower(opBasis b,s,χ[r](y))).1),
      IsNodalBoundaryTower ((P (y ≫ (invCenters E).inv)).invert (ι := Fin r)).pair.hom.left.ker
        (((P (y ≫ (invCenters E).inv)).invert (ι := Fin r)).surface ↘ S) (𝟙 _) R ∧
      q.projection = d'.inv ≫ R.toBase ∧ q.boundaryMap = p.boundaryMap := by
  rw [← character_comp_invert_inv E y]
  refine ⟨p.invert, d ≪≫ (modelIso(b,s,χ[r](y ≫ (invCenters E).inv))).symm,
    hR, ?_, p.invert_boundaryMap⟩
  rw [ContractedToricFiber.invert_projection, hp, Iso.trans_inv, Iso.symm_inv, Category.assoc]

end GeometricRealization

end QPainleve.SignedClusterModularGroup

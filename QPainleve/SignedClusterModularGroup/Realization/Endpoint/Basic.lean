/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Period.Orientation
public import QPainleve.Geometry.Toric.Fan.Subdivision.Endpoint
public import QPainleve.SignedClusterModularGroup.Realization.Agreement

import QPainleve.AlgebraicGeometry.Chow.Isomorphism
import QPainleve.Geometry.Toric.Fan.Boundary.Refinement
import QPainleve.SignedClusterModularGroup.Realization.Boundary

/-!
# Marked comparison at the endpoints of a cluster word

A common toric subdivision compares the terminal presentation of a word with the
initial presentation evaluated at the transported centers. The descent to the
marked pairs commutes with the projections of the common strict boundary,
intertwines the independent X evaluations, and identifies pullbacks on the
entire Picard lattices in the common coordinates.
The descent uses `Fan.exists_iso_of_matching_toric_models_of_latticeEquiv`.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup Multiplicative
open QPainleve.BlowupTower TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme.IdealSheafData LineBundleClass

namespace QPainleve.SignedClusterModularGroup.ContractedToricFiber

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "Xtor[" r "]" => Spec (CommRingCat.of (LaurentRing k₀ (Fin r)))
local notation "Dtor[" coeff "," Φ "," h "]" => Scheme.IdealSheafData.subscheme
  (Fan.toricBoundaryIdeal coeff Φ h)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "Pic[" coeff "," Φ "," r "]" =>
  Additive (LineBundleClass (Fan.finiteFanScheme coeff Φ)) × (Fin r → ℤ)
local notation "centers(" c ")" => (fun j ↦ c (ofAdd (Pi.single j 1)))
local notation "model[" b "," s "," c "]" => Fan.internalBlowupTower k₀ b s centers(c)
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "renameX(" σ ")" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (LaurentRing.rename (R := k₀) (Equiv.toFun σ))))

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ Δ : Fan i} {Ψ : Fan i'}
  [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones]
  {r n m m' : ℕ} [NeZero n] [NeZero m] [NeZero m']
  {L L' : Type} [AddCommGroup L] [AddCommGroup L']
  {B : LinearMap.BilinForm ℤ L} {B' : LinearMap.BilinForm ℤ L'}
  {M : MarkedSurface k₀ n B (QPainleve.CharacterTorus.scheme k₀ (Fin r →₀ ℤ))}
    {M' : MarkedSurface k₀ n B' (QPainleve.CharacterTorus.scheme k₀ (Fin r →₀ ℤ))}
  {b : Module.Basis (Fin 2) ℤ N} {b' : Module.Basis (Fin 2) ℤ N'}
  {s : Fin r → Φ.Ray} {s' : Fin r → Ψ.Ray} {hΦ : Φ.IsRegular} {hΨ : Ψ.IsRegular}
  [PrestableFamily (Dtor[k₀,Φ,hΦ₀] ↘ Spec (.of k₀))] [PrestableFamily (Dtor[k₀,Ψ,hΨ₀] ↘ Spec
    (.of k₀))]
  {α α' : Type*} {a : α → (Dtor[k₀,Φ,hΦ₀] ↘ Spec (.of k₀)).smoothLocus}
  {a' : α' → (Dtor[k₀,Ψ,hΨ₀] ↘ Spec (.of k₀)).smoothLocus}
  {T : Scheme.NodalCycleNumbering a m} {T' : Scheme.NodalCycleNumbering a' m'}
  {o : ZMod m} {o' : ZMod m'} {J : L →ₗ[ℤ] Pic[k₀,Φ,r]} {J' : L' →ₗ[ℤ] Pic[k₀,Ψ,r]}
  {c d : Multiplicative (Fin r → ℤ) →* k₀ˣ}
  (p : ContractedToricFiber b s hΦ T o J c M)
  (q : ContractedToricFiber b' s' hΨ T' o' J' d M')

variable (e : N ≃ₗ[ℤ] N') (hΔΦ : Δ.IsSubdivision Φ)
  (hΔΩ : Δ.IsSubdivision (Ψ.mapEquiv Φ.lattice e.symm))

local notation "g" => Fan.mapEquivIso Ψ (Fan.lattice Φ) (LinearEquiv.symm e)
local notation "hΩ₀" => Nonempty.map (FanEquiv.coneEquiv g) hΨ₀
local notation "hΔ₀" => Fan.IsSubdivision.nonempty_cones_of_nonempty hΔΦ hΦ₀
local notation "leftBoundary" => Fan.IsSubdivision.boundaryMap k₀ hΔΦ hΔ₀ hΦ₀
local notation "rightBoundary" =>
  Fan.IsSubdivision.boundaryMap k₀ hΔΩ hΔ₀ hΩ₀ ≫ Iso.inv (FanEquiv.boundaryIso k₀ g hΨ₀ hΩ₀)

/-- A comparison of two marked endpoints on a specified common toric subdivision.
The pair isomorphism realizes the coordinate relabeling. Its Picard pullback is
read in the common toric marking and its boundary rotation is read from the
image of component zero. -/
structure MarkedToricEndpointComparison (σ : Equiv.Perm (Fin r)) where
  /-- The Picard pullback from the target marking to the source marking. -/
  picard : B'.IsometryEquiv B
  /-- The forward rotation of the numbered boundary, including its ordered branches. -/
  rotation : ZMod n
  /-- The fixed-center realization inducing the stated Picard pullback and rotation. -/
  fiber : FiberRealization M M' (renameX(σ.symm)).toRationalMap picard (DihedralGroup.r rotation)
  /-- The endpoint isomorphism intertwines the two maps from the subdivided boundary. -/
  boundary_comp : (leftBoundary ≫ p.boundaryMap) ≫ (MarkedSurface.boundaryIso fiber.iso).hom =
    rightBoundary ≫ q.boundaryMap
  /-- Pullback matches the toric and ordered exceptional coordinates on the subdivision. -/
  picard_apply_eq_iff (x : L) (y : L') : picard y = x ↔
    (Additive.ofMul (pullback (hΔΦ.toFanHom.finiteFanSchemeHom k₀) (J x).1.toMul), (J x).2) =
    (Additive.ofMul (pullback
      ((hΔΩ.toFanHom.finiteFanSchemeHom k₀) ≫ ((g).symm.toFanHom.finiteFanSchemeHom k₀))
        (J' y).1.toMul),
      (J' y).2 ∘ σ)
  /-- A point over the initial surviving component maps to its forward boundary label. -/
  componentGenericPoint_eq :
    letI : PrestableFamily (M.boundary ↘ S) := M.prestable
    letI : PrestableFamily (M'.boundary ↘ S) := M'.prestable
    ∀ x : Dtor[k₀,Δ,hΔ₀], leftBoundary x = T.componentGenericPoint o →
      (rightBoundary ≫ q.boundaryMap) x = M'.cycle.componentGenericPoint rotation

variable {p q e hΔΦ hΔΩ} in
/-- For fixed subdivision and relabeling, the endpoint pair isomorphism determines the
comparison. -/
@[ext]
theorem MarkedToricEndpointComparison.ext {σ : Equiv.Perm (Fin r)}
    {C C' : MarkedToricEndpointComparison p q e hΔΦ hΔΩ σ}
    (h : C.fiber.iso = C'.fiber.iso) : C = C' := by
  have hp : C.picard = C'.picard := by
    apply DFunLike.ext
    intro y
    apply M.picardMarking.injective
    rw [C.fiber.picard_eq, C'.fiber.picard_eq, h]
  have hr : C.rotation = C'.rotation := by
    apply DihedralGroup.r.inj
    rw [← C.fiber.boundaryAction_eq, ← C'.fiber.boundaryAction_eq, h]
  cases C
  cases C'
  dsimp only at h hp hr
  cases hp
  cases hr
  cases FiberRealization.ext h
  rfl

private theorem exists_endpoint_rotation (hΔ : Δ.IsRegular)
    [PrestableFamily (Dtor[k₀,Δ,hΔ₀] ↘ S)] {k : ℕ} [NeZero k] {β : Type*}
    {w : β → (Dtor[k₀,Δ,hΔ₀] ↘ S).smoothLocus} (U : Scheme.NodalCycleNumbering w k)
    (hleft : (leftBoundary).IsOrientedCycleSubdivision U T)
    (hright : (rightBoundary).IsOrientedCycleSubdivision U T')
    (f : M.pair ≅ M'.pair)
    (hcomm : (leftBoundary ≫ p.boundaryMap) ≫ (MarkedSurface.boundaryIso f).hom =
      rightBoundary ≫ q.boundaryMap) :
    letI : PrestableFamily (M.boundary ↘ S) := M.prestable
    letI : PrestableFamily (M'.boundary ↘ S) := M'.prestable
    ∃ j : ZMod n,
      (MarkedSurface.boundaryIso f).boundaryCycleAction M.cycle M'.cycle = DihedralGroup.r j ∧
      ∀ x : Dtor[k₀,Δ,hΔ₀], leftBoundary x = T.componentGenericPoint o →
        (rightBoundary ≫ q.boundaryMap) x = M'.cycle.componentGenericPoint j := by
  let : PrestableFamily (M.boundary ↘ S) := M.prestable
  let : PrestableFamily (M'.boundary ↘ S) := M'.prestable
  let : Nonempty Δ.cones := hΔ₀
  let E := MarkedSurface.boundaryIso f
  let j := cycleVertexPerm (E.boundaryCycleAction M.cycle M'.cycle) 0
  have hpoint (x : Dtor[k₀,Δ,hΔ₀]) (hx : leftBoundary x = T.componentGenericPoint o) :
      (rightBoundary ≫ q.boundaryMap) x = M'.cycle.componentGenericPoint j := by
    have h := congrArg (fun f : Dtor[k₀,Δ,hΔ₀] ⟶ M'.boundary ↦ f x) hcomm
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx, p.component_zero] at h
    exact h.symm.trans (E.apply_componentGenericPoint M.cycle M'.cycle 0)
  obtain ⟨l, hl⟩ := hΔΦ.exists_componentGenericPoint_lift k₀ T hΦ hΔ U o
  have hzero : (leftBoundary ≫ p.boundaryMap) (U.componentGenericPoint l) =
      M.cycle.componentGenericPoint 0 := by
    rw [Scheme.Hom.comp_apply, hl, p.component_zero]
  exact ⟨j, (E.boundaryCycleAction_eq_r_iff_of_common_subdivision M.cycle M'.cycle U
    (hleft.comp p.orientedSubdivision) (hright.comp q.orientedSubdivision) hcomm hzero j).mpr
    (hpoint _ hl), hpoint⟩

include p q in
/-- Matching endpoint charges and centers identify the marked pairs. The same
isomorphism identifies the two maps from the boundary of the common subdivision,
relabels the independent X evaluation, and computes the full marked Picard
pullback on the common subdivision. Its rotation on the ordered branches is
read from the image of the initial surviving component. Inversions of the
label order are allowed only between distinct centers. -/
theorem nonempty_markedToricEndpointComparison
    (hΔ : Δ.IsRegular) (σ : Equiv.Perm (Fin r)) (hc : centers(d) ∘ σ = centers(c))
    (hss' : ∀ j, e (s j).primitiveGenerator = (s' (σ j)).primitiveGenerator)
    (hdet : ∀ x y, b'.detDualEquiv (e x) (e y) = b.detDualEquiv x y)
    (horder : ∀ j l, j < l → σ l < σ j →
      (s' (σ j), centers(d) (σ j)) ≠ (s' (σ l), centers(d) (σ l)))
    {l l' : ℕ} {Y Y' : Scheme}
    {A : BlowupTower M.surface l Y} {A' : BlowupTower M'.surface l' Y'}
    (hA : IsNodalBoundaryTower D[M] (M.surface ↘ S) (𝟙 _) A)
    (hA' : IsNodalBoundaryTower D[M'] (M'.surface ↘ S) (𝟙 _) A')
    (u : Y ≅ (model[b,s,c]).1) (u' : Y' ≅ (model[b',s',d]).1)
    (hu : u.inv ≫ A.toBase = p.projection) (hu' : u'.inv ≫ A'.toBase = q.projection)
    (hD : D[M].IsEffectiveCartier) (hE : D[M'].IsEffectiveCartier)
    (hnefD : IsNef k₀ (M.surface ↘ S) classOf(hD))
    (hnefE : IsNef k₀ (M'.surface ↘ S) classOf(hE))
    (hsqD : Chow.classIntersectionNumber k₀ M.surface classOf(hD) classOf(hD) = 0)
    (hsqE : Chow.classIntersectionNumber k₀ M'.surface classOf(hE) classOf(hE) = 0)
    [PrestableFamily (Dtor[k₀,Δ,hΔ₀] ↘ S)] {k : ℕ} [NeZero k] {β : Type*}
    {w : β → (Dtor[k₀,Δ,hΔ₀] ↘ S).smoothLocus} (U : Scheme.NodalCycleNumbering w k)
    (hleft : (leftBoundary).IsOrientedCycleSubdivision U T)
    (hright : (rightBoundary).IsOrientedCycleSubdivision U T') :
    Nonempty (MarkedToricEndpointComparison p q e hΔΦ hΔΩ σ) := by
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : SmoothOfRelativeDimension 2 (M'.surface ↘ S) := M'.smooth
  let : M.surface.IsProjectiveOver k₀ := M.projective
  let : M'.surface.IsProjectiveOver k₀ := M'.projective
  let : PrestableFamily (D[M].subscheme ↘ S) := M.prestable_boundaryImage
  let : ConnectedSpace D[M].subscheme :=
    GeometricallyConnected.connectedSpace_of_subsingleton (D[M].subscheme ↘ S)
  have hconn : _root_.IsConnected (D[M].support : Set M.surface) := by
    simpa only [range_subschemeι] using isConnected_range D[M].subschemeι.continuous
  have hp : u.hom ≫ p.projection = A.toBase := by rw [← hu, Iso.hom_inv_id_assoc]
  have hq : u'.hom ≫ q.projection = A'.toBase := by rw [← hu', Iso.hom_inv_id_assoc]
  obtain ⟨f, hf, hideal, hboundary, heval, hpic⟩ :=
    Fan.exists_iso_of_matching_toric_models_of_latticeEquiv k₀
      b b' hΦ hΨ s s' c d σ hc e hss' hdet hΔΦ hΔΩ hΔ hA hA' u u'
      (by rw [← p.projection_over, ← Category.assoc, hp])
      (by rw [← q.projection_over, ← Category.assoc, hq])
      (by rw [← hp, comap_comp, Scheme.IdealSheafData.support_comap,
        Scheme.IdealSheafData.support_comap, p.support_comap])
      (by rw [← hq, comap_comp, Scheme.IdealSheafData.support_comap,
        Scheme.IdealSheafData.support_comap, q.support_comap])
      hD hE M.boundaryIdeal_nodal M'.boundaryIdeal_nodal hconn hnefD hnefE hsqD hsqE
  obtain ⟨f', hf'⟩ := M.exists_pairIso_of_boundaryIdeal M' f hf hideal
  have he : f = MarkedSurface.surfaceIso f' := Iso.ext hf'.symm
  subst f
  have : IsClosedImmersion M'.pair.hom.left := M'.closedImmersion
  have hcomm : (leftBoundary ≫ p.boundaryMap) ≫ (MarkedSurface.boundaryIso f').hom =
      rightBoundary ≫ q.boundaryMap := by
    rw [← cancel_mono M'.pair.hom.left]
    simpa only [← hu, ← hu', Category.assoc, MarkedSurface.boundaryIso_hom_comp,
      reassoc_of% p.boundary_comp, q.boundary_comp] using hboundary
  obtain ⟨j, hrotation, hpoint⟩ := exists_endpoint_rotation p q e hΔΦ hΔΩ hΔ U hleft hright f' hcomm
  let I := M'.marking.trans
    ((Chow.picardPullbackIsometry k₀ (MarkedSurface.surfaceIso f')).trans M.marking.symm)
  have hI (y : L') : M.picardMarking (I y) =
      Additive.ofMul (pullback (MarkedSurface.surfaceIso f').hom (M'.picardMarking y).toMul) := by
    simp only [MarkedSurface.picardMarking_apply, I, LinearMap.BilinForm.IsometryEquiv.trans_apply,
      LinearMap.BilinForm.IsometryEquiv.apply_symm_apply, Chow.picardPullbackIsometry_apply]
  refine ⟨{ picard := I
            rotation := j
            fiber := ⟨f', hI, hrotation, ?_⟩
            boundary_comp := hcomm
            picard_apply_eq_iff := fun x y ↦ ?_
            componentGenericPoint_eq := hpoint }⟩
  · obtain ⟨h, hX⟩ := M.evaluation.compOfDefined_toRationalMap (renameX(σ.symm))
    refine ⟨h, hX.trans ?_⟩
    rw [p.evaluation_eq, q.evaluation_eq]
    simpa only [hu, hu'] using heval.symm
  · rw [← M.picardMarking.injective.eq_iff, hI, ← Additive.toMul.injective.eq_iff, toMul_ofMul]
    simpa only [hu, hu', p.marked_pullback, q.marked_pullback] using
      hpic horder (M.picardMarking x).toMul (M'.picardMarking y).toMul

end QPainleve.SignedClusterModularGroup.ContractedToricFiber

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.CommonRefinement
public import QPainleve.Geometry.Toric.Fan.Equiv
public import QPainleve.SignedClusterModularGroup.Realization.Iteration

import QPainleve.SignedClusterModularGroup.Realization.Endpoint.EqualExchangeMatrix

/-!
# Common refinements for signed cluster loop endpoints

The exchange matrix of a loop returns to its initial value. For a presentation
of a primitive nef square-zero anticanonical cycle, this identifies the terminal
charge lattice with the initial one in their respective frames. A single
oriented common toric subdivision can then be used at every reached center.

The construction combines
`ContractedToricFiber.existsUnique_rayChargeEquiv_of_equal_exchange_matrix`
with `FanEquiv.exists_oriented_common_boundary_subdivision`.
-/

public section

open AlgebraicGeometry CategoryTheory Module Quiver
open QPainleve.CharacterTorus QPainleve.Cluster TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup

open GeometricRealization (Point CenterPoint)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "Dtor[" Φ "," h "]" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L} {γ : Type}

namespace GeometricRealization

local notation "frameSwap" => (Equiv.swap 0 1 : Equiv.Perm (Fin 2))
local notation "Cw[" w "," P "]" => Quiver.Path.centerPartialMap ℂ w P
local notation "Cnil[" P "]" => Quiver.Path.centerPartialMap ℂ Quiver.Path.nil P
local notation "src(" C "," c ")" =>
  c ≫ Scheme.PartialMap.domainSource (X := Centers[r]) (Y := Centers[r]) C
local notation "dst(" C "," c ")" =>
  c ≫ Scheme.PartialMap.domainTarget (X := Centers[r]) (Y := Centers[r]) C

/-- Both ends of a loop's center map lie in the initial noncollision open
when the exchange kernel is the charge kernel. -/
theorem _root_.Quiver.Path.centerPoint_endpoints_mem_noncollision
    {E : SkewExchangeMatrix (Fin r)} (w : Word E E) (P : ChargeSeed E N)
    (hker : E.matrix.mulVecLin.ker = P.charge.ker)
    (x : CenterPoint (U := Centers[r]) (V := Centers[r]) Cw[w,P]) :
    (src(Cw[w,P],x)).left (default : S) ∈ Path.centerOpen ℂ Path.nil P ∧
      (dst(Cw[w,P],x)).left (default : S) ∈ Path.centerOpen ℂ Path.nil P := by
  constructor
  · rw [Over.comp_left, PartialMap.domainSource_left, Scheme.Hom.comp_apply]
    apply w.centerOpen_le_centerOpen_nil ℂ P
    rw [← w.centerPartialMap_domain (K := ℂ) P]
    exact (x.left (default : S)).property
  · rw [Over.comp_left, PartialMap.domainTarget_left, Scheme.Hom.comp_apply]
    apply w.centerPartialMap_opensRange_le_centerOpen_nil P hker
    exact (Cw[w,P]).hom.mem_opensRange.mpr (Set.mem_range_self _)

private theorem hasNodalModel_at_loop_target
    {B : SkewExchangeMatrix (Fin r)} (w : Word B B) (P : ChargeSeed B N)
    (Q : CompleteToricPresentation i b r L γ)
    (M : Point Centers[r] → MarkedSurface ℂ n H XTor[r])
    (models : ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P],
      Q.HasNodalModel (dst(Cnil[P],c)) (M (dst(Cnil[P],c))))
    (e : N ≃ₗ[ℤ] N)
    (he : ∀ j, e ((w.chargeTarget P).charge (Pi.single j 1)) = P.charge (Pi.single j 1))
    (c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cw[w,P]) :
    Q.HasNodalModel (dst(Cw[w,P],c)) (M (dst(Cw[w,P],c))) := by
  have he' : e ∘ (fun j ↦ (w.chargeTarget P).charge (Pi.single j 1)) =
      fun j ↦ P.charge (Pi.single j 1) := funext he
  have hU := w.centerOpen_le_preimage_distinctCentersOpen ℂ P
  rw [← distinctCentersOpen_comp_of_injective ℂ _ e.injective, he',
    ← Path.centerOpen_nil] at hU
  have hr : Set.range (Cw[w,P]).hom ⊆ Set.range (Cnil[P]).hom := by
    rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
      Path.centerPartialMap_opensRange, Path.centerPartialMap_opensRange,
      Path.centerIso_nil, Iso.refl_inv, Scheme.Hom.id_preimage, Scheme.Hom.inv_preimage]
    exact ((w.centerIso ℂ).hom.image_mono hU).trans ((w.centerIso ℂ).hom.image_preimage_le _)
  -- A reached center factors through the empty word's center domain.
  let f := IsOpenImmersion.lift (Cnil[P]).hom (Cw[w,P]).hom hr
  have hf : f ≫ (Cnil[P]).hom = (Cw[w,P]).hom := IsOpenImmersion.lift_fac _ _ _
  let g : (Cw[w,P]).domainOver (X := Centers[r]) (Y := Centers[r]) ⟶
      (Cnil[P]).domainOver (X := Centers[r]) (Y := Centers[r]) :=
    Over.homMk f (by
      rw [← Over.w ((Cnil[P]).domainTarget (X := Centers[r]) (Y := Centers[r])),
        Scheme.PartialMap.domainTarget_left, ← Category.assoc, hf]
      simpa only [Scheme.PartialMap.domainTarget_left] using
        (Over.w ((Cw[w,P]).domainTarget (X := Centers[r]) (Y := Centers[r]))))
  have hg : g ≫ (Cnil[P]).domainTarget (X := Centers[r]) (Y := Centers[r]) =
      (Cw[w,P]).domainTarget (X := Centers[r]) (Y := Centers[r]) := by
    apply Over.OverMorphism.ext
    simpa only [g, Over.comp_left, Over.homMk_left, Scheme.PartialMap.domainTarget_left] using hf
  simpa only [Category.assoc, hg] using models (c ≫ g)

/-- Realize a signed loop over its entire noncollision open and identify its
terminal charge rays with the original ones by the unique oriented lattice equivalence.
Both presentations have nodal models at every reached center. A single common
toric subdivision preserves the boundary orders in the transported and original
frames through its respective projections. -/
theorem exists_realize_signed_loop_with_oriented_refinement
    {B : SkewExchangeMatrix (Fin r)} (w : Word B B) (P : ChargeSeed B N)
    (Q : CompleteToricPresentation i b r L γ)
    (hform : P.form = b.detDualEquiv.toLinearMap)
    (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (M : Point Centers[r] → MarkedSurface ℂ n H XTor[r])
    (models : ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P],
      Q.HasNodalModel (dst(Cnil[P],c)) (M (dst(Cnil[P],c))))
    {c₀ : Point Centers[r]} (hmodel : Q.HasNodalModel c₀ (M c₀))
    [IsRationalOver ((M c₀).surface ↘ S)]
    (hD : D[M c₀].IsEffectiveCartier) (hnef : (classOf(hD)).IsNef ℂ ((M c₀).surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ (M c₀).surface classOf(hD) classOf(hD) = 0)
    (hcan : letI : SmoothOfRelativeDimension 2 ((M c₀).surface ↘ S) := (M c₀).smooth
      classOf(hD) = (LineBundleClass.mk (canonicalBundle ℂ (M c₀).surface 2))⁻¹)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD))) :
    let b' := b.reindex (frameSwap ^ w.inversionCount)
    ∃ (γ' : Type) (Q' : CompleteToricPresentation i b' r L γ')
      (M' : Point Centers[r] → MarkedSurface ℂ n H XTor[r])
      (R : GeometricRealization (T₀ := Centers[r]) (T₁ := Centers[r])
        M M' Cw[w,P] (w.xRationalMap ℂ)),
      R.picard = .refl H ∧ R.boundaryAction = DihedralGroup.sr 0 ^ w.inversionCount ∧
      (∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cw[w,P],
        Q'.HasNodalModel (dst(Cw[w,P],c)) (M' (dst(Cw[w,P],c))) ∧
        Q.HasNodalModel (dst(Cw[w,P],c)) (M (dst(Cw[w,P],c)))) ∧
      ∃ e : N ≃ₗ[ℤ] N,
        (∀ j, e (Q'.rays j).primitiveGenerator = (Q.rays j).primitiveGenerator) ∧
        (∀ x y, b.detDualEquiv (e x) (e y) = b'.detDualEquiv x y) ∧
        (∀ e' : N ≃ₗ[ℤ] N,
          (∀ j, e' (Q'.rays j).primitiveGenerator = (Q.rays j).primitiveGenerator) →
          (∀ x y, b.detDualEquiv (e' x) (e' y) = b'.detDualEquiv x y) → e' = e) ∧
        let g := Q.fan.mapEquivIso Q'.fan.lattice e.symm
        let hQ' := Q'.complete.nonempty_cones
        let hQ := Q.complete.nonempty_cones
        let hΩ := Nonempty.map g.coneEquiv hQ
        letI := Q'.prestable
        letI := Q.prestable
        letI := Q'.neZero
        letI := Q.neZero
        ∃ (Δ : Fan i) (hΔQ' : Δ.IsSubdivision Q'.fan)
          (hΔΩ : Δ.IsSubdivision (Q.fan.mapEquiv Q'.fan.lattice e.symm)),
          let hΔ₀ := hΔQ'.nonempty_cones_of_nonempty hQ'
          ∃ (_ : Δ.IsRegular) (hpre : PrestableFamily (Dtor[Δ,hΔ₀] ↘ S))
            (l : ℕ) (_ : NeZero l),
            letI := hpre
            ∃ U : NodalCycleNumbering (Empty.elim : Empty → (Dtor[Δ,hΔ₀] ↘ S).smoothLocus) l,
              (hΔQ'.boundaryMap hΔ₀ hQ').IsOrientedCycleSubdivision U Q'.cycle ∧
              (hΔΩ.boundaryMap hΔ₀ hΩ ≫ (g.boundaryIso hQ hΩ).inv).IsOrientedCycleSubdivision
                U Q.cycle := by
  obtain ⟨γ', Q', M', R, hf', hc', hpic, hact, hmodels⟩ :=
    exists_realize_signed_word w P Q hform hcharge M models
  have hmat := P.matrix_eq.trans (w.chargeTarget P).matrix_eq.symm
  rw [hform, hcharge, hf', hc'] at hmat
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  let := Q'.complete.nonempty_cones
  let := Q'.prestable
  let := Q'.neZero
  obtain ⟨p, _, _, _, u, hu, hp⟩ := (Q.hasNodalModel_iff c₀ (M c₀)).mp hmodel
  obtain ⟨f, ⟨hf, hdet⟩, huniq⟩ := p.existsUnique_rayChargeEquiv_of_equal_exchange_matrix
    Q.complete hu u hp.symm hD hnef hsq hcan hprim hmat
  have hf' (j : Fin r) : f.symm (Q'.rays j).primitiveGenerator = (Q.rays j).primitiveGenerator :=
    f.symm_apply_eq.mpr (hf j).symm
  have hdet' (x y : N) : b.detDualEquiv (f.symm x) (f.symm y) =
      (b.reindex (frameSwap ^ w.inversionCount)).detDualEquiv x y := by
    simpa only [LinearEquiv.apply_symm_apply] using (hdet (f.symm x) (f.symm y)).symm
  have he (j : Fin r) : f.symm ((w.chargeTarget P).charge (Pi.single j 1)) =
      P.charge (Pi.single j 1) := by
    simpa only [hc', hcharge, Fan.rayChargeMap_single] using hf' j
  refine ⟨γ', Q', M', R, hpic, hact, fun c ↦
    ⟨hmodels c, hasNodalModel_at_loop_target w P Q M models f.symm he c⟩,
    f.symm, hf', hdet', ?_, ?_⟩
  · intro e hcharge' hdet''
    have hu := huniq e.symm
      ⟨fun j ↦ e.symm_apply_eq.mpr (hcharge' j).symm, fun x y ↦ by
        simpa only [LinearEquiv.apply_symm_apply] using (hdet'' (e.symm x) (e.symm y)).symm⟩
    simpa only [LinearEquiv.symm_symm] using congrArg LinearEquiv.symm hu
  · let g := Q.fan.mapEquivIso Q'.fan.lattice f
    have hg (x y : N) : (b.reindex (frameSwap ^ w.inversionCount)).detDualEquiv
        (g.latticeEquiv x) (g.latticeEquiv y) = b.detDualEquiv x y := by
      simpa only [g, Fan.mapEquivIso_latticeEquiv, LinearEquiv.coe_addEquiv_apply] using hdet x y
    simpa only [LinearEquiv.symm_symm] using
      g.exists_oriented_common_boundary_subdivision Q'.cycle Q.cycle Q'.regular Q.regular
        Q'.complete Q.complete Q'.component_eq Q.component_eq _ b hg Q'.positive Q.positive

end GeometricRealization

end QPainleve.SignedClusterModularGroup

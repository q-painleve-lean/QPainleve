/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.CommonRefinement
public import QPainleve.Geometry.Toric.Fan.Equiv
public import QPainleve.SignedClusterModularGroup.Realization.Iteration

import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.Endpoint.EqualExchangeMatrix
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber

/-!
# Common refinements for signed cluster word endpoints

The exchange matrix at the end of a word identifies the transported charges with
the charges of a specified target presentation of a primitive nef square-zero
anticanonical cycle. A single oriented common toric subdivision compares the
two presentations at every reached center.

The construction combines
`ContractedToricFiber.existsUnique_rayChargeEquiv_of_equal_exchange_matrix`
with `FanEquiv.exists_oriented_common_boundary_subdivision`.
-/

public section

open AlgebraicGeometry CategoryTheory Module Quiver
open QPainleve.CharacterTorus QPainleve.Cluster TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

open GeometricRealization (Point CenterPoint)

local notation "S" => Spec (CommRingCat.of k₀)
local notation "Centers[" r "]" => Over.mk (structureMap k₀ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme k₀ (Fin r →₀ ℤ)
local notation "Dtor[" Φ "," h "]" => Scheme.IdealSheafData.subscheme
  (Fan.toricBoundaryIdeal k₀ Φ h)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L} {γ : Type}

namespace GeometricRealization

local notation "frameSwap" => (Equiv.swap 0 1 : Equiv.Perm (Fin 2))
local notation "Cw[" w "," P "]" => Quiver.Path.centerPartialMap k₀ w P
local notation "Cnil[" P "]" => Quiver.Path.centerPartialMap k₀ Quiver.Path.nil P
local notation "dst(" C "," c ")" =>
  c ≫ Scheme.PartialMap.domainTarget (X := Centers[r]) (Y := Centers[r]) C

variable {N₁ V₁ : Type} [AddCommGroup N₁] [AddCommGroup V₁] [Module ℝ V₁]
  {i₁ : N₁ →+ V₁} {b₁ : Basis (Fin 2) ℤ N₁} {L₁ γ₁ : Type} [AddCommGroup L₁]
  {H₁ : LinearMap.BilinForm ℤ L₁} {B E : SkewExchangeMatrix (Fin r)}

private theorem hasNodalModel_at_word_target
    (w : Word B E) (P : ChargeSeed B N) (P₁ : ChargeSeed E N₁)
    (Q : CompleteToricPresentation k₀ i₁ b₁ r L₁ γ₁)
    (M : Point Centers[r] → MarkedSurface k₀ n H₁ XTor[r])
    (models : ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P₁],
      Q.HasNodalModel (dst(Cnil[P₁],c)) (M (dst(Cnil[P₁],c))))
    (e : N ≃ₗ[ℤ] N₁)
    (he : ∀ j, e ((w.chargeTarget P).charge (Pi.single j 1)) = P₁.charge (Pi.single j 1))
    (c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cw[w,P]) :
    Q.HasNodalModel (dst(Cw[w,P],c)) (M (dst(Cw[w,P],c))) := by
  have he' : e ∘ (fun j ↦ (w.chargeTarget P).charge (Pi.single j 1)) =
      fun j ↦ P₁.charge (Pi.single j 1) := funext he
  have hU := w.centerPartialMap_opensRange_le_distinctCentersOpen (K := k₀) P
  rw [← distinctCentersOpen_comp_of_injective k₀ _ e.injective, he',
    ← Path.centerOpen_nil] at hU
  have hr : Set.range (Cw[w,P]).hom ⊆ Set.range (Cnil[P₁]).hom := by
    rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
      Path.centerPartialMap_opensRange (Path.nil : Word E E) P₁,
      Path.centerIso_nil, Iso.refl_inv, Scheme.Hom.id_preimage]
    exact hU
  -- A reached center factors through the empty word's center domain.
  let f := IsOpenImmersion.lift (Cnil[P₁]).hom (Cw[w,P]).hom hr
  have hf : f ≫ (Cnil[P₁]).hom = (Cw[w,P]).hom := IsOpenImmersion.lift_fac _ _ _
  let g : (Cw[w,P]).domainOver (X := Centers[r]) (Y := Centers[r]) ⟶
      (Cnil[P₁]).domainOver (X := Centers[r]) (Y := Centers[r]) :=
    Over.homMk f (by
      rw [← Over.w ((Cnil[P₁]).domainTarget (X := Centers[r]) (Y := Centers[r])),
        Scheme.PartialMap.domainTarget_left, ← Category.assoc, hf]
      simpa only [Scheme.PartialMap.domainTarget_left] using
        (Over.w ((Cw[w,P]).domainTarget (X := Centers[r]) (Y := Centers[r]))))
  have hg : g ≫ (Cnil[P₁]).domainTarget (X := Centers[r]) (Y := Centers[r]) =
      (Cw[w,P]).domainTarget (X := Centers[r]) (Y := Centers[r]) := by
    apply Over.OverMorphism.ext
    simpa only [g, Over.comp_left, Over.homMk_left, Scheme.PartialMap.domainTarget_left] using hf
  simpa only [Category.assoc, hg] using models (c ≫ g)

/-- Realize a signed word on its whole noncollision open with the transported
marking and identify its final charges with those of a specified target presentation.
Both presentations have nodal models at every reached center. Their charge equivalence
is unique and a common subdivision preserves both boundary orders. -/
theorem exists_realize_signed_word_with_oriented_refinement
    (w : Word B E) (P : ChargeSeed B N) (P₁ : ChargeSeed E N₁)
    (Q : CompleteToricPresentation k₀ i b r L γ)
    (Q₁ : CompleteToricPresentation k₀ i₁ b₁ r L₁ γ₁)
    (hform : P.form = b.detDualEquiv.toLinearMap)
    (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (hform₁ : P₁.form = b₁.detDualEquiv.toLinearMap)
    (hcharge₁ : P₁.charge = Fan.rayChargeMap Q₁.rays)
    (M : Point Centers[r] → MarkedSurface k₀ n H XTor[r])
    (M₁ : Point Centers[r] → MarkedSurface k₀ n H₁ XTor[r])
    (models : ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P],
      Q.HasNodalModel (dst(Cnil[P],c)) (M (dst(Cnil[P],c))))
    (models₁ : ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P₁],
      Q₁.HasNodalModel (dst(Cnil[P₁],c)) (M₁ (dst(Cnil[P₁],c))))
    {a₁ : Point Centers[r]} (hmodel : Q₁.HasNodalModel a₁ (M₁ a₁))
    (hD : D[M₁ a₁].IsEffectiveCartier)
    (hnef : (classOf(hD)).IsNef k₀ ((M₁ a₁).surface ↘ S))
    (hsq : Chow.classIntersectionNumber k₀ (M₁ a₁).surface classOf(hD) classOf(hD) = 0)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD))) :
    let b' := b.reindex (frameSwap ^ w.inversionCount)
    ∃ (γ' : Type) (Q' : CompleteToricPresentation k₀ i b' r L γ')
      (M' : Point Centers[r] → MarkedSurface k₀ n H XTor[r])
      (R : GeometricRealization (T₀ := Centers[r]) (T₁ := Centers[r])
        M M' Cw[w,P] (w.xRationalMap k₀)),
      R.picard = .refl H ∧ R.boundaryAction = DihedralGroup.sr 0 ^ w.inversionCount ∧
      (∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cw[w,P],
        Q'.HasNodalModel (dst(Cw[w,P],c)) (M' (dst(Cw[w,P],c))) ∧
        Q₁.HasNodalModel (dst(Cw[w,P],c)) (M₁ (dst(Cw[w,P],c)))) ∧
      ∃ e : N ≃ₗ[ℤ] N₁,
        (∀ j, e (Q'.rays j).primitiveGenerator = (Q₁.rays j).primitiveGenerator) ∧
        (∀ x y, b₁.detDualEquiv (e x) (e y) = b'.detDualEquiv x y) ∧
        (∀ e' : N ≃ₗ[ℤ] N₁,
          (∀ j, e' (Q'.rays j).primitiveGenerator = (Q₁.rays j).primitiveGenerator) →
          (∀ x y, b₁.detDualEquiv (e' x) (e' y) = b'.detDualEquiv x y) → e' = e) ∧
        let g := Q₁.fan.mapEquivIso Q'.fan.lattice e.symm
        let hQ' := Q'.complete.nonempty_cones
        let hQ := Q₁.complete.nonempty_cones
        let hΩ := Nonempty.map g.coneEquiv hQ
        letI := Q'.prestable
        letI := Q₁.prestable
        letI := Q'.neZero
        letI := Q₁.neZero
        ∃ (Δ : Fan i) (hΔQ' : Δ.IsSubdivision Q'.fan)
          (hΔΩ : Δ.IsSubdivision (Q₁.fan.mapEquiv Q'.fan.lattice e.symm)),
          let hΔ₀ := hΔQ'.nonempty_cones_of_nonempty hQ'
          ∃ (_ : Δ.IsRegular) (hpre : PrestableFamily (Dtor[Δ,hΔ₀] ↘ S))
            (l : ℕ) (_ : NeZero l),
            letI := hpre
            ∃ U : NodalCycleNumbering (Empty.elim : Empty → (Dtor[Δ,hΔ₀] ↘ S).smoothLocus) l,
              (hΔQ'.boundaryMap k₀ hΔ₀ hQ').IsOrientedCycleSubdivision U Q'.cycle ∧
              (hΔΩ.boundaryMap k₀ hΔ₀ hΩ ≫ (g.boundaryIso k₀ hQ hΩ).inv).IsOrientedCycleSubdivision
                U Q₁.cycle := by
  obtain ⟨γ', Q', M', R, hform', hc', hpic, hact, hmodels⟩ :=
    exists_realize_signed_word w P Q hform hcharge M models
  have hmat := P₁.matrix_eq.trans (w.chargeTarget P).matrix_eq.symm
  rw [hform₁, hcharge₁, hform', hc'] at hmat
  let := Q₁.complete.nonempty_cones
  let := Q₁.prestable
  let := Q₁.neZero
  let : IsRationalOver ((M₁ a₁).surface ↘ S) := hmodel.isRationalOver
  let : SmoothOfRelativeDimension 2 ((M₁ a₁).surface ↘ S) := (M₁ a₁).smooth
  have hcan := congrArg Inv.inv (hmodel.canonicalClass hD)
  obtain ⟨p, _, _, _, u, hu, hp⟩ := (Q₁.hasNodalModel_iff a₁ (M₁ a₁)).mp hmodel
  obtain ⟨f, ⟨hf, hdet⟩, huniq⟩ := p.existsUnique_rayChargeEquiv_of_equal_exchange_matrix
    Q₁.complete hu u hp.symm hD hnef hsq hcan hprim hmat
  have hf' (j : Fin r) : f.symm (Q'.rays j).primitiveGenerator = (Q₁.rays j).primitiveGenerator :=
    f.symm_apply_eq.mpr (hf j).symm
  have hdet' (x y : N) : b₁.detDualEquiv (f.symm x) (f.symm y) =
      (b.reindex (frameSwap ^ w.inversionCount)).detDualEquiv x y := by
    simpa only [LinearEquiv.apply_symm_apply] using (hdet (f.symm x) (f.symm y)).symm
  have he (j : Fin r) : f.symm ((w.chargeTarget P).charge (Pi.single j 1)) =
      P₁.charge (Pi.single j 1) := by
    simpa only [hc', hcharge₁, Fan.rayChargeMap_single] using hf' j
  refine ⟨γ', Q', M', R, hpic, hact, fun c ↦
    ⟨hmodels c, hasNodalModel_at_word_target w P P₁ Q₁ M₁ models₁ f.symm he c⟩,
    f.symm, hf', hdet', ?_, ?_⟩
  · intro e hcharge' hdet''
    have hu := huniq e.symm
      ⟨fun j ↦ e.symm_apply_eq.mpr (hcharge' j).symm, fun x y ↦ by
        simpa only [LinearEquiv.apply_symm_apply] using (hdet'' (e.symm x) (e.symm y)).symm⟩
    simpa only [LinearEquiv.symm_symm] using congrArg LinearEquiv.symm hu
  · let := Q'.complete.nonempty_cones
    let := Q'.prestable
    let := Q'.neZero
    let g := Q₁.fan.mapEquivIso Q'.fan.lattice f
    have hg (x y : N₁) : (b.reindex (frameSwap ^ w.inversionCount)).detDualEquiv
        (g.latticeEquiv x) (g.latticeEquiv y) = b₁.detDualEquiv x y := by
      simpa only [g, Fan.mapEquivIso_latticeEquiv, LinearEquiv.coe_addEquiv_apply] using hdet x y
    simpa only [LinearEquiv.symm_symm] using
      g.exists_oriented_common_boundary_subdivision k₀ Q'.cycle Q₁.cycle Q'.regular Q₁.regular
        Q'.complete Q₁.complete Q'.component_eq Q₁.component_eq _ b₁ hg Q'.positive Q₁.positive

end GeometricRealization

end QPainleve.SignedClusterModularGroup

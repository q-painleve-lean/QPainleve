/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.ModularGroup
public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.SelfRealization

import QPainleve.SignedClusterModularGroup.Realization.Endpoint.Kernel
import QPainleve.SignedClusterModularGroup.Realization.PicardAction

/-!
# The Picard action of unsigned cluster loops in a marked presentation

The signed Picard action restricts to the unsigned point-map group and takes
values in the boundary rotation group. For a marked toric presentation of a
primitive nef square-zero anticanonical cycle, the action is characterized by
the pullbacks of the realized loops and has trivial kernel.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

open Module (Basis)

local notation "S" => Spec (CommRingCat.of k₀)
local notation "Centers[" r "]" => Over.mk (structureMap k₀ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme k₀ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "Cnil[" P "]" => Path.centerPartialMap k₀ Path.nil P
local notation "U₀[" P "]" => Path.centerOpen k₀ Path.nil P
local notation "dst(" C "," c ")" =>
  c ≫ Scheme.PartialMap.domainTarget (X := Centers[_]) (Y := Centers[_]) C
local notation "χ[" c "]" => pointsEquiv k₀ _
  (Subtype.mk (Over.Hom.left c) (Over.w c))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L} {E : SkewExchangeMatrix (Fin r)}

local instance instIsDominantRotationLoopXRationalMap (w : inversionFreeLoops E) :
    ((End.asHom w.val).xRationalMap k₀).IsDominant :=
  Path.instIsDominantXRationalMap k₀ (End.asHom w.val)

local notation "LoopX[" w "]" => Path.xRationalMap k₀ (End.asHom (Subtype.val w))

variable (Q : CompleteToricPresentation k₀ i b r L γ)

local notation "Models[" M "," C "]" =>
  HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r])
    (b := b) (hΦ := Q.regular) (T := Q.cycle)
    (origin := Q.origin) (s := Q.rays) (ι := Q.inclusion) (P₁ := M)
    (fun c : Point Centers[r] ↦ χ[c]) C

/-- The Picard pullback along unsigned loop realizations of a fixed marked
presentation defines a unique faithful homomorphism from the opposite group
of independent X maps to the boundary rotations. It suffices to have nodal
models on the initial noncollision open. The reference fiber carrying the
primitive nef square-zero boundary can lie outside this open. -/
theorem existsUnique_picardHom_of_presentation
    (P : ChargeSeed E N)
    (hform : P.form = b.detDualEquiv.toLinearMap)
    (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (M : Point Centers[r] → MarkedSurface k₀ n H XTor[r])
    (models : ∀ c : Point Centers[r], c.left (default : S) ∈ U₀[P] →
      Q.HasNodalModel c (M c))
    {c₀ : Point Centers[r]} (hmodel : Q.HasNodalModel c₀ (M c₀))
    (hD : ∀ c, D[M c].IsEffectiveCartier)
    (hnef : (classOf(hD c₀)).IsNef k₀ ((M c₀).surface ↘ S))
    (hsq : Chow.classIntersectionNumber k₀ (M c₀).surface classOf(hD c₀) classOf(hD c₀) = 0)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD c₀)))
    (d : ZMod n → L) (hmark : ∀ c j, (M c).boundaryClass (hD c) j = d j) :
    letI := Q.complete.nonempty_cones
    letI := Q.prestable
    letI := Q.neZero
    ∃! f : (ClusterModularGroup k₀ E)ᵐᵒᵖ →* boundaryRotationGroup H d,
      (∀ (w : inversionFreeLoops E)
        {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
        [C.IsOver Centers[r].hom Centers[r].hom]
        (R : GeometricRealization M M C LoopX[w]),
        Models[M,C] →
        rotationInclusion H d (f (op (clusterModularGroupMap k₀ E w))) =
          R.toSignedBoundaryIsometry d hD hmark) ∧ f.ker = ⊥ := by
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  obtain ⟨ρ, ⟨hρ, hker⟩, -⟩ := existsUnique_faithful_signedPicardHom_of_presentation
    Q P hform hcharge M models hmodel hD hnef hsq hprim d hmark
  let f := picardRotationHom ρ hρ.sign_ker_unop.ge
  have hf (w : inversionFreeLoops E)
      {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
      [C.IsOver Centers[r].hom Centers[r].hom] (R : GeometricRealization M M C LoopX[w])
      (hR : Models[M,C]) :
      rotationInclusion H d (f (op (clusterModularGroupMap k₀ E w))) =
        R.toSignedBoundaryIsometry d hD hmark := by
    have hw : End.of (End.asHom w.val) = w.val := End.ext rfl
    simp only [f, rotationInclusion_picardRotationHom_apply, MonoidHom.op_apply_apply,
      Function.comp_apply, unop_op, clusterModularGroupInclusion_clusterModularGroupMap]
    have h := hρ.apply_of_realization (End.asHom w.val) R hR
    rw [hw] at h
    exact h
  refine ⟨f, ⟨hf, f.ker_eq_bot_iff.mpr ?_⟩, ?_⟩
  · exact picardRotationHom_injective ρ hρ.sign_ker_unop.ge (ρ.ker_eq_bot_iff.mp hker)
  · intro f' hf'
    have hmodels (x : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P]) :
        Q.HasNodalModel (dst(Cnil[P],x)) (M (dst(Cnil[P],x))) := by
      apply models
      rw [Over.comp_left, Scheme.PartialMap.domainTarget_left, Path.centerPartialMap_hom,
        Path.centerIso_nil, Iso.refl_hom, Category.comp_id, Scheme.Hom.comp_apply,
        ← Path.centerPartialMap_domain]
      exact (x.left (default : S)).property
    refine MonoidHom.ext fun g ↦ ?_
    obtain ⟨w, hw⟩ := clusterModularGroupMap_surjective k₀ E g.unop
    rw [← op_unop g, ← hw]
    obtain ⟨R, -, -, hR⟩ := exists_realize_signed_loop (End.asHom w.val) P Q
      hform hcharge M hmodels hmodel hD hnef hsq hprim d hmark
    let C := Path.centerPartialMap k₀ (End.asHom w.val) P
    let : C.IsOver Centers[r].hom Centers[r].hom :=
      Path.instIsOverCenterPartialMapHomSchemeMkStructureMapForallInt (K := k₀) (End.asHom w.val) P
    let : IsDominant C.hom :=
      Path.instIsDominantHomCenterPartialMap (K := k₀) (End.asHom w.val) P
    have htargets : Models[M,C] := fun x ↦ by
      have hx : Q.HasNodalModel (dst(C,x)) (M (dst(C,x))) := hR x
      exact hx.nonempty_contractedToricFiber
    exact rotationInclusion_injective H d
      ((hf'.1 w (C := C) R htargets).trans (hf w (C := C) R htargets).symm)

end QPainleve.SignedClusterModularGroup.GeometricRealization

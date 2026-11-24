/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Center
public import QPainleve.Algebra.Cluster.Word.ModularGroup
public import QPainleve.Algebra.Cluster.Word.Monomial

import TauCeti.Algebra.Module.Equiv.AutCongr

/-!
# Casimir action of the signed cluster modular group

Pullback preserves the monomials with exponents in the exchange kernel. Their linear
independence makes the integral exponent substitution an action of the opposite point-map
group. When the charges span rationally and their alternating pairing separates on the
right, the exchange kernel identifies with the charge kernel.

The monomial action uses the cluster X mutations of Fock and Goncharov,
*Cluster ensembles, quantization and the dilogarithm*, §1.2.4, and the signed generators of
Bershtein, Gavrylenko and Marshakov, *Cluster integrable systems, q-Painlevé equations and
their quantization*, §3.1.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
open QPainleve.CharacterTorus

namespace QPainleve.Cluster

universe u

section Action

variable (k : Type*) [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (B : SkewExchangeMatrix ι)

local notation "E" => B.matrix.mulVecLin.ker
local notation "Γ" => SignedClusterModularGroup k B
local notation "χ" => fun x : ι → ℤ ↦
  monomial k (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm x))
local notation "evalLoop" => signedClusterModularGroupMap k B
local notation "Loops" => End (Prefunctor.obj (Paths.of (SkewExchangeMatrix ι)) B)

private def exchangeKernelEquivOfPullback (f : signedLoopPullbacks k B) : E ≃ₗ[ℤ] E :=
  ((mem_signedLoopPullbacks_iff k B f.val).mp f.property).choose.exchangeKernelEquiv

private theorem exchangeKernelEquivOfPullback_eq (f : signedLoopPullbacks k B) (w : Word B B)
    (hw : w.xPullback k = f.val) :
    exchangeKernelEquivOfPullback k B f = w.exchangeKernelEquiv :=
  Path.exchangeKernelEquiv_eq_of_xPullback_eq k
    (((mem_signedLoopPullbacks_iff k B f.val).mp f.property).choose_spec.trans hw.symm)

/-- The action of signed cluster pullbacks on the exchange kernel of the base seed. -/
def exchangeKernelAction : Γᵐᵒᵖ →* (E ≃ₗ[ℤ] E) :=
  let f : signedLoopPullbacks k B →* (E ≃ₗ[ℤ] E) :=
    { toFun := exchangeKernelEquivOfPullback k B
      map_one' := by
        rw [exchangeKernelEquivOfPullback_eq k B 1 Path.nil (Path.xPullback_nil k),
          Path.exchangeKernelEquiv_nil]
        rfl
      map_mul' := by
        intro f g
        obtain ⟨w, hw⟩ := (mem_signedLoopPullbacks_iff k B f.val).mp f.property
        obtain ⟨v, hv⟩ := (mem_signedLoopPullbacks_iff k B g.val).mp g.property
        rw [exchangeKernelEquivOfPullback_eq k B (f * g) (w.comp v) (by simp [hw, hv]),
          exchangeKernelEquivOfPullback_eq k B f w hw,
          exchangeKernelEquivOfPullback_eq k B g v hv, Path.exchangeKernelEquiv_comp]
        rfl }
  f.comp (MulEquiv.opOp _).symm.toMonoidHom

/-- On a loop representative, the modular group acts by its integral exponent transport. -/
@[simp]
theorem exchangeKernelAction_op_loop (w : Loops) :
    exchangeKernelAction k B (op (evalLoop w)) =
      Path.exchangeKernelEquiv (B := B) (C := B) w.asHom :=
  exchangeKernelEquivOfPullback_eq k B _ w.asHom
    (signedClusterModularGroupMap_unop_coe k B w).symm

/-- The exchange-kernel action is characterized by the pullback of each Casimir monomial. -/
theorem exchangeKernelAction_monomial (f : Γᵐᵒᵖ) (x : E) :
    f.unop.unop.val (χ (x : ι → ℤ)) = χ (exchangeKernelAction k B f x : ι → ℤ) := by
  obtain ⟨w, hw⟩ := signedClusterModularGroupMap_surjective k B f.unop
  rw [← op_unop f, ← hw]
  simp only [exchangeKernelAction_op_loop, signedClusterModularGroupMap_unop_coe, unop_op]
  exact (End.asHom w).xPullback_apply_monomial k x

variable {B}

/-- A charge seed with rationally spanning charges and a right-separating form has
the same charge and exchange kernels. -/
theorem ChargeSeed.exchangeKernel_eq {N : Type*} [AddCommGroup N]
    [Module.Free ℤ N] [Module.Finite ℤ N] (P : ChargeSeed B N)
    (hω : P.form.SeparatingRight) (hrank : Module.finrank ℤ P.charge.range = Module.finrank ℤ N) :
    E = P.charge.ker := by
  rw [← P.matrix_eq]
  exact ker_chargeExchangeMatrix P.form P.charge hω hrank

variable {N : Type*} [AddCommGroup N] (P : ChargeSeed B N)

variable {C : SkewExchangeMatrix ι} in
/-- Equality of the charge and exchange kernels is preserved by every signed word. -/
theorem _root_.Quiver.Path.exchangeKernel_eq_chargeTarget_ker (w : Word B C)
    (h : E = P.charge.ker) :
    C.matrix.mulVecLin.ker = (w.chargeTarget P).charge.ker := by
  rw [w.exchangeKernel_comap, w.chargeTarget_ker, h]

local notation "K" => P.charge.ker

/-- The Casimir action of the opposite signed cluster modular group on the charge kernel. -/
def chargeKernelAction (h : E = K) : Γᵐᵒᵖ →* (K ≃ₗ[ℤ] K) :=
  (LinearEquiv.autCongr (LinearEquiv.ofEq _ _ h)).toMonoidHom.comp (exchangeKernelAction k B)

private theorem chargeKernelEquiv_autCongr (h : E = K) (w : Word B B) :
    LinearEquiv.autCongr (LinearEquiv.ofEq _ _ h) w.exchangeKernelEquiv =
      (LinearEquiv.ofEq _ _ (h.symm.trans (w.exchangeKernel_eq_chargeTarget_ker P h))).trans
        (w.chargeKernelEquiv P) := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  simp only [LinearEquiv.autCongr_apply_apply, LinearEquiv.trans_apply, LinearEquiv.ofEq_symm,
    LinearEquiv.coe_ofEq_apply, Path.coe_exchangeKernelEquiv_apply,
    Path.coe_chargeKernelEquiv_apply]

/-- On a loop representative, the Casimir action is charge transport, with the terminal
kernel identified with the initial kernel. -/
@[simp]
theorem chargeKernelAction_op_loop (h : E = K) (w : Word B B) :
    chargeKernelAction k P h (op (evalLoop (End.of w))) =
      (LinearEquiv.ofEq _ _ (h.symm.trans (w.exchangeKernel_eq_chargeTarget_ker P h))).trans
        (w.chargeKernelEquiv P) := by
  rw [chargeKernelAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    exchangeKernelAction_op_loop]
  exact chargeKernelEquiv_autCongr P h w

/-- Pullback by any signed loop takes a Casimir monomial to the monomial indexed by
the group action on its exponent. -/
theorem chargeKernelAction_monomial (h : E = K) (f : Γᵐᵒᵖ) (x : K) :
    f.unop.unop.val (χ (x : ι → ℤ)) = χ (chargeKernelAction k P h f x : ι → ℤ) := by
  simpa only [chargeKernelAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    LinearEquiv.autCongr_apply_apply, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply] using
    exchangeKernelAction_monomial k B f ((LinearEquiv.ofEq _ _ h).symm x)

/-- The kernel of the Casimir action consists of the signed pullbacks fixing every
charge monomial. -/
theorem mem_ker_chargeKernelAction_iff (h : E = K) (f : Γᵐᵒᵖ) :
    f ∈ (chargeKernelAction k P h).ker ↔ ∀ x : K, f.unop.unop.val (χ (x : ι → ℤ)) = χ x := by
  simp only [MonoidHom.mem_ker, chargeKernelAction_monomial k P h]
  refine ⟨fun h₁ x ↦ by simp [h₁], fun h₁ ↦ ?_⟩
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  apply Finsupp.equivFunOnFinite.symm.injective
  exact (linearIndependent_monomial (B := ι →₀ ℤ) k).injective (h₁ x)

/-- The Casimir action of the unsigned modular group is the restriction of the signed
action to the subgroup represented by inversion-free loops. Its range is the unsigned
Casimir group. -/
def unsignedChargeKernelAction (h : E = K) :
    (ClusterModularGroup k B)ᵐᵒᵖ →* (K ≃ₗ[ℤ] K) :=
  let incl := Subgroup.inclusion (unsignedLoopPullbacks_le_signedLoopPullbacks k B)
  (chargeKernelAction k P h).comp
    (MonoidHom.op (MonoidHom.op incl))

/-- An inversion-free representative acts by the same integral charge transport in
the unsigned and signed modular groups. -/
@[simp]
theorem unsignedChargeKernelAction_op_loop (h : E = K) (w : inversionFreeLoops B) :
    unsignedChargeKernelAction k P h (op (clusterModularGroupMap k B w)) =
      chargeKernelAction k P h (op (evalLoop w.val)) := by
  have hi : (Subgroup.inclusion (unsignedLoopPullbacks_le_signedLoopPullbacks k B))
      (clusterModularGroupMap k B w).unop = (evalLoop w.val).unop := by
    apply Subtype.ext
    rw [Subgroup.coe_inclusion, clusterModularGroupMap_unop_coe,
      signedClusterModularGroupMap_unop_coe]
  exact congrArg (fun f : signedLoopPullbacks k B ↦ chargeKernelAction k P h (op (op f))) hi

end Action

section Center

variable (k : Type u) [Field k] {ι : Type u} [Fintype ι] [DecidableEq ι]
  {B : SkewExchangeMatrix ι} {N : Type*} [AddCommGroup N] (P : ChargeSeed B N)

local notation "K" => P.charge.ker
local notation "restrictCharge" => CharacterTorus.map k (LinearMap.toAddMonoidHom
  (Submodule.subtype (P.charge.ker)))

/-- The center map of a loop descends to the torus of charge characters by the Casimir
action. Its induced map there depends only on the independent X map. -/
theorem centerIso_hom_comp_chargeRestriction (h : B.matrix.mulVecLin.ker = K) (w : Word B B) :
    (w.centerIso k).hom ≫ restrictCharge =
      restrictCharge ≫
        CharacterTorus.map k (chargeKernelAction k P h
          (op (signedClusterModularGroupMap k B (End.of w)))).toLinearMap.toAddMonoidHom := by
  rw [Path.centerIso_hom, ← CharacterTorus.map_comp, ← CharacterTorus.map_comp,
    chargeKernelAction_op_loop]
  congr 1
  ext x : 1
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply,
    AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_coe]
  rw [LinearEquiv.trans_apply, Path.coe_chargeKernelEquiv_apply, LinearEquiv.coe_ofEq_apply]
  exact LinearEquiv.coe_addEquiv_apply _ _

end Center

end QPainleve.Cluster

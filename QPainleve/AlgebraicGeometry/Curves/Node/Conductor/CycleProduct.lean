/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Coordinates
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Units
public import QPainleve.AlgebraicGeometry.Curves.DualGraph.Gluing
public import QPainleve.AlgebraicGeometry.LineBundle.GluingUnit

/-!
# The product of branch gluing ratios around a nodal cycle

Rescaling on the normalization changes the branch ratios by a vertex coboundary.
For an oriented cycle, the product of those ratios identifies the conductor gluing
quotient with the multiplicative group of the field.

This is the computation with trivializations in
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
Lemma 2.1](https://arxiv.org/html/1211.6367v5#S2).
-/

public noncomputable section

open CategoryTheory TauCeti TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u v

variable {k : Type u} [Field k]
variable (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [PrestableFamily (X ↘ Spec (.of k))]
variable {ι : Type v} (p : ι → (X ↘ Spec (.of k)).smoothLocus)

local notation "nodal" => PrestableFamily.atWorstNodalOfRelativeDimensionOne
local notation "B" => branchScheme k X
local notation "N" => IdealSheafData.subscheme (singularLocus k X)
local notation "Y" => IdealSheafData.blowup (singularLocus k X)
local notation "π" => branchSchemeToSingularLocus k X
local notation "j" => branchSchemeToBlowup k X

section Product

variable [IsSepClosed k]
variable {n : ℕ} [NeZero n] (e : ZMod n ≃ (X.dualGraph p).Edge)
variable (o : (X.dualGraph p).Edge → Equiv.Perm (Fin 2))

private abbrev cycleRatios :=
  X.branchRatioHom nodal (X.branchOrderOfDualGraph p o)

private def cycleNodes : ZMod n ≃ N :=
  e.trans (X.dualGraphNodeEquiv p)

/-- The product of the oriented branch ratios at all nodes. -/
def nodalConductorCycleProduct : Γ(B, ⊤)ˣ →* kˣ :=
  ∏ i : ZMod n, (Pi.evalMonoidHom (fun _ : N ↦ kˣ) (cycleNodes X p e i)).comp (cycleRatios X p o)

private theorem nodalConductorCycleProduct_eq_prod (a : Γ(B, ⊤)ˣ) :
    X.nodalConductorCycleProduct p e o a =
      ∏ i, cycleRatios X p o a (X.dualGraphNodeEquiv p (e i)) := by
  simp [nodalConductorCycleProduct, cycleNodes]

/-- Each factor in the cycle product is the second branch value divided by the first. -/
theorem nodalConductorCycleProduct_apply (a : Γ(B, ⊤)ˣ) :
    X.nodalConductorCycleProduct p e o a = ∏ i,
      X.branchSchemeGlobalUnitsEquiv PrestableFamily.atWorstNodalOfRelativeDimensionOne a
        (X.dualGraphBranchEquiv p (e i, o (e i) 1)) /
      X.branchSchemeGlobalUnitsEquiv PrestableFamily.atWorstNodalOfRelativeDimensionOne a
        (X.dualGraphBranchEquiv p (e i, o (e i) 0)) := by
  simp only [nodalConductorCycleProduct_eq_prod, cycleRatios, branchRatioHom_apply,
    branchOrderOfDualGraph_apply_val]

/-- The cycle product takes every nonzero scalar value. -/
theorem nodalConductorCycleProduct_surjective :
    Function.Surjective (X.nodalConductorCycleProduct p e o) := by
  classical
  intro b
  let c : ZMod n → kˣ := Pi.mulSingle 0 b
  let d : N → kˣ := c ∘ (cycleNodes X p e).symm
  obtain ⟨a, ha⟩ := X.branchRatioHom_surjective nodal
    (X.branchOrderOfDualGraph p o) d
  refine ⟨a, ?_⟩
  rw [nodalConductorCycleProduct_eq_prod]
  simp only [cycleRatios, ha, d, Function.comp_apply]
  have hd (i : ZMod n) :
      (cycleNodes X p e).symm (X.dualGraphNodeEquiv p (e i)) = i :=
    (cycleNodes X p e).symm_apply_apply i
  simp [hd, c]

/-- Changing the first node of a cyclic numbering leaves the product unchanged. -/
theorem nodalConductorCycleProduct_rotate (t : ZMod n) (a : Γ(B, ⊤)ˣ) :
    X.nodalConductorCycleProduct p ((Equiv.addRight t).trans e) o a =
      X.nodalConductorCycleProduct p e o a := by
  rw [nodalConductorCycleProduct_eq_prod, nodalConductorCycleProduct_eq_prod]
  exact Equiv.prod_comp (Equiv.addRight t) fun i ↦
    cycleRatios X p o a (X.dualGraphNodeEquiv p (e i))

/-- Reversing the cyclic numbering and exchanging the two branches at every node
inverts the product. -/
theorem nodalConductorCycleProduct_reverse (t : ZMod n) (a : Γ(B, ⊤)ˣ) :
    X.nodalConductorCycleProduct p ((Equiv.subLeft t).trans e)
      (fun i ↦ (Equiv.swap 0 1).trans (o i)) a =
        (X.nodalConductorCycleProduct p e o a)⁻¹ := by
  rw [nodalConductorCycleProduct_apply, nodalConductorCycleProduct_apply, ← Finset.prod_inv_distrib]
  simpa only [Equiv.trans_apply, Equiv.swap_apply_left, Equiv.swap_apply_right, inv_div] using
    Equiv.prod_comp (Equiv.subLeft t) (fun i ↦
      (X.branchSchemeGlobalUnitsEquiv nodal a
        (X.dualGraphBranchEquiv p (e i, o (e i) 1)) /
      X.branchSchemeGlobalUnitsEquiv nodal a
        (X.dualGraphBranchEquiv p (e i, o (e i) 0)))⁻¹)

end Product

variable [IsAlgClosed k]

variable {n : ℕ} [NeZero n] (e : ZMod n ≃ (X.dualGraph p).Edge)
variable (o : (X.dualGraph p).Edge → Equiv.Perm (Fin 2))
variable (w : ZMod n ≃ (X.dualGraph p).Vertex)
variable (hw : ∀ i b, (X.dualGraph p).endpoint (e i) (o (e i) b) =
  w ((DualGraph.cycle n).endpoint i b))

include hw in
private theorem cycleRatios_appTop_normalization (u : Γ(Y, ⊤)ˣ) (i : ZMod n) :
    cycleRatios X p o (Units.map (j).appTop.hom u) (X.dualGraphNodeEquiv p (e i)) =
      (DualGraph.cycle n).gluingCoboundary kˣ (X.normalizationGlobalUnitsEquiv p u ∘ w) i := by
  have he (b : Fin 2) :
      X.branchSchemeGlobalUnitsEquiv nodal (Units.map (j).appTop.hom u)
        (X.dualGraphBranchEquiv p (e i, o (e i) b)) =
          X.normalizationGlobalUnitsEquiv p u (w ((DualGraph.cycle n).endpoint i b)) := by
    rw [← hw]
    apply X.branchSchemeGlobalUnitsEquiv_appTop_normalization
    rw [branchSchemeToBlowup_dualGraphBranchEquiv]
    exact X.branchPointEquiv_mem_dualGraph_endpoint p (e i) (o (e i) b)
  rw [DualGraph.gluingCoboundary_cycle_apply]
  simp [cycleRatios, he]

include hw in
/-- For a cyclic numbering of the components and oriented nodes, the kernel of
the product consists of the rescalings from the two sides of the conductor square. -/
theorem ker_nodalConductorCycleProduct :
    (X.nodalConductorCycleProduct p e o).ker = ((j).lineGluingCoboundary π).range := by
  ext a
  rw [MonoidHom.mem_ker, nodalConductorCycleProduct_eq_prod,
    ← DualGraph.mem_range_gluingCoboundary_cycle_iff]
  constructor
  · rintro ⟨c, hc⟩
    let u := (X.normalizationGlobalUnitsEquiv p).symm (c ∘ w.symm)
    let b := Units.map (j).appTop.hom.toMonoidHom u
    have hb : cycleRatios X p o b = cycleRatios X p o a := by
      funext z
      obtain ⟨i, rfl⟩ := (cycleNodes X p e).surjective z
      have hi := cycleRatios_appTop_normalization X p e o w hw u i
      have hcomp : (c ∘ w.symm) ∘ w = c := funext fun i ↦ congrArg c (w.symm_apply_apply i)
      rw [MulEquiv.apply_symm_apply, hcomp, hc] at hi
      exact hi
    have hdiv : b / a ∈ (cycleRatios X p o).ker := by rw [MonoidHom.mem_ker, map_div, hb, div_self']
    rw [cycleRatios, X.branchRatioHom_ker] at hdiv
    obtain ⟨t, ht⟩ := hdiv
    refine ⟨(u, t), ?_⟩
    rw [Hom.lineGluingCoboundary_apply]
    -- The first factor is the previously chosen pullback from the normalization.
    change b / Units.map (π).appTop.hom.toMonoidHom t = a
    have ht' : Units.map (π).appTop.hom.toMonoidHom t = b / a := ht
    rw [ht', div_div_cancel]
  · rintro ⟨⟨u, t⟩, rfl⟩
    have ht : cycleRatios X p o (Units.map (π).appTop.hom t) = 1 := by
      rw [← MonoidHom.mem_ker, cycleRatios, X.branchRatioHom_ker]
      exact ⟨t, rfl⟩
    refine ⟨X.normalizationGlobalUnitsEquiv p u ∘ w, funext fun i ↦ ?_⟩
    rw [Hom.lineGluingCoboundary_apply, map_div, Pi.div_apply]
    -- Evaluate the two rescalings at the node indexed by the current edge.
    change _ = cycleRatios X p o (Units.map (j).appTop.hom u) (cycleNodes X p e i) /
      cycleRatios X p o (Units.map (π).appTop.hom t) (cycleNodes X p e i)
    rw [congrFun ht (cycleNodes X p e i), Pi.one_apply, div_one]
    exact (cycleRatios_appTop_normalization X p e o w hw u i).symm

include hw in
/-- The oriented cycle product identifies the conductor gluing quotient with
the multiplicative group of the base field. -/
def nodalConductorCycleProductEquiv :
    (Γ(B, ⊤)ˣ ⧸ ((j).lineGluingCoboundary π).range) ≃* kˣ :=
  (QuotientGroup.quotientMulEquivOfEq (X.ker_nodalConductorCycleProduct p e o w hw).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (X.nodalConductorCycleProduct_surjective p e o))

include hw in
@[simp]
theorem nodalConductorCycleProductEquiv_mk (a : Γ(B, ⊤)ˣ) :
    X.nodalConductorCycleProductEquiv p e o w hw (QuotientGroup.mk a) =
      X.nodalConductorCycleProduct p e o a := by
  rw [nodalConductorCycleProductEquiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

end AlgebraicGeometry.Scheme

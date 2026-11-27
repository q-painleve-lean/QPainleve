/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.MarkedComparison
public import QPainleve.SignedClusterModularGroup.Realization.PicardAction

import QPainleve.SignedClusterModularGroup.Realization.BranchAction
import QPainleve.SignedClusterModularGroup.Realization.Evaluation

/-!
# Identity detection and the unsigned Picard kernel

An orientation-preserving loop whose marked Picard pullback is trivial can be
compared with the identity realization. Distinct boundary classes determine the
component permutation by `GeometricRealization.cycleVertexPerm_eq_of_picard_eq`.
The comparison `GeometricRealization.xMap_eq_of_marked_actions_eq` then detects
equality on the independent X coordinates.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory MulOpposite Scheme
open QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric DiagonalizableGroup

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [hΦ₀ : Nonempty Φ.cones]
  {r m n : ℕ} [NeZero m] [NeZero n] {L : Type} [AddCommGroup L]
  {B : LinearMap.BilinForm ℤ L} {E : SkewExchangeMatrix (Fin r)}
  {A N₀ : Type} [AddCommGroup A] [AddCommGroup N₀] [IsAddFG A] [IsAddFG N₀]
  [Module.Free ℤ A] [Module.Free ℤ N₀]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "X[" coeff "," r "]" => scheme coeff (Fin r →₀ ℤ)
local notation "sX[" k "," r "]" => structureMap k (Fin r →₀ ℤ)
local notation "T[" coeff "," M "]" => Grp.X (groupScheme coeff (FGCommGrpCat.of
  (Multiplicative M)))
local notation "Dtor[" coeff "," Φ "," h "]" => Scheme.IdealSheafData.subscheme
  (Fan.toricBoundaryIdeal coeff Φ h)
local notation "F[" E "," w "]" =>
  Quiver.Path.xRationalMap k₀ (End.asHom (Subtype.val (w : inversionFreeLoops E)))

variable [Smooth T[k₀,A].hom] [(Φ.finiteFanScheme k₀).IsProjectiveOver k₀] [B.IsPerfPair]
  {P : Point T[k₀,A] → MarkedSurface k₀ n B X[k₀,r]}
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}
  [PrestableFamily (Dtor[k₀,Φ,hΦ₀] ↘ Spec (.of k₀))] {γ : Type*} {a : γ →
    (Dtor[k₀,Φ,hΦ₀] ↘ Spec (.of k₀)).smoothLocus}
  {T : NodalCycleNumbering a m} {origin : ZMod m}
  {ι : L →ₗ[ℤ] Additive (LineBundleClass (Φ.finiteFanScheme k₀)) × (Fin r → ℤ)}
  (centers : Point T[k₀,A] → Multiplicative (Fin r → ℤ) →* k₀ˣ)

variable (hc : Φ.IsComplete) (u : ZMod m ≃ Φ.Ray)
  (hvertices : ∀ j, Dtor[k₀,Φ,hΦ₀].dualGraphVertexEquiv a (T.vertex j) =
    Φ.boundaryNormalizationComponentEquiv k₀ hΦ (u j))
  (hdet : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1)
  (hnodes : ∀ j, ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ ∧
    (Fan.toricBoundaryIdeal k₀ Φ hΦ₀).subschemeι (Dtor[k₀,Φ,hΦ₀].dualGraphEdgeEquiv a
      (T.edge j)).val =
      (Φ.distinguishedSection (R := k₀) σ) (IsLocalRing.closedPoint k₀))
  (survives : Set Φ.Ray)
  (hmodels : ∀ c, ∃ p : ContractedToricFiber b s hΦ T origin ι (centers c) (P c),
    p.IsNodalContraction ∧ Set.range p.boundaryRayEmbedding = survives)
  (D : ZMod n → L)
  (hmark : ∀ c j, (P c).boundaryClass (hmodels c).choose_spec.1.cartier j = D j)
  (e : T[k₀,A].left ≅ X[k₀,r]) (he : e.hom ≫ sX[k₀,r] = T[k₀,A].hom)
  (v : A →+ N₀)
  (hchart : ∀ c : Point T[k₀,A], ∃ (j : T[k₀,N₀].left ⤏ (P c).surface) (_ : j.IsDominant),
    j.comp (P c).evaluation = ((evaluationAtCenter k₀ v c.left (Over.w c)) ≫ e.hom).toRationalMap)

omit [Smooth T[k₀,A].hom] in
include he in
omit [IsAlgClosed k₀] in
private theorem isOver_precomp {F : X[k₀,r] ⤏ X[k₀,r]} [F.IsDominant] [F.IsOver sX[k₀,r] sX[k₀,r]] :
    (e.hom.toRationalMap.comp F).IsOver T[k₀,A].hom sX[k₀,r] := by
  have h : e.hom.toRationalMap.IsOver T[k₀,A].hom sX[k₀,r] := by
    rw [RationalMap.isOver_iff, Hom.toRationalMap_compHom, he]
  exact RationalMap.isOver_comp e.hom.toRationalMap h F inferInstance

include hvertices hdet hnodes hmodels hmark hc he hchart in
/-- A geometric self-realization over a fixed ordered toric presentation with
distinct marked boundary classes represents the identity X map if its Picard
pullback is the identity and it preserves the boundary orientation. -/
theorem xMap_eq_id_of_picard_eq_refl
    {C : T[k₀,A].left.PartialMap T[k₀,A].left} [IsDominant C.hom] [C.IsOver T[k₀,A].hom T[k₀,A].hom]
    {F : X[k₀,r] ⤏ X[k₀,r]} [F.IsDominant] [F.IsOver sX[k₀,r] sX[k₀,r]]
    (R : GeometricRealization P P C F) (hinj : Function.Injective D)
    (hI : R.picard = .refl B) (hη : R.orientation = 1) :
    F = RationalMap.id X[k₀,r] := by
  let R' := refl P
  have hpic : R.picard = R'.picard := hI.trans (refl_picard P).symm
  have horient : R.orientation = R'.orientation := by
    simpa only [R', orientation_def, refl_boundaryAction, map_one] using hη
  let : (e.hom.toRationalMap.comp F).IsOver T[k₀,A].hom sX[k₀,r] := isOver_precomp e he
  let : (RationalMap.id X[k₀,r]).IsOver sX[k₀,r] sX[k₀,r] := by
    rw [RationalMap.isOver_iff, RationalMap.id_compHom]
  let : (e.hom.toRationalMap.comp (RationalMap.id X[k₀,r])).IsOver T[k₀,A].hom sX[k₀,r] :=
    isOver_precomp e he
  have : Nonempty C.domain := C.dense_domain.nonempty.to_subtype
  refine RationalMap.comp_left_injective e.hom.toRationalMap ?_
  refine (R.precompEvaluation e).xMap_eq_of_marked_actions_eq (R'.precompEvaluation e)
    (by simpa only [precompEvaluation_picard] using hpic)
    (by simpa only [precompEvaluation_boundaryAction] using
      R.boundaryAction_eq_of_picard_eq_of_orientation_eq R' hmark hmark hinj hpic horient)
    v sX[k₀,r] C.domain le_rfl le_top (fun c _ ↦ ?_) hc u hvertices hdet hnodes centers survives
    (.of_forall hmodels) (.of_forall hmodels)
  obtain ⟨j, hj, hj'⟩ := hchart c
  let : j.IsDominant := hj
  refine ⟨j, hj, ?_⟩
  have h := RationalMap.comp_compHom j (P c).evaluation e.inv
  calc
    _ = (j.comp (P c).evaluation).compHom e.inv :=
      (congrArg (fun f : (P c).surface ⤏ T[k₀,A].left ↦ j.comp f)
        ((P c).compEvaluation_evaluation e.inv)).trans h
    _ = _ := by rw [hj', Hom.toRationalMap_compHom, Category.assoc, e.hom_inv_id, Category.comp_id]

-- The endpoint projection is an endomorphism in the path category.
local instance (w : inversionFreeLoops E) : F[E,w].IsDominant :=
  Quiver.Path.instIsDominantXRationalMap k₀ (End.asHom w.val)

local instance (w : inversionFreeLoops E) : F[E,w].IsOver sX[k₀,r] sX[k₀,r] :=
  Quiver.Path.instIsOverXRationalMapStructureMapFinsuppInt k₀ (End.asHom w.val)

include hc hvertices hdet hnodes hmodels hmark he hchart in
/-- The descended Picard homomorphism of orientation-preserving cluster loops has
trivial kernel. The ordered toric models share the same surviving rays, and the
fixed-center evaluations are the fibers of variable-center evaluation on dominant
charts. Distinct marked boundary classes recover the component permutation
from the Picard pullback, including for one- and two-component boundaries. -/
theorem picardHom_ker_eq_bot
    (ρ : (ClusterModularGroup k₀ E)ᵐᵒᵖ →* boundaryRotationGroup B D)
    (hρ : ∀ (w : inversionFreeLoops E)
      {C : T[k₀,A].left.PartialMap T[k₀,A].left} [IsDominant C.hom]
        [C.IsOver T[k₀,A].hom T[k₀,A].hom]
      (R : GeometricRealization P P C F[E,w]),
      (ρ (op (clusterModularGroupMap k₀ E w)) : B.isometryGroup) =
        (LinearMap.BilinForm.isometryGroupEquivIsometryEquiv B).symm R.picard)
    (hreal : ∀ w : inversionFreeLoops E, ∃ (C : T[k₀,A].left.PartialMap T[k₀,A].left)
      (hC : IsDominant C.hom) (hCO : C.IsOver T[k₀,A].hom T[k₀,A].hom),
      letI := hC
      letI := hCO
      ∃ R : GeometricRealization P P C F[E,w], R.orientation = 1)
    (hinj : Function.Injective D) : ρ.ker = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨w, hw⟩ := clusterModularGroupMap_surjective k₀ E g.unop
  have hg' : op (clusterModularGroupMap k₀ E w) = g := (congrArg op hw).trans (op_unop g)
  obtain ⟨C, hC, hCO, R, hη⟩ := hreal w
  have hI : R.picard = .refl B := by
    apply (LinearMap.BilinForm.isometryGroupEquivIsometryEquiv B).symm.injective
    rw [← hρ w R, hg', MonoidHom.mem_ker.mp hg]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro a
    exact (congrFun (LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv_symm B
      (LinearMap.BilinForm.IsometryEquiv.refl B)) a).symm
  have hF := xMap_eq_id_of_picard_eq_refl centers hc u hvertices hdet hnodes survives hmodels
    D hmark e he v hchart R hinj hI hη
  have hgroup : clusterModularGroupMap k₀ E w = clusterModularGroupMap k₀ E 1 := by
    apply (clusterModularGroupMap_eq_iff k₀ E _ _).mpr
    apply (Quiver.Path.xRationalMap_eq_iff k₀ _ _).mp
    exact hF.trans (Quiver.Path.xRationalMap_nil k₀).symm
  rw [map_one] at hgroup
  rw [← hg', hgroup, op_one]

end QPainleve.SignedClusterModularGroup.GeometricRealization

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

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [hΦ₀ : Nonempty Φ.cones]
  {r m n : ℕ} [NeZero m] [NeZero n] {L : Type} [AddCommGroup L]
  {B : LinearMap.BilinForm ℤ L} {E : SkewExchangeMatrix (Fin r)}
  {A N₀ : Type} [AddCommGroup A] [AddCommGroup N₀] [IsAddFG A] [IsAddFG N₀]
  [Module.Free ℤ A] [Module.Free ℤ N₀]

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "sX[" r "]" => structureMap ℂ (Fin r →₀ ℤ)
local notation "T[" M "]" => Grp.X (groupScheme ℂ (FGCommGrpCat.of (Multiplicative M)))
local notation "Dtor[" Φ "," h "]" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h)
local notation "F[" E "," w "]" =>
  Quiver.Path.xRationalMap ℂ (End.asHom (Subtype.val (w : inversionFreeLoops E)))

variable [Smooth T[A].hom] [Φ.algebraicRealization.IsProjectiveOver ℂ] [B.IsPerfPair]
  {P : Point T[A] → MarkedSurface ℂ n B X[r]}
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}
  [PrestableFamily (Dtor[Φ,hΦ₀] ↘ S)] {γ : Type*} {a : γ → (Dtor[Φ,hΦ₀] ↘ S).smoothLocus}
  {T : NodalCycleNumbering a m} {origin : ZMod m}
  {ι : L →ₗ[ℤ] Additive (LineBundleClass Φ.algebraicRealization) × (Fin r → ℤ)}
  (centers : Point T[A] → Multiplicative (Fin r → ℤ) →* ℂˣ)

local notation "D[" P "," c "]" =>
  Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair (P c))))

variable (hc : Φ.IsComplete) (u : ZMod m ≃ Φ.Ray)
  (hvertices : ∀ j, Dtor[Φ,hΦ₀].dualGraphVertexEquiv a (T.vertex j) =
    Φ.boundaryNormalizationComponentEquiv hΦ (u j))
  (hdet : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1)
  (hnodes : ∀ j, ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ ∧
    (Fan.boundaryIdeal Φ hΦ₀).subschemeι (Dtor[Φ,hΦ₀].dualGraphEdgeEquiv a (T.edge j)).val =
      Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
  (survives : Set Φ.Ray)
  (hmodels : ∀ c, ∃ p : ContractedToricFiber b s hΦ T origin ι (centers c) (P c),
    p.IsNodalContraction ∧ ∀ ρ : Φ.Ray,
      p.projection (Fan.internalBlowupBoundaryPrimeEquiv hΦ b s
        (fun j ↦ centers c (Multiplicative.ofAdd (Pi.single j 1))) ρ).val ∈
        D[P,c].boundaryPrimes ↔ ρ ∈ survives)
  (D : ZMod n → L)
  (hmark : ∀ c j, (P c).boundaryClass (hmodels c).choose_spec.1.cartier j = D j)
  (e : T[A].left ≅ X[r]) (he : e.hom ≫ sX[r] = T[A].hom)
  (v : A →+ N₀)
  (hchart : ∀ c : Point T[A], ∃ (j : T[N₀].left ⤏ (P c).surface) (_ : j.IsDominant),
    j.comp (P c).evaluation = ((evaluationAtCenter ℂ v c.left (Over.w c)) ≫ e.hom).toRationalMap)

omit [Smooth T[A].hom] in
include he in
private theorem isOver_precomp {F : X[r] ⤏ X[r]} [F.IsDominant] [F.IsOver sX[r] sX[r]] :
    (e.hom.toRationalMap.comp F).IsOver T[A].hom sX[r] := by
  have h : e.hom.toRationalMap.IsOver T[A].hom sX[r] := by
    rw [RationalMap.isOver_iff, Hom.toRationalMap_compHom, he]
  exact RationalMap.isOver_comp e.hom.toRationalMap h F inferInstance

include hvertices hdet hnodes hmodels hmark hc he hchart in
/-- A geometric self-realization over a fixed ordered toric presentation with
distinct marked boundary classes represents the identity X map if its Picard
pullback is the identity and it preserves the boundary orientation. -/
theorem xMap_eq_id_of_picard_eq_refl
    {C : T[A].left.PartialMap T[A].left} [IsDominant C.hom] [C.IsOver T[A].hom T[A].hom]
    {F : X[r] ⤏ X[r]} [F.IsDominant] [F.IsOver sX[r] sX[r]]
    (R : GeometricRealization P P C F) (hinj : Function.Injective D)
    (hI : R.picard = .refl B) (hη : R.orientation = 1) :
    F = RationalMap.id X[r] := by
  let R' := refl P
  have hpic : R.picard = R'.picard := hI.trans (refl_picard P).symm
  have hperm := R.cycleVertexPerm_eq_of_picard_eq R' hmark hmark hinj hpic
  have horient : R.orientation = R'.orientation := by
    simpa only [R', orientation_def, refl_boundaryAction, map_one] using hη
  let : (e.hom.toRationalMap.comp F).IsOver T[A].hom sX[r] := isOver_precomp e he
  let : (RationalMap.id X[r]).IsOver sX[r] sX[r] := by
    rw [RationalMap.isOver_iff, RationalMap.id_compHom]
  let : (e.hom.toRationalMap.comp (RationalMap.id X[r])).IsOver T[A].hom sX[r] :=
    isOver_precomp e he
  have : Nonempty C.domain := C.dense_domain.nonempty.to_subtype
  refine RationalMap.comp_left_injective e.hom.toRationalMap ?_
  refine (R.precompEvaluation e).xMap_eq_of_marked_actions_eq (R'.precompEvaluation e)
    (by simpa only [precompEvaluation_picard] using hpic)
    (by simpa only [boundaryPerm_def, precompEvaluation_boundaryAction] using hperm)
    (by simpa only [orientation_def, precompEvaluation_boundaryAction] using horient)
    v sX[r] C.domain le_rfl le_top (fun c _ ↦ ?_) hc u hvertices hdet hnodes centers survives
    (fun c ↦ hmodels (c ≫ C.domainTarget)) (fun c ↦ hmodels (c ≫ _))
  obtain ⟨j, hj, hj'⟩ := hchart c
  let : j.IsDominant := hj
  refine ⟨j, hj, ?_⟩
  have h := RationalMap.comp_compHom j (P c).evaluation e.inv
  calc
    _ = (j.comp (P c).evaluation).compHom e.inv :=
      (congrArg (fun f : (P c).surface ⤏ T[A].left ↦ j.comp f)
        ((P c).compEvaluation_evaluation e.inv)).trans h
    _ = _ := by rw [hj', Hom.toRationalMap_compHom, Category.assoc, e.hom_inv_id, Category.comp_id]

-- The endpoint projection is an endomorphism in the path category.
local instance (w : inversionFreeLoops E) : F[E,w].IsDominant :=
  Quiver.Path.instIsDominantXRationalMap ℂ (End.asHom w.val)

local instance (w : inversionFreeLoops E) : F[E,w].IsOver sX[r] sX[r] :=
  Quiver.Path.instIsOverXRationalMapStructureMapFinsuppInt ℂ (End.asHom w.val)

include hc hvertices hdet hnodes hmodels hmark he hchart in
/-- The descended Picard homomorphism of orientation-preserving cluster loops has
trivial kernel. The ordered toric models share the same surviving rays, and the
fixed-center evaluations are the fibers of variable-center evaluation on dominant
charts. Distinct marked boundary classes recover the component permutation
from the Picard pullback, including for one- and two-component boundaries. -/
theorem picardHom_ker_eq_bot
    (ρ : (ClusterModularGroup ℂ E)ᵐᵒᵖ →* boundaryRotationGroup B D)
    (hρ : ∀ (w : inversionFreeLoops E)
      {C : T[A].left.PartialMap T[A].left} [IsDominant C.hom] [C.IsOver T[A].hom T[A].hom]
      (R : GeometricRealization P P C F[E,w]),
      (ρ (op (clusterModularGroupMap ℂ E w)) : B.isometryGroup) =
        (LinearMap.BilinForm.isometryGroupEquivIsometryEquiv B).symm R.picard)
    (hreal : ∀ w : inversionFreeLoops E, ∃ (C : T[A].left.PartialMap T[A].left)
      (hC : IsDominant C.hom) (hCO : C.IsOver T[A].hom T[A].hom),
      letI := hC
      letI := hCO
      ∃ R : GeometricRealization P P C F[E,w], R.orientation = 1)
    (hinj : Function.Injective D) : ρ.ker = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨w, hw⟩ := clusterModularGroupMap_surjective ℂ E g.unop
  have hg' : op (clusterModularGroupMap ℂ E w) = g := (congrArg op hw).trans (op_unop g)
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
  have hgroup : clusterModularGroupMap ℂ E w = clusterModularGroupMap ℂ E 1 := by
    apply (clusterModularGroupMap_eq_iff ℂ E _ _).mpr
    apply (Quiver.Path.xRationalMap_eq_iff ℂ _ _).mp
    exact hF.trans (Quiver.Path.xRationalMap_nil ℂ).symm
  rw [map_one] at hgroup
  rw [← hg', hgroup, op_one]

end QPainleve.SignedClusterModularGroup.GeometricRealization

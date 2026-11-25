/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Conjugation
public import QPainleve.SignedClusterModularGroup.Boundary.Conjugation
public import QPainleve.SignedClusterModularGroup.Realization.PicardAction

/-!
# Change of base seed for the Picard action

A realization of a connecting word changes the Picard marking by its marked
pullback. The Picard homomorphisms at the two seeds intertwine the conjugation
of cluster loops and the conjugation of boundary rotations. The comparison
uses the two orders of composition with the connecting realization.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup MulOpposite Multiplicative
open QPainleve.CharacterTorus QPainleve.Cluster TauCeti.AlgebraicGeometry TauCeti.Toric
open LinearMap (BilinForm)
open Scheme

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {n : ℕ} [NeZero n] {L₀ L₁ : Type} [AddCommGroup L₀] [AddCommGroup L₁]
  {B₀ : BilinForm ℤ L₀} {B₁ : BilinForm ℤ L₁} {d₀ : ZMod n → L₀} {d₁ : ZMod n → L₁}

section BoundaryMarking

variable {k : Type} [Field k] [IsSepClosed k] [Infinite k]
  {X Y : Scheme} [IsIntegral X] [X.IsSeparated] [Y.IsSeparated]
  {T₀ T₁ : Over (Spec (.of k))} [Nonempty T₀.left] [Smooth T₀.hom]
  {P₀ : Point T₀ → MarkedSurface k n B₀ X} {P₁ : Point T₁ → MarkedSurface k n B₁ Y}
  {C : T₀.left.PartialMap T₁.left} [IsDominant C.hom] [C.IsOver T₀.hom T₁.hom]
  {F : X ⤏ Y} [F.IsDominant]
  (R : GeometricRealization P₀ P₁ C F)
  {h₀ : ∀ c, (P₀ c).pair.hom.left.ker.IsEffectiveCartier}
  {h₁ : ∀ c, (P₁ c).pair.hom.left.ker.IsEffectiveCartier}
  (hd₀ : ∀ c j, (P₀ c).boundaryClass (h₀ c) j = d₀ j)
  (hd₁ : ∀ c j, (P₁ c).boundaryClass (h₁ c) j = d₁ j)

/-- The marked Picard pullback of a realization identifies the two boundary
rotation groups by conjugation. -/
def boundaryRotationGroupCongr :
    boundaryRotationGroup B₀ d₀ ≃* boundaryRotationGroup B₁ d₁ :=
  QPainleve.boundaryRotationGroupCongr R.picard (ε := cycleOrientationSign R.boundaryAction⁻¹)
    (a := cycleVertexPerm R.boundaryAction⁻¹ 0) (fun j ↦ by
      obtain ⟨c⟩ := nonempty_centerPoint C
      have h := R.picard_boundaryClass c (h₀ _) (h₁ _) j
      rw [hd₀, hd₁, cycleVertexPerm_apply R.boundaryAction⁻¹ j, ← Units.smul_def] at h
      exact h)

@[simp]
theorem boundaryRotationGroupCongr_apply_apply (g : boundaryRotationGroup B₀ d₀) (x : L₁) :
    (R.boundaryRotationGroupCongr hd₀ hd₁ g).val.val x = R.picard.symm (g.val.val (R.picard x)) :=
  QPainleve.boundaryRotationGroupCongr_apply_apply ..

end BoundaryMarking

section Words

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "Maps[" E "]" => (ClusterModularGroup ℂ E)ᵐᵒᵖ
local notation "eval[" E "," v "]" => op (clusterModularGroupMap ℂ E v)
local notation "asIsometry[" B "]" => Equiv.symm (BilinForm.isometryGroupEquivIsometryEquiv B)
local notation "xmap[" E "," v "]" =>
  Quiver.Path.xRationalMap (B := E) (C := E) ℂ (End.asHom (Subtype.val v))

variable {r : ℕ} {E₀ E₁ : SkewExchangeMatrix (Fin r)}
  {T₀ T₁ : Over S} [Nonempty T₀.left] [Smooth T₀.hom] [PreirreducibleSpace T₀.left]
  [Nonempty T₁.left] [Smooth T₁.hom]
  {P₀ : Point T₀ → MarkedSurface ℂ n B₀ X[r]} {P₁ : Point T₁ → MarkedSurface ℂ n B₁ X[r]}
  {C : T₀.left.PartialMap T₁.left} [IsDominant C.hom] [C.IsOver T₀.hom T₁.hom]
  {w : Word E₀ E₁} (R : GeometricRealization P₀ P₁ C (w.xRationalMap ℂ))
  {h₀ : ∀ c, (P₀ c).pair.hom.left.ker.IsEffectiveCartier}
  {h₁ : ∀ c, (P₁ c).pair.hom.left.ker.IsEffectiveCartier}
  (hd₀ : ∀ c j, (P₀ c).boundaryClass (h₀ c) j = d₀ j)
  (hd₁ : ∀ c j, (P₁ c).boundaryClass (h₁ c) j = d₁ j)

-- The path-category endomorphism projection uses the path-category hom type.
local instance {E : SkewExchangeMatrix (Fin r)} (v : inversionFreeLoops E) :
    xmap[E,v].IsDominant :=
  Quiver.Path.instIsDominantXRationalMap ℂ (End.asHom v.val)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [hΦ₀ : Nonempty Φ.cones]
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}
  {m : ℕ} [NeZero m] [PrestableFamily ((Φ.boundaryIdeal hΦ₀).subscheme ↘ S)]
  {γ : Type*} {p : γ → ((Φ.boundaryIdeal hΦ₀).subscheme ↘ S).smoothLocus}
  {T : NodalCycleNumbering p m} {origin : ZMod m}
  {ι : L₁ →ₗ[ℤ] Additive (LineBundleClass Φ.algebraicRealization) × (Fin r → ℤ)}
  {centers : Point T₁ → Multiplicative (Fin r → ℤ) →* ℂˣ}

local notation "Models[" D "]" =>
  HasToricTargetModels (b := b) (s := s) (hΦ := hΦ) (T := T) (origin := origin)
    (ι := ι) (P₁ := P₁) centers D

/-- A realized change of base seed intertwines the two Picard homomorphisms.
The loop actions are evaluated on realizations at the respective seeds. Only
the reached fibers at the target of the change of seed need the finite-index
toric comparison. The connecting word may contain inversions. -/
theorem picardHom_base_change
    (hc : Φ.IsComplete) (hι : Function.Injective ι)
    (hindex : (Fan.rayChargeMap s).range.toAddSubgroup.index ≠ 0) (hC : Models[C])
    (ρ₀ : Maps[E₀] →* boundaryRotationGroup B₀ d₀)
    (ρ₁ : Maps[E₁] →* boundaryRotationGroup B₁ d₁)
    (hreal₀ : ∀ v : inversionFreeLoops E₀, ∃ (D : T₀.left.PartialMap T₀.left)
      (hD : IsDominant D.hom) (hDO : D.IsOver T₀.hom T₀.hom),
      letI := hD
      letI := hDO
      ∃ A : GeometricRealization P₀ P₀ D xmap[E₀,v],
        (ρ₀ eval[E₀,v]).val = asIsometry[B₀] A.picard)
    (hreal₁ : ∀ v : inversionFreeLoops E₁, ∃ (D : T₁.left.PartialMap T₁.left)
      (hD : IsDominant D.hom) (hDO : D.IsOver T₁.hom T₁.hom),
      letI := hD
      letI := hDO
      ∃ A : GeometricRealization P₁ P₁ D xmap[E₁,v],
        Models[D] ∧ (ρ₁ eval[E₁,v]).val = asIsometry[B₁] A.picard) :
    ρ₁.comp (MulEquiv.op (clusterModularGroupCongr ℂ w)).toMonoidHom =
      (R.boundaryRotationGroupCongr hd₀ hd₁).toMonoidHom.comp ρ₀ := by
  apply MonoidHom.ext
  intro g
  obtain ⟨u, hu⟩ := clusterModularGroupMap_surjective ℂ E₀ g.unop
  obtain ⟨v, hv⟩ := clusterModularGroupMap_surjective ℂ E₁ (clusterModularGroupCongr ℂ w g.unop)
  obtain ⟨D, hD, hDO, A, hA⟩ := hreal₀ u
  obtain ⟨J, hJ, hJO, B, hmodel, hB⟩ := hreal₁ v
  let := hD
  let := hDO
  let := hJ
  let := hJO
  -- The two composites act alike on independent X coordinates.
  let u' : Word E₀ E₀ := u.val.asHom
  let v' : Word E₁ E₁ := v.val.asHom
  have hx : v'.xPullback ℂ = ((w.reverse.comp u').comp w).xPullback ℂ :=
    (clusterModularGroupMap_eq_congr_iff ℂ w u'
      ((mem_inversionFreeLoops_iff E₀ _).mp u.property) v'
      ((mem_inversionFreeLoops_iff E₁ _).mp v.property)).mp (hu.symm ▸ hv)
  have hcomp : (w.xRationalMap ℂ).comp xmap[E₁,v] = xmap[E₀,u].comp (w.xRationalMap ℂ) := by
    have h := (Quiver.Path.xRationalMap_eq_iff ℂ (w.comp v') (u'.comp w)).mpr (by
      simp only [Quiver.Path.xPullback_comp, hx, Quiver.Path.xPullback_reverse]
      group)
    simpa only [Quiver.Path.xRationalMap_comp] using h
  have hmodels₁ : Models[C.comp J] := fun c ↦ by
    simpa only [Category.assoc, PartialMap.compDomainRight_target] using
      hmodel (c ≫ C.compDomainRight J)
  have hmodels₀ : Models[D.comp C] := fun c ↦ by
    simpa only [Category.assoc, PartialMap.compDomainRight_target] using
      hC (c ≫ D.compDomainRight C)
  obtain ⟨hpic, _⟩ := (R.comp B).marked_actions_eq_of_xMap_eq (A.comp R)
    hcomp hc hι hindex centers hmodels₁ hmodels₀
  have hg : g = eval[E₀,u] := op_unop g ▸ congrArg op hu.symm
  have hv' : MulEquiv.op (clusterModularGroupCongr ℂ w) g = eval[E₁,v] := congrArg op hv.symm
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hv']
  rw [hg]
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [boundaryRotationGroupCongr_apply_apply, hA, hB]
  simp only [BilinForm.coe_isometryGroupEquivIsometryEquiv_symm]
  have h := congrArg (fun e : B₁.IsometryEquiv B₀ ↦ e x) hpic
  simp only [comp_picard, BilinForm.IsometryEquiv.trans_apply] at h
  simpa only [BilinForm.IsometryEquiv.symm_apply_apply] using congrArg R.picard.symm h

end Words

end QPainleve.SignedClusterModularGroup.GeometricRealization

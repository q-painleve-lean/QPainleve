/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RationalMap.Composition.Inverse
public import QPainleve.AlgebraicGeometry.RationalMap.Family
public import QPainleve.AlgebraicGeometry.RationalMap.PartialIso
public import QPainleve.SignedClusterModularGroup.Realization.Basic

/-!
# Inverses of geometric realizations

An inverse realization uses the inverse isomorphism on each pair, the inverse
Picard pullback and the inverse dihedral action. When the evaluations come from
a dominant regular map on an open family of charts, the generic domain
condition for the inverse X map holds on a dense open of target centers.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace QPainleve.SignedClusterModularGroup

variable {k : Type u} [Field k] [IsSepClosed k] [Infinite k] {n : ℕ} [NeZero n]
  {L₀ L₁ : Type u} [AddCommGroup L₀] [AddCommGroup L₁]
  {B₀ : LinearMap.BilinForm ℤ L₀} {B₁ : LinearMap.BilinForm ℤ L₁}
  {X₀ X₁ : Scheme.{u}} [IsIntegral X₀] [IsIntegral X₁] [X₀.IsSeparated] [X₁.IsSeparated]

local notation "S" => Spec (CommRingCat.of k)

open MarkedSurface (surfaceIso boundaryIso)

namespace FiberRealization

variable {M : MarkedSurface k n B₀ X₀} {N : MarkedSurface k n B₁ X₁}
  {F : X₀ ⤏ X₁} [F.IsDominant] {G : X₁ ⤏ X₀}
  {I : B₁.IsometryEquiv B₀} {g : DihedralGroup n}

/-- Reverse a realization at a center where the target evaluation lies in the
domain of the inverse X map at the generic point. -/
def symm (R : FiberRealization M N F I g) (hFG : F.comp G = RationalMap.id X₀)
    (hG : N.evaluation.fromFunctionField (IsLocalRing.closedPoint N.surface.functionField) ∈
      G.domain) : FiberRealization N M G I.symm g⁻¹ where
  iso := R.iso.symm
  picard_eq a := by
    have h := R.picard_eq (I.symm a)
    have hI : I (I.symm a) = a := I.toLinearEquiv.apply_symm_apply a
    rw [hI] at h
    let e := LineBundleClass.pullbackEquiv (surfaceIso R.iso)
    have hp : (M.picardMarking a).toMul = e (N.picardMarking (I.symm a)).toMul := by
      simpa only [e, toMul_ofMul, LineBundleClass.pullbackEquiv_apply] using
        congrArg Additive.toMul h
    have hh : (N.picardMarking (I.symm a)).toMul = e.symm (M.picardMarking a).toMul :=
      (e.symm_apply_apply _).symm.trans (congrArg e.symm hp.symm)
    apply Additive.toMul.injective
    simpa only [e, MarkedSurface.surfaceIso_symm, toMul_ofMul,
      LineBundleClass.pullbackEquiv_symm, LineBundleClass.pullbackEquiv_apply] using hh
  boundaryAction_eq := by
    let : PrestableFamily (M.boundary ↘ S) := M.prestable
    let : PrestableFamily (N.boundary ↘ S) := N.prestable
    dsimp only
    simpa only [← MarkedSurface.boundaryIso_symm] using
      (Iso.boundaryCycleAction_symm (boundaryIso R.iso) M.cycle N.cycle).trans
        (congrArg Inv.inv R.boundaryAction_eq)
  evaluation_eq := by
    obtain ⟨hF, he⟩ := R.evaluation_eq
    refine ⟨hG, ?_⟩
    simpa only [MarkedSurface.surfaceIso_symm, Iso.symm_hom] using
      RationalMap.compOfDefined_eq_inv_comp_of_comp_eq _ _ _ F G hFG hF hG he

@[simp]
theorem symm_iso (R : FiberRealization M N F I g) (hFG : F.comp G = RationalMap.id X₀)
    (hG : N.evaluation.fromFunctionField (IsLocalRing.closedPoint N.surface.functionField) ∈
      G.domain) : (R.symm hFG hG).iso = R.iso.symm := (rfl)

end FiberRealization

namespace GeometricRealization

variable {T₀ T₁ : Over (Spec (CommRingCat.of k))} [Nonempty T₀.left] [Smooth T₀.hom]
  [Nonempty T₁.left] [Smooth T₁.hom]
  {P₀ : Point T₀ → MarkedSurface k n B₀ X₀} {P₁ : Point T₁ → MarkedSurface k n B₁ X₁}
  {C : T₀.left.PartialIso T₁.left} [C.toPartialMap.IsOver T₀.hom T₁.hom]
  {F : X₀ ⤏ X₁} [F.IsDominant] {G : X₁ ⤏ X₀} [G.IsDominant]
  (R : GeometricRealization P₀ P₁ C.toPartialMap F)

/-- Invert a geometric realization over a dense open of the inverse center domain
where every target fiber evaluation can be followed by the inverse X map. -/
def symmOn (hFG : F.comp G = RationalMap.id X₀)
    (W : T₁.left.Opens) (hW : Dense (W : Set T₁.left)) (hWC : W ≤ C.symm.toPartialMap.domain)
    (hG : ∀ c : CenterPoint (C.symm.toPartialMap.restrict W hW hWC),
      let M := P₁ (c ≫ (C.symm.toPartialMap.restrict W hW hWC).domainSource)
      M.evaluation.fromFunctionField (IsLocalRing.closedPoint M.surface.functionField) ∈
        G.domain) :
    GeometricRealization P₁ P₀ (C.symm.toPartialMap.restrict W hW hWC) G where
  picard := R.picard.symm
  boundaryAction := R.boundaryAction⁻¹
  fiber c := by
    let d := (c ≫ C.symm.toPartialMap.restrictDomainHom W hW hWC) ≫ C.domainOverIso.inv
    have hs : d ≫ C.toPartialMap.domainSource =
        c ≫ (C.symm.toPartialMap.restrict W hW hWC).domainTarget := by
      simp only [d, Category.assoc, PartialIso.domainOverIso_inv_source,
        PartialMap.restrictDomainHom_target]
    have ht : d ≫ C.toPartialMap.domainTarget =
        c ≫ (C.symm.toPartialMap.restrict W hW hWC).domainSource := by
      simp only [d, Category.assoc, PartialIso.domainOverIso_inv_target,
        PartialMap.restrictDomainHom_source]
    let Q := (R.fiber d).symm hFG (ht.symm ▸ hG c)
    exact hs ▸ ht ▸ Q

variable {W : T₁.left.Opens} {hW : Dense (W : Set T₁.left)} {hWC : W ≤ C.symm.toPartialMap.domain}
  {hFG : F.comp G = RationalMap.id X₀}
  {hG : ∀ c : CenterPoint (C.symm.toPartialMap.restrict W hW hWC),
    let M := P₁ (c ≫ (C.symm.toPartialMap.restrict W hW hWC).domainSource)
    M.evaluation.fromFunctionField (IsLocalRing.closedPoint M.surface.functionField) ∈ G.domain}

@[simp]
theorem symmOn_picard :
    (R.symmOn hFG W hW hWC hG).picard = R.picard.symm := (rfl)

@[simp]
theorem symmOn_boundaryAction :
    (R.symmOn hFG W hW hWC hG).boundaryAction = R.boundaryAction⁻¹ := (rfl)

omit [IsIntegral X₀] [Nonempty T₀.left] [Smooth T₀.hom] [Nonempty T₁.left] [Smooth T₁.hom]
  [G.IsDominant] in
private theorem fiberIso_heq_of_center_eq
    {c c' : Point T₁} {d d' : Point T₀} (hd : d = d') (hc : c = c')
    {I : B₀.IsometryEquiv B₁} {g : DihedralGroup n}
    (r : FiberRealization (P₁ c) (P₀ d) G I g) :
    HEq (hd ▸ hc ▸ r : FiberRealization (P₁ c') (P₀ d') G I g).iso r.iso := by
  subst c'
  subst d'
  rfl

/-- At an inverse center, the pair isomorphism is the inverse of the forward
fiber isomorphism at the corresponding center. -/
theorem symmOn_fiber_iso (c : CenterPoint (C.symm.toPartialMap.restrict W hW hWC)) :
    HEq ((R.symmOn hFG W hW hWC hG).fiber c).iso
      (R.fiber ((c ≫ C.symm.toPartialMap.restrictDomainHom W hW hWC) ≫
        C.domainOverIso.inv)).iso.symm := by
  simp only [symmOn]
  refine (fiberIso_heq_of_center_eq _ _ _).trans ?_
  exact heq_of_eq (FiberRealization.symm_iso ..)

/-- A dominant regular evaluation on an open family of target charts guarantees
an inverse on a dense target center open. The charts may be chosen separately on
the surfaces, as long as their evaluations are the restrictions of the total map. -/
theorem exists_symm_of_family_evaluation [PreirreducibleSpace T₁.left]
    (hFG : F.comp G = RationalMap.id X₀)
    {V : Scheme.{u}} (π : V ⟶ T₁.left) (hπ : IsOpenMap π) (e : V ⟶ X₁) [IsDominant e]
    (hV : ∀ c : Point T₁, IsIntegral (pullback π c.left))
    (j : ∀ c : Point T₁, pullback π c.left ⟶ (P₁ c).surface)
    (hj : ∀ c : Point T₁, IsDominant (j c))
    (he : ∀ c : Point T₁, letI := hV c; letI := hj c
      (j c).toRationalMap.comp (P₁ c).evaluation = (pullback.fst π c.left ≫ e).toRationalMap) :
    ∃ (W : T₁.left.Opens) (hW : Dense (W : Set T₁.left)) (hWC : W ≤ C.symm.toPartialMap.domain)
      (R' : GeometricRealization P₁ P₀ (C.symm.toPartialMap.restrict W hW hWC) G),
      R'.picard = R.picard.symm ∧ R'.boundaryAction = R.boundaryAction⁻¹ := by
  obtain ⟨U, hU, hgood⟩ :=
    π.exists_dense_open_for_rational_evaluation hπ e G.domain G.dense_domain.nonempty
  let W := U ⊓ C.target
  have hW : Dense (W : Set T₁.left) :=
    hU.inter_of_isOpen_right C.dense_target C.target.isOpen
  have hWC : W ≤ C.symm.toPartialMap.domain := inf_le_right
  refine ⟨W, hW, hWC, R.symmOn hFG W hW hWC ?_, rfl, rfl⟩
  intro c
  let D := C.symm.toPartialMap.restrict W hW hWC
  let p := c ≫ D.domainSource
  let x : S := default
  have hpW : p.left x ∈ W := by
    -- The center factors through the restricted inverse domain.
    have hp : p.left = c.left ≫ D.domain.ι := by
      simp only [p, Over.comp_left, PartialMap.domainSource_left]
    rw [hp, Hom.comp_apply]
    exact (c.left x).property
  let := hV p
  let := hj p
  exact hgood p.left x hpW.1 (j p) (P₁ p).evaluation (he p)

end GeometricRealization
end QPainleve.SignedClusterModularGroup

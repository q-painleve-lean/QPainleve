/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IdealSheaf.Conductor.Modules
public import TauCeti.AlgebraicGeometry.LineBundle.Basic

import QPainleve.AlgebraicGeometry.Morphisms.Pullback.UnitLift

import TauCeti.AlgebraicGeometry.Modules.AffineRestriction
import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange

/-!
# Gluing lines across a conductor square

Trivial lines on the finite modification and the conductor subscheme can be
identified on their intersection by a unit. The fiber product of the two direct
images, with one restriction twisted by that unit, is a line bundle. This is
the rank-one case of module patching over a fiber product of rings (Stacks
Project, Tag 0D2J).
-/

public noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
open Scheme.Modules MonoidalCategory Opposite
open TauCeti.AlgebraicGeometry

namespace CategoryTheory.IsPullback

universe u

variable {P Y Z X : Scheme.{u}} {j : P ⟶ Y} {g : P ⟶ Z} {f : Y ⟶ X} {i : Z ⟶ X}

section Gluing

variable (h : IsPullback j g f i) (a : Γ(P, ⊤)ˣ)

local notation "F" => Functor.obj (pushforward f) (𝟙_ (Scheme.Modules Y))
local notation "G" => Functor.obj (pushforward i) (𝟙_ (Scheme.Modules Z))
local notation "H" => Functor.obj (pushforward (j ≫ f)) (𝟙_ (Scheme.Modules P))

private def leftRestriction (j : P ⟶ Y) (f : Y ⟶ X) :
    (pushforward f).obj (𝟙_ Y.Modules) ⟶ (pushforward (j ≫ f)).obj (𝟙_ P.Modules) :=
  (Scheme.Hom.pushforwardStructureAlgebraMap j (rfl : j ≫ f = j ≫ f)).hom.hom

private def rightRestriction : G ⟶ H :=
  (Scheme.Hom.pushforwardStructureAlgebraMap g h.w.symm).hom.hom

local notation "r" => leftRestriction j f
local notation "s" => rightRestriction h

private def twistedRestriction : G ⟶ H :=
  s ≫ (pushforward (j ≫ f)).map (globalSectionsSmul (𝟙_ P.Modules) (a : Γ(P, ⊤)))

local notation "t" => twistedRestriction h a

private def gluedLine : X.Modules := Limits.pullback r t

private def gluedLineLeft : gluedLine h a ⟶ F := Limits.pullback.fst r t

private def gluedLineRight : gluedLine h a ⟶ G := Limits.pullback.snd r t

private theorem gluedLine_condition :
    gluedLineLeft h a ≫ r = gluedLineRight h a ≫ t :=
  Limits.pullback.condition

private theorem sections_pullback (U : X.Opens) :
    IsPullback
      (C := Type u)
      (↾fun x ↦ (gluedLineLeft h a).app U x)
      (↾fun x ↦ (gluedLineRight h a).app U x)
      (↾fun x ↦ (r).app U x) (↾fun x ↦ (t).app U x) := by
  let E := (evaluation (Opens X)ᵒᵖ Ab).obj (Opposite.op U)
  exact (((IsPullback.of_hasPullback r t).map (Scheme.Modules.toPresheaf X)).map E).map (forget Ab)

private theorem sections_conductor [IsFinite f] [IsSchemeTheoreticallyDominant f]
    [IsClosedImmersion i] (hi : i.ker = f.conductor) (U : X.Opens) :
    IsPullback (C := Type u)
      (↾fun x ↦ f.app U x) (↾fun x ↦ i.app U x)
      (↾fun x ↦ (r).app U x) (↾fun x ↦ (s).app U x) := by
  let E := (evaluation (Opens X)ᵒᵖ Ab).obj (Opposite.op U)
  let Φ := Scheme.Modules.toPresheaf X
  have hp := (((h.isPullback_structureModules_of_ker_eq_conductor hi).map Φ).map E).map
    (forget Ab)
  have unitMap {W : Scheme.{u}} (q : W ⟶ X) :
      (forget Ab).map (E.map (Φ.map (MonObj.one (X := q.pushforwardStructureAlgebra.toMon.X)))) =
        (↾fun x ↦ q.app U x : (Γ(X, U) : Type u) ⟶ (Γ(W, q ⁻¹ᵁ U) : Type u)) :=
    congrArg (fun k : 𝟙_ X.Modules ⟶ (pushforward q).obj (𝟙_ W.Modules) ↦
      (forget Ab).map (E.map (Φ.map k))) (Scheme.Hom.pushforwardStructureAlgebra_one q)
  rw [unitMap f, unitMap i] at hp
  exact hp

private theorem app_left (U : X.Opens) (b : Γ(Y, f ⁻¹ᵁ U)) :
    (r).app U b = j.app (f ⁻¹ᵁ U) b := by
  let c := Scheme.Hom.pushforwardStructureAlgebraMap j (rfl : j ≫ f = j ≫ f)
  have hb := Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply j
    (rfl : j ≫ f = j ≫ f) U b
  have he : CommMon.sectionsAlgHom c U b =
      j.appLE (f ⁻¹ᵁ U) ((j ≫ f) ⁻¹ᵁ U) le_rfl b :=
    hb.trans ((Scheme.Hom.pushforwardStructureAlgebraSectionsRingEquiv_symm_apply
      (j ≫ f) U _).trans (congrArg
        (fun d ↦ j.appLE (f ⁻¹ᵁ U) ((j ≫ f) ⁻¹ᵁ U) le_rfl d)
        (Scheme.Hom.pushforwardStructureAlgebraSectionsRingEquiv_apply f U b)))
  exact (CommMon.sectionsAlgHom_apply c U b).symm.trans
    (he.trans (ConcreteCategory.congr_hom (Scheme.Hom.appLE_eq_app j) b))

private def rightApp (U : X.Opens) (b : Γ(Z, i ⁻¹ᵁ U)) : Γ(P, (j ≫ f) ⁻¹ᵁ U) :=
  (s).app U b

private theorem rightApp_one (U : X.Opens) :
    rightApp h U 1 = 1 := by
  let c := Scheme.Hom.pushforwardStructureAlgebraMap g h.w.symm
  have he := Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply g h.w.symm U
    (i.pushforwardStructureAlgebraSectionsRingEquiv U |>.symm 1)
  refine (congrArg (rightApp h U)
    (i.pushforwardStructureAlgebraSectionsRingEquiv_symm_apply U 1).symm).trans ?_
  refine (CommMon.sectionsAlgHom_apply c U _).symm.trans (he.trans ?_)
  exact ((j ≫ f).pushforwardStructureAlgebraSectionsRingEquiv_symm_apply U _).trans
    ((congrArg (fun d ↦ g.appLE (i ⁻¹ᵁ U) ((j ≫ f) ⁻¹ᵁ U)
        (by rw [h.w, Scheme.Hom.comp_preimage]) d)
        ((i.pushforwardStructureAlgebraSectionsRingEquiv U).apply_symm_apply 1)).trans
      (map_one (g.appLE (i ⁻¹ᵁ U) ((j ≫ f) ⁻¹ᵁ U)
        (by rw [h.w, Scheme.Hom.comp_preimage])).hom))

private theorem app_twist (U : X.Opens) (b : Γ(Z, i ⁻¹ᵁ U)) :
    (t).app U b = P.presheaf.map ((j ≫ f) ⁻¹ᵁ U).leTop.op (a : Γ(P, ⊤)) * rightApp h U b := by
  simp only [twistedRestriction, Hom.comp_app, pushforward_map_app,
    globalSectionsSmul_app]
  rfl

private theorem exists_gluedSection (U : X.Opens) (b : Γ(Y, f ⁻¹ᵁ U))
    (hb : j.app (f ⁻¹ᵁ U) b =
      P.presheaf.map (j ⁻¹ᵁ (f ⁻¹ᵁ U)).leTop.op (a : Γ(P, ⊤))) :
    ∃ m : Γ(gluedLine h a, U),
      (gluedLineLeft h a).app U m = b ∧ (gluedLineRight h a).app U m = (1 : Γ(Z, i ⁻¹ᵁ U)) := by
  apply Types.exists_of_isPullback (sections_pullback h a U) b (1 : Γ(Z, i ⁻¹ᵁ U))
  have ht := app_twist h a U 1
  rw [rightApp_one, mul_one] at ht
  exact (app_left U b).trans (hb.trans ht.symm)

private theorem gluedLine_section_relation (U : X.Opens) (z : Γ(gluedLine h a, U)) :
    j.app (f ⁻¹ᵁ U) ((gluedLineLeft h a).app U z) =
      P.presheaf.map ((j ≫ f) ⁻¹ᵁ U).leTop.op (a : Γ(P, ⊤)) *
        rightApp h U ((gluedLineRight h a).app U z) := by
  have he : (r).app U ((gluedLineLeft h a).app U z) =
      (t).app U ((gluedLineRight h a).app U z) :=
    ConcreteCategory.congr_hom (sections_pullback h a U).w z
  exact (app_left U ((gluedLineLeft h a).app U z)).symm.trans
    (he.trans (app_twist h a U ((gluedLineRight h a).app U z)))

variable [IsFinite f] [IsSchemeTheoreticallyDominant f] [IsClosedImmersion i]
  (hi : i.ker = f.conductor)

include hi in
private theorem bijective_smul_gluedSection (U : X.Opens) (b : Γ(Y, f ⁻¹ᵁ U)ˣ)
    (m : Γ(gluedLine h a, U)) (hm₁ : (gluedLineLeft h a).app U m = (b : Γ(Y, f ⁻¹ᵁ U)))
    (hm₂ : (gluedLineRight h a).app U m = (1 : Γ(Z, i ⁻¹ᵁ U))) :
    Function.Bijective (fun c : Γ(X, U) ↦ c • m) := by
  have hp := sections_pullback h a U
  have hc := sections_conductor h hi U
  have hleft (c : Γ(X, U)) :
      (gluedLineLeft h a).app U (c • m) = f.app U c * (b : Γ(Y, f ⁻¹ᵁ U)) := by
    rw [Hom.app_smul, hm₁]
    rfl
  have hright (c : Γ(X, U)) :
      (gluedLineRight h a).app U (c • m) = i.app U c := by
    exact (Hom.app_smul (gluedLineRight h a) c m).trans
      ((congrArg (c • ·) hm₂).trans (mul_one (i.app U c)))
  constructor
  · intro x y hxy
    apply Types.ext_of_isPullback hc
    · exact b.isUnit.mul_right_cancel ((hleft x).symm.trans ((congrArg _ hxy).trans (hleft y)))
    · exact (hright x).symm.trans ((congrArg _ hxy).trans (hright y))
  · intro z
    -- Divide the left component by the lifted unit to recover a pair in the untwisted square.
    let y : Γ(Y, f ⁻¹ᵁ U) := (gluedLineLeft h a).app U z
    let w : Γ(Z, i ⁻¹ᵁ U) := (gluedLineRight h a).app U z
    let jU : Γ(Y, f ⁻¹ᵁ U) →+* Γ(P, (j ≫ f) ⁻¹ᵁ U) := (j.app (f ⁻¹ᵁ U)).hom
    let aU : Γ(P, (j ≫ f) ⁻¹ᵁ U) :=
      P.presheaf.map ((j ≫ f) ⁻¹ᵁ U).leTop.op (a : Γ(P, ⊤))
    have hb : jU (b : Γ(Y, f ⁻¹ᵁ U)) = aU := by
      have eq := gluedLine_section_relation h a U m
      exact (congrArg jU hm₁).symm.trans
        (eq.trans ((congrArg (fun d ↦ aU * rightApp h U d) hm₂).trans
          (by rw [rightApp_one, mul_one])))
    have hcanc : jU (y * ↑b⁻¹) = rightApp h U w := by
      calc
        jU (y * ↑b⁻¹) = jU y * jU (↑b⁻¹ : Γ(Y, f ⁻¹ᵁ U)) := jU.map_mul _ _
        _ = rightApp h U w * (jU ↑b * jU (↑b⁻¹ : Γ(Y, f ⁻¹ᵁ U))) := by
          have hy : jU y = aU * rightApp h U w := gluedLine_section_relation h a U z
          rw [hy, ← hb, mul_comm (jU ↑b), mul_assoc]
        _ = _ := by rw [← jU.map_mul, Units.mul_inv, jU.map_one, mul_one]
    let y' : Γ(Y, f ⁻¹ᵁ U) := y * ↑b⁻¹
    have hmatch : (r).app U y' = (s).app U w := (app_left U y').trans hcanc
    obtain ⟨c, hc₁, hc₂⟩ := Types.exists_of_isPullback hc y' w hmatch
    refine ⟨c, Types.ext_of_isPullback hp ?_ ?_⟩
    · -- Evaluate the left projection of the pullback as a section on the finite source.
      change (gluedLineLeft h a).app U (c • m) = y
      rw [hleft]
      have hc₁' : f.app U c = y * ↑b⁻¹ := hc₁
      rw [hc₁', mul_assoc, Units.inv_mul, mul_one]
    · exact (hright c).trans hc₂

include hi in
private theorem isInvertible_gluedLine :
    SheafOfModules.isInvertible X (gluedLine h a) := by
  classical
  choose U hx b hb using h.exists_affineOpen_unit_lift a
  choose m hm₁ hm₂ using fun x ↦ exists_gluedSection h a (U x).val (b x) (hb x)
  apply SheafOfModules.isInvertible_iff_exists_isOpenCover.mpr
  refine ⟨X, fun x ↦ (U x).val, ?_, fun x ↦ ?_⟩
  · exact IsOpenCover.mk (top_unique fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩)
  let V := (U x).val
  let M := gluedLine h a
  let p := (M.over V).unitHomEquiv.symm ((M.overSectionsEquiv V).symm (m x))
  have hp : IsIso p := by
    apply TauCeti.SheafOfModules.isIso_unitHomEquiv_symm
    intro W
    induction W using Opposite.rec with | op W => ?_
    erw [SheafOfModules.overSectionsEquiv_symm_apply_eval]
    let b' := Units.map (Y.presheaf.map ((Opens.map f.base).map W.hom).op).hom.toMonoidHom (b x)
    apply bijective_smul_gluedSection h a hi W.left b'
    · have he := (gluedLineLeft h a).mapPresheaf.naturality_apply W.hom.op (m x)
      exact he.trans (congrArg
        (fun c : Γ(Y, f ⁻¹ᵁ V) ↦ Y.presheaf.map ((Opens.map f.base).map W.hom).op c) (hm₁ x))
    · have he := (gluedLineRight h a).mapPresheaf.naturality_apply W.hom.op (m x)
      exact he.trans ((congrArg
        (fun c : Γ(Z, i ⁻¹ᵁ V) ↦ Z.presheaf.map ((Opens.map i.base).map W.hom).op c)
          (hm₂ x)).trans
          (map_one (Z.presheaf.map ((Opens.map i.base).map W.hom).op).hom))
  exact ⟨TauCeti.SheafOfModules.LocalTrivializations.unitIsoRestrict
    (TauCeti.SheafOfModules.freePUnitIsoUnit (X.ringCatSheaf.over V) ≪≫ asIso p)⟩

include hi in
private theorem isIso_of_unit_on_gluedSections {T : Scheme.{u}} (q : T ⟶ X) [IsAffineHom q]
    (φ : (Scheme.Modules.pullback q).obj (gluedLine h a) ⟶ 𝟙_ T.Modules)
    (hφ : ∀ (U : X.affineOpens) (b : Γ(Y, f ⁻¹ᵁ U.val)ˣ)
      (m : Γ(gluedLine h a, U.val)),
      (gluedLineLeft h a).app U.val m = (b : Γ(Y, f ⁻¹ᵁ U.val)) →
      (gluedLineRight h a).app U.val m = (1 : Γ(Z, i ⁻¹ᵁ U.val)) →
      IsUnit (M := Γ(T, q ⁻¹ᵁ U.val))
        (((pullbackPushforwardAdjunction q).homEquiv _ _ φ).app U.val m)) : IsIso φ := by
  classical
  let := isInvertible_gluedLine h a hi
  choose U hx b hb using h.exists_affineOpen_unit_lift a
  choose m hm₁ hm₂ using fun x ↦ exists_gluedSection h a (U x).val (b x) (hb x)
  apply φ.isIso_of_bijective_app (U := fun x ↦ q ⁻¹ᵁ (U x).val)
    (fun x ↦ (U x).property.preimage q)
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨q y, hx (q y)⟩
  · intro x
    let V := (U x).val
    let M := gluedLine h a
    have hgen : Submodule.span Γ(X, V) {m x} = ⊤ := by
      apply eq_top_iff.mpr
      intro y _
      exact Submodule.mem_span_singleton.mpr
        ((bijective_smul_gluedSection h a hi V (b x) (m x) (hm₁ x) (hm₂ x)).surjective y)
    have hspan := q.span_singleton_pullbackSections_eq_top M (U x).property
      ((U x).property.preimage q) hgen
    let p := q.pullbackSections M V (m x)
    let value : Γ(T, q ⁻¹ᵁ V) := φ.app (q ⁻¹ᵁ V) p
    have hp : IsUnit value := by
      dsimp only [value]
      rw [← pullbackPushforwardAdjunction_homEquiv_app_apply]
      exact hφ (U x) (b x) (m x) (hm₁ x) (hm₂ x)
    have hex (y : Γ((Scheme.Modules.pullback q).obj M, q ⁻¹ᵁ V)) :
        ∃ c : Γ(T, q ⁻¹ᵁ V), c • p = y :=
      Submodule.mem_span_singleton.mp (hspan.ge (Submodule.mem_top (x := y)))
    constructor
    · intro y z hyz
      obtain ⟨c, rfl⟩ := hex y
      obtain ⟨d, rfl⟩ := hex z
      simp only [Hom.app_smul] at hyz
      have he : c * value = d * value := hyz
      exact congrArg (· • p) (hp.mul_right_cancel he)
    · intro y
      obtain ⟨u, hu⟩ := hp
      let y₀ : Γ(T, q ⁻¹ᵁ V) := y
      let c := y₀ * ↑u⁻¹
      refine ⟨c • p, (Hom.app_smul φ c p).trans ?_⟩
      have hc : c * (↑u : Γ(T, q ⁻¹ᵁ V)) = y₀ := by
        dsimp only [c]
        rw [mul_assoc, Units.inv_mul, mul_one]
      exact (congrArg (fun d : Γ(T, q ⁻¹ᵁ V) ↦ c * d) hu.symm).trans hc

include hi in
/-- A unit on the intersection of a conductor square glues the two trivial line bundles.
The resulting line bundle has trivializations on the finite source and conductor subscheme.
On the intersection the source trivialization equals the conductor trivialization followed
by multiplication by the prescribed unit. -/
theorem exists_glued_line_of_conductor_square :
    ∃ (L : InvertibleSheaf X)
      (e : (Scheme.Modules.pullback f).obj L.obj ≅ 𝟙_ Y.Modules)
      (d : (Scheme.Modules.pullback i).obj L.obj ≅ 𝟙_ Z.Modules),
      (pullbackComp j f).inv.app L.obj ≫ (Scheme.Modules.pullback j).map e.hom ≫
        (pullbackObjUnitIso j).hom =
      (pullbackCongr h.w.symm).inv.app L.obj ≫ (pullbackComp g i).inv.app L.obj ≫
        (Scheme.Modules.pullback g).map d.hom ≫ (pullbackObjUnitIso g).hom ≫
          globalSectionsSmul (𝟙_ P.Modules) (a : Γ(P, ⊤)) := by
  let M := gluedLine h a
  let L : InvertibleSheaf X := ⟨M, isInvertible_gluedLine h a hi⟩
  let ef := (pullbackPushforwardAdjunction f).homEquiv M (𝟙_ Y.Modules)
  let ei := (pullbackPushforwardAdjunction i).homEquiv M (𝟙_ Z.Modules)
  let α := ef.symm (gluedLineLeft h a)
  let β := ei.symm (gluedLineRight h a)
  have hα : IsIso α := isIso_of_unit_on_gluedSections h a hi f α fun U b m hm _ ↦ by
    have he := ConcreteCategory.congr_hom (congrArg (Hom.app · U.val)
      (ef.apply_symm_apply (gluedLineLeft h a))) m
    exact (he.trans hm) ▸ b.isUnit
  have hβ : IsIso β := isIso_of_unit_on_gluedSections h a hi i β fun U _ m _ hm ↦ by
    have he := ConcreteCategory.congr_hom (congrArg (Hom.app · U.val)
      (ei.apply_symm_apply (gluedLineRight h a))) m
    exact (he.trans hm) ▸ isUnit_one
  refine ⟨L, asIso α, asIso β, ?_⟩
  let E := (pullbackPushforwardAdjunction (j ≫ f)).homEquiv M (𝟙_ P.Modules)
  apply E.injective
  have hj := Scheme.Hom.pullbackPushforwardAdjunction_homEquiv_pullback_map j
    (rfl : j ≫ f = j ≫ f) M α
  have hg := Scheme.Hom.pullbackPushforwardAdjunction_homEquiv_pullback_map g h.w.symm M β
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app, Category.id_comp] at hj
  -- Under adjunction, compatibility is the defining equation of the module pullback.
  let v := (pullbackCongr h.w.symm).inv.app M ≫ (pullbackComp g i).inv.app M ≫
    (Scheme.Modules.pullback g).map β ≫ (pullbackObjUnitIso g).hom
  let u := globalSectionsSmul (𝟙_ P.Modules) (a : Γ(P, ⊤))
  refine hj.trans ((congrArg (· ≫ r) (ef.apply_symm_apply (gluedLineLeft h a))).trans ?_)
  have hv : E (v ≫ u) = gluedLineRight h a ≫ t :=
    (Adjunction.homEquiv_naturality_right _ _ _).trans
      ((congrArg (· ≫ _) (hg.trans (congrArg (· ≫ s)
        (ei.apply_symm_apply (gluedLineRight h a))))).trans (Category.assoc _ _ _))
  exact (gluedLine_condition h a).trans (hv.symm.trans
    (congrArg E (by dsimp only [v, u, L]; simp only [Category.assoc, asIso_hom])))

end Gluing

end CategoryTheory.IsPullback

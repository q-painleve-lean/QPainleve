/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import TauCeti.AlgebraicGeometry.IdealSheaf.Image
public import TauCeti.AlgebraicGeometry.Modules.Dual
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
public import TauCeti.AlgebraicGeometry.Modules.Sections
public import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Basic
import QPainleve.AlgebraicGeometry.IdealSheaf.Image.Pullback
import QPainleve.AlgebraicGeometry.Modules.Pullback.Sections
import TauCeti.AlgebraicGeometry.Modules.Pullback.InternalHom.Coherence
import TauCeti.AlgebraicGeometry.VectorBundle.InternalHom.Pullback

/-!
# Pullback and point evaluation of zero loci of sections

The image ideal of evaluation at a section of a finite locally free sheaf defines its
scheme-theoretic zero locus. It commutes with pullback, including to the spectrum of
the residue field of a point, where the ideal detects whether the section evaluates to zero.
The comparison uses Tau Ceti's evaluation formula for the internal Hom under base change.

See [The Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0) for the
zero divisor of a regular section of an invertible sheaf.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonoidalClosed TopologicalSpace

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

universe u

-- Give the internal-Hom dual the quasicoherence of the bundled dual, and transport
-- the bundle instances to the unbundled sheaf used by the section pullback.
local instance {Y : Scheme.{u}} (E : FiniteLocallyFreeSheaf Y) :
    ((ihom E.obj).obj (𝟙_ Y.Modules)).IsQuasicoherent :=
  dual_obj E ▸ ((toQuasicoherent Y).obj (dual E)).property

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (E : FiniteLocallyFreeSheaf Y) :
    ((Scheme.Modules.pullback f).obj E.obj).IsLocallyFree :=
  Scheme.Modules.isLocallyFree_pullback f E.obj

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (E : FiniteLocallyFreeSheaf Y) :
    ((Scheme.Modules.pullback f).obj E.obj).IsFiniteType := by
  rw [← pullback_obj_obj f E]
  infer_instance

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (E : FiniteLocallyFreeSheaf Y) :
    ((ihom ((Scheme.Modules.pullback f).obj E.obj)).obj (𝟙_ X.Modules)).IsQuasicoherent := by
  rw [← pullback_obj_obj f E]
  infer_instance

variable {X Y : Scheme.{u}} (E : FiniteLocallyFreeSheaf Y)

/-- Evaluation at a pulled-back section has the pullback of its original image ideal. -/
theorem imageIdealSheaf_evaluation_pullback (s : 𝟙_ Y.Modules ⟶ E.obj) (f : X ⟶ Y) :
    (Scheme.Modules.Hom.imageIdealSheaf
      ((Scheme.Modules.dualHomUnitEquiv ((Scheme.Modules.pullback f).obj E.obj)).symm
        ((Scheme.Modules.pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s))) =
      (((Scheme.Modules.dualHomUnitEquiv E.obj).symm s).imageIdealSheaf).comap f := by
  let P := Scheme.Modules.pullback f
  let u := Scheme.Modules.pullbackObjUnitIso f
  let α : P.obj ((ihom E.obj).obj (𝟙_ Y.Modules)) ⟶
      (ihom (P.obj E.obj)).obj (P.obj (𝟙_ Y.Modules)) :=
    (pullbackIhomComparison E.obj f).app (𝟙_ Y.Modules)
  have : IsIso α := inferInstanceAs
    (IsIso ((pullbackIhomComparison E.obj f).app (𝟙_ Y.Modules)))
  let e := asIso α ≪≫ (ihom (P.obj E.obj)).mapIso u
  let s' := u.inv ≫ P.map s
  let φ := (Scheme.Modules.dualHomUnitEquiv E.obj).symm s
  let φ' := (Scheme.Modules.dualHomUnitEquiv (P.obj E.obj)).symm s'
  have he : P.map φ ≫ u.hom = e.hom ≫ φ' := by
    simpa only [φ, φ', e, α, s', P, u, Scheme.Modules.dualHomUnitEquiv_symm_apply,
      Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Category.assoc] using
      f.pullback_map_evaluation_comp_pullbackObjUnitIso_hom E.obj s
  have : (P.obj ((ihom E.obj).obj (𝟙_ Y.Modules))).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pullback f ((ihom E.obj).obj (𝟙_ Y.Modules))
  have hbase : (P.map φ ≫ u.hom).imageIdealSheaf = φ.imageIdealSheaf.comap f :=
    φ.imageIdealSheaf_pullback f
  rw [he, Scheme.Modules.Hom.imageIdealSheaf_comp_iso] at hbase
  exact hbase

/-- The ideal of zeros commutes with pullback of global sections. -/
theorem imageIdealSheaf_evaluation_pullback_section (s : Γ(E.obj, ⊤)) (f : X ⟶ Y) :
    let E' := (Scheme.Modules.pullback f).obj E.obj
    ((Scheme.Modules.dualHomUnitEquiv E').symm
      ((Scheme.Modules.unitHomEquivTop E').symm (f.pullbackSections E.obj ⊤ s))).imageIdealSheaf =
      (((Scheme.Modules.dualHomUnitEquiv E.obj).symm
        ((Scheme.Modules.unitHomEquivTop E.obj).symm s)).imageIdealSheaf).comap f := by
  let t : 𝟙_ Y.Modules ⟶ E.obj := (Scheme.Modules.unitHomEquivTop E.obj).symm s
  let eval := fun t' : 𝟙_ X.Modules ⟶ (Scheme.Modules.pullback f).obj E.obj ↦
    ((Scheme.Modules.dualHomUnitEquiv _).symm t').imageIdealSheaf
  exact (congrArg eval (f.unitHomEquivTop_symm_pullbackSections s)).trans
    (E.imageIdealSheaf_evaluation_pullback t f)

/-- A point lies in the zero locus of a section exactly when the section pulled back to
its residue field is zero. -/
theorem mem_support_imageIdealSheaf_evaluation_iff (s : 𝟙_ Y.Modules ⟶ E.obj) (y : Y) :
    y ∈ (((Scheme.Modules.dualHomUnitEquiv E.obj).symm s).imageIdealSheaf.support : Set Y) ↔
      (Scheme.Modules.pullbackObjUnitIso (Y.fromSpecResidueField y)).inv ≫
        (Scheme.Modules.pullback (Y.fromSpecResidueField y)).map s = 0 := by
  let f := Y.fromSpecResidueField y
  let I := ((Scheme.Modules.dualHomUnitEquiv E.obj).symm s).imageIdealSheaf
  have ht : y ∈ (I.support : Set Y) ↔ (I.comap f).support = ⊤ := by
    rw [Scheme.IdealSheafData.support_comap, ← top_le_iff, IsConcreteLE.le_iff]
    simp only [← SetLike.mem_coe, Closeds.coe_top, Set.mem_univ, true_implies,
      Closeds.coe_preimage, Set.mem_preimage,
      f, Scheme.fromSpecResidueField_apply]
    exact ⟨fun hy _ ↦ hy, fun h ↦ @h default⟩
  rw [ht, Scheme.IdealSheafData.support_eq_top_iff,
    ← E.imageIdealSheaf_evaluation_pullback s f,
    Scheme.Modules.Hom.imageIdealSheaf_eq_bot_iff, Equiv.symm_apply_eq,
    Scheme.Modules.dualHomUnitEquiv_zero]

/-- The zero locus of a section is detected by its value in the residue-field fiber,
expressed using the section pullback on global sections. -/
theorem mem_support_imageIdealSheaf_evaluation_section_iff (s : Γ(E.obj, ⊤)) (y : Y) :
    y ∈ (((Scheme.Modules.dualHomUnitEquiv E.obj).symm
        ((Scheme.Modules.unitHomEquivTop E.obj).symm s)).imageIdealSheaf.support : Set Y) ↔
      (Y.fromSpecResidueField y).pullbackSections E.obj ⊤ s = 0 := by
  let t : 𝟙_ Y.Modules ⟶ E.obj := (Scheme.Modules.unitHomEquivTop E.obj).symm s
  let f := Y.fromSpecResidueField y
  let F := Scheme.Modules.unitHomEquivTop ((Scheme.Modules.pullback f).obj E.obj)
  have h₀ : F (0 : 𝟙_ (Spec (Y.residueField y)).Modules ⟶
      (Scheme.Modules.pullback f).obj E.obj) = 0 :=
    Scheme.Modules.unitHomEquivTop_zero _
  have h₁ : F ((Scheme.Modules.pullbackObjUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map t) = f.pullbackSections E.obj ⊤ s :=
    (f.unitHomEquivTop_pullback t).trans <|
      congrArg (f.pullbackSections E.obj ⊤)
        ((Scheme.Modules.unitHomEquivTop E.obj).apply_symm_apply s)
  exact (E.mem_support_imageIdealSheaf_evaluation_iff t y).trans
    (F.apply_eq_iff_eq.symm.trans (Iff.of_eq (congrArg₂ Eq h₁ h₀)))

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Modules.ExteriorPower.Sections
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Sections
public import TauCeti.AlgebraicGeometry.VectorBundle.FixedRank
import QPainleve.AlgebraicGeometry.Modules.Hom
import QPainleve.AlgebraicGeometry.VectorBundle.Affine
import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.WeakSerre
import TauCeti.AlgebraicGeometry.Modules.Sheaf
import TauCeti.AlgebraicGeometry.Modules.Tensor.AffineSections
import TauCeti.AlgebraicGeometry.VectorBundle.ExteriorPower.Basic
import TauCeti.Data.Fin.Tuple.Basic
import TauCeti.LinearAlgebra.ExteriorPower.FreeShortExact

/-!
# Determinants of short exact sequences of vector bundles

For an exact sequence `0 → E → M → G → 0` whose end terms have constant ranks `n` and `r`,
the top exterior powers satisfy `⋀ⁿ E ⊗ ⋀ʳ G ≅ ⋀ⁿ⁺ʳ M`. The comparison sends the wedge of
subbundle sections and the wedge of quotient sections to the wedge of the images of the
subbundle sections followed by lifts of the quotient sections. This order fixes the sign
used in the determinant of the conormal sequence.

The local computation uses `TauCeti.exteriorPower.shortExactEquivOfBasis`. The wedge formula
on sections makes the local isomorphisms compatible with restriction.
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules CategoryTheory Limits MonoidalCategory
  Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank

variable {X : Scheme.{u}} {n r : ℕ}
  (E : FixedRank X n) (G : FixedRank X r)
  {M : X.Modules} (f : E.obj.obj ⟶ M) (g : M ⟶ G.obj.obj) {hz : f ≫ g = 0}
  (h : (ShortComplex.mk f g hz).ShortExact)

local notation "D[" d "," A "]" =>
  (Functor.obj (_root_.SheafOfModules.exteriorPower X.sheaf d) A : X.Modules)
local notation "DE" => D[n,E.obj.obj]
local notation "DG" => D[r,G.obj.obj]
local notation "DM" => D[n+r,M]

private abbrev FrameOpens :=
  {U : X.Opens // IsAffineOpen U ∧
    Nonempty (Module.Basis (Fin n) Γ(X, U) Γ(E.obj.obj, U)) ∧
    Nonempty (Module.Basis (Fin r) Γ(X, U) Γ(G.obj.obj, U))}

private lemma isBasis_frameOpens :
    Opens.IsBasis (Set.range (Subtype.val : FrameOpens E G → X.Opens)) := by
  refine Opens.isBasis_iff_nbhd.mpr fun {W x} hx ↦ ?_
  let ranks : Bool → ℕ := fun i ↦ if i then n else r
  let F : (i : Bool) → FixedRank X (ranks i)
    | true => E
    | false => G
  obtain ⟨U, hU, hxU, hUW, b⟩ := exists_isAffineOpen_basis_sections_family_le F hx
  obtain ⟨bE⟩ := b true
  obtain ⟨bG⟩ := b false
  exact ⟨U, ⟨⟨U, hU, ⟨bE.reindex Equiv.ulift⟩, ⟨bG.reindex Equiv.ulift⟩⟩, rfl⟩, hxU, hUW⟩

private def wedgeSection {A : X.Modules} {U : X.Opens} {d : ℕ} (v : Fin d → Γ(A, U)) :
    Γ(D[d,A], U) :=
  A.exteriorPowerSections U d (ModuleCat.exteriorPower.mk v)

private def tensorWedge {U : X.Opens} (v : Fin n → Γ(E.obj.obj, U))
    (w : Fin r → Γ(G.obj.obj, U)) : Γ(DE ⊗ DG, U) :=
  tmulRight DE (wedgeSection w) (wedgeSection v)

private lemma map_wedgeSection {A : X.Modules} {U V : X.Opens} (j : V ⟶ U)
    {d : ℕ} (v : Fin d → Γ(A, U)) :
    D[d,A].presheaf.map j.op (wedgeSection v) = wedgeSection (A.presheaf.map j.op ∘ v) :=
  A.restrict_exteriorPowerSections_mk j d v

private lemma map_tensorWedge {U V : X.Opens} (j : V ⟶ U) (v : Fin n → Γ(E.obj.obj, U))
    (w : Fin r → Γ(G.obj.obj, U)) :
    (DE ⊗ DG).presheaf.map j.op (tensorWedge E G v w) =
      tensorWedge E G (E.obj.obj.presheaf.map j.op ∘ v) (G.obj.obj.presheaf.map j.op ∘ w) := by
  simp only [tensorWedge, map_tmulRight, map_wedgeSection]

private def exteriorSectionsEquiv (A : X.Modules) [A.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (d : ℕ) :
    (⋀[Γ(X, U)]^d Γ(A, U)) ≃ₗ[Γ(X, U)] Γ(D[d,A], U) :=
  LinearEquiv.ofBijective (A.exteriorPowerSections U d).hom (A.bijective_exteriorPowerSections hU d)

private lemma determinant_isQuasicoherent (A : FiniteLocallyFreeSheaf X) (d : ℕ) :
    D[d,A.obj].IsQuasicoherent :=
  FiniteLocallyFreeSheaf.exteriorPower_obj_obj d A ▸
    (inferInstance : ((FiniteLocallyFreeSheaf.exteriorPower X d).obj A).obj.IsQuasicoherent)

private def tensorWedgeEquiv {U : X.Opens} (hU : IsAffineOpen U) :
    ((⋀[Γ(X, U)]^n Γ(E.obj.obj, U)) ⊗[Γ(X, U)] (⋀[Γ(X, U)]^r Γ(G.obj.obj, U))) ≃ₗ[Γ(X, U)]
      Γ(DE ⊗ DG, U) := by
  have : (DE).IsQuasicoherent := determinant_isQuasicoherent E.obj n
  have : (DG).IsQuasicoherent := determinant_isQuasicoherent G.obj r
  exact (TensorProduct.congr (exteriorSectionsEquiv E.obj.obj hU n)
    (exteriorSectionsEquiv G.obj.obj hU r)).trans
    (LinearEquiv.ofBijective _ (bijective_μ_sectionsFunctor DE DG hU))

private lemma tensorWedgeEquiv_tmul {U : X.Opens} (hU : IsAffineOpen U)
    (v : Fin n → Γ(E.obj.obj, U)) (w : Fin r → Γ(G.obj.obj, U)) :
    tensorWedgeEquiv E G hU
        (ModuleCat.exteriorPower.mk v ⊗ₜ ModuleCat.exteriorPower.mk w) =
      tensorWedge E G v w := by
  rw [tensorWedge, tmulRight_apply]
  exact congrArg (Functor.LaxMonoidal.μ (sectionsFunctor U) DE DG).hom
    (TensorProduct.congr_tmul (exteriorSectionsEquiv E.obj.obj hU n)
      (exteriorSectionsEquiv G.obj.obj hU r)
      (ModuleCat.exteriorPower.mk v) (ModuleCat.exteriorPower.mk w))

include h in
private lemma middle_isQuasicoherent : M.IsQuasicoherent :=
  (isQuasicoherent X).prop_X₂_of_shortExact h inferInstance inferInstance

include h in
private lemma shortExact_sectionsFunctor {U : X.Opens} (hU : IsAffineOpen U) :
    ((ShortComplex.mk f g hz).map (sectionsFunctor U)).ShortExact := by
  have := h.mono_f
  have := h.epi_g
  have := middle_isQuasicoherent E G f g h
  exact
    { exact := h.exact.map_of_mono_of_preservesKernel (sectionsFunctor U)
        inferInstance inferInstance
      mono_f := inferInstanceAs (Mono ((sectionsFunctor U).map f))
      epi_g := (ModuleCat.epi_iff_surjective _).2
        (Hom.app_surjective_of_epi_of_isAffineOpen g U hU) }

private def determinantOfSectionBases (U : FrameOpens E G) :
    ((⋀[Γ(X, U.val)]^n Γ(E.obj.obj, U.val)) ⊗[Γ(X, U.val)]
      (⋀[Γ(X, U.val)]^r Γ(G.obj.obj, U.val))) ≃ₗ[Γ(X, U.val)]
      ⋀[Γ(X, U.val)]^(n + r) Γ(M, U.val) := by
  have hs := shortExact_sectionsFunctor E G f g h U.property.1
  exact TauCeti.exteriorPower.shortExactEquivOfBasis
    hs.moduleCat_injective_f ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      hs.exact) hs.moduleCat_surjective_g
    U.property.2.1.some U.property.2.2.some

private def determinantOnFrame (U : FrameOpens E G) :
    Γ(DE ⊗ DG, U.val) ≃ₗ[Γ(X, U.val)] Γ(DM, U.val) := by
  haveI := middle_isQuasicoherent E G f g h
  exact (tensorWedgeEquiv E G U.property.1).symm.trans
    ((determinantOfSectionBases E G f g h U).trans (exteriorSectionsEquiv M U.property.1 _))

private lemma determinantOfSectionBases_apply (U : FrameOpens E G)
    (v : Fin n → Γ(E.obj.obj, U.val)) (z : Fin r → Γ(M, U.val)) :
    determinantOfSectionBases E G f g h U
        (exteriorPower.ιMulti Γ(X, U.val) n v ⊗ₜ
          exteriorPower.ιMulti Γ(X, U.val) r (g.app U.val ∘ z)) =
      exteriorPower.ιMulti Γ(X, U.val) (n + r) (Fin.append (f.app U.val ∘ v) z) := by
  have hs := shortExact_sectionsFunctor E G f g h U.property.1
  exact TauCeti.exteriorPower.shortExactEquivOfBasis_tmul_ιMulti
    hs.moduleCat_injective_f ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      hs.exact) hs.moduleCat_surjective_g U.property.2.1.some U.property.2.2.some v z

private lemma determinantOnFrame_apply (U : FrameOpens E G)
    (v : Fin n → Γ(E.obj.obj, U.val)) (z : Fin r → Γ(M, U.val)) :
    determinantOnFrame E G f g h U (tensorWedge E G v (g.app U.val ∘ z)) =
      wedgeSection (Fin.append (f.app U.val ∘ v) z) := by
  rw [← tensorWedgeEquiv_tmul E G U.property.1]
  simp only [determinantOnFrame, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  have := middle_isQuasicoherent E G f g h
  exact congrArg (exteriorSectionsEquiv M U.property.1 (n + r))
    (determinantOfSectionBases_apply E G f g h U v z)

include h in
private lemma exists_smul_tensorWedge (U : FrameOpens E G) (s : Γ(DE ⊗ DG, U.val)) :
    ∃ (a : Γ(X, U.val)) (v : Fin n → Γ(E.obj.obj, U.val)) (z : Fin r → Γ(M, U.val)),
      s = a • tensorWedge E G v (g.app U.val ∘ z) := by
  let b := U.property.2.1.some
  let c := U.property.2.2.some
  let e := (TensorProduct.congr b.exteriorPowerTopEquiv c.exteriorPowerTopEquiv).trans
    (TensorProduct.lid Γ(X, U.val) Γ(X, U.val))
  have hgen : e (ModuleCat.exteriorPower.mk b ⊗ₜ ModuleCat.exteriorPower.mk c) = 1 := by
    have hw := TensorProduct.congr_tmul b.exteriorPowerTopEquiv c.exteriorPowerTopEquiv
      (exteriorPower.ιMulti _ _ b) (exteriorPower.ιMulti _ _ c)
    exact (congrArg (TensorProduct.lid Γ(X, U.val) Γ(X, U.val)) hw).trans
      (by simp [Module.Basis.det_self])
  have hg := (shortExact_sectionsFunctor E G f g h U.property.1).moduleCat_surjective_g
  choose z hz using fun j ↦ hg (c j)
  let t := tensorWedgeEquiv E G U.property.1
  have hq : g.app U.val ∘ z = c := funext hz
  have ht : t (ModuleCat.exteriorPower.mk b ⊗ₜ ModuleCat.exteriorPower.mk c) =
      tensorWedge E G b c := tensorWedgeEquiv_tmul E G U.property.1 b c
  refine ⟨e (t.symm s), b, z, ?_⟩
  rw [hq, ← ht]
  apply t.symm.injective
  apply e.injective
  simp only [LinearEquiv.map_smul, LinearEquiv.symm_apply_apply, hgen, smul_eq_mul, mul_one]

private lemma determinantOnFrame_restrict {U : X.Opens} {V : FrameOpens E G} (j : V.val ⟶ U)
    (v : Fin n → Γ(E.obj.obj, U)) (z : Fin r → Γ(M, U)) :
    determinantOnFrame E G f g h V
        ((DE ⊗ DG).presheaf.map j.op (tensorWedge E G v (g.app U ∘ z))) =
      (DM).presheaf.map j.op (wedgeSection (Fin.append (f.app U ∘ v) z)) := by
  rw [map_tensorWedge, map_wedgeSection]
  have hg : G.obj.obj.presheaf.map j.op ∘ (g.app U ∘ z) =
      g.app V.val ∘ (M.presheaf.map j.op ∘ z) :=
    funext fun i ↦ (Hom.naturality_apply g j (z i)).symm
  have hf : f.app V.val ∘ (E.obj.obj.presheaf.map j.op ∘ v) =
      M.presheaf.map j.op ∘ (f.app U ∘ v) :=
    funext fun i ↦ Hom.naturality_apply f j (v i)
  rw [hg, determinantOnFrame_apply, Fin.comp_append, hf]

private lemma determinantOnFrame_naturality {U V : FrameOpens E G} (j : V.val ⟶ U.val)
    (s : Γ(DE ⊗ DG, U.val)) :
    determinantOnFrame E G f g h V ((DE ⊗ DG).presheaf.map j.op s) =
      (DM).presheaf.map j.op (determinantOnFrame E G f g h U s) := by
  obtain ⟨a, v, z, rfl⟩ := exists_smul_tensorWedge E G f g h U s
  simp only [Scheme.Modules.map_smul, LinearEquiv.map_smul, determinantOnFrame_apply,
    determinantOnFrame_restrict]

private def determinantHom : DE ⊗ DG ⟶ DM :=
  homOfBasis (isBasis_frameOpens E G) (fun U ↦ (determinantOnFrame E G f g h U).toLinearMap)
    (determinantOnFrame_naturality E G f g h)

private lemma determinantHom_app_frame (U : FrameOpens E G) (s : Γ(DE ⊗ DG, U.val)) :
    (determinantHom E G f g h).app U.val s = determinantOnFrame E G f g h U s :=
  homOfBasis_app _ _ _ U s

/-- The canonical comparison from the tensor of the top exterior powers of the end terms
of a short exact sequence to the top exterior power of the middle term. -/
def determinantShortExactIso : DE ⊗ DG ≅ DM := by
  have : IsIso (determinantHom E G f g h) := by
    refine Hom.isIso_of_isBasis _ (isBasis_frameOpens E G) fun U ↦ ?_
    refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
    have he : ⇑((determinantHom E G f g h).app U.val) = ⇑(determinantOnFrame E G f g h U) :=
      funext (determinantHom_app_frame E G f g h U)
    rw [he]
    exact (determinantOnFrame E G f g h U).bijective
  exact asIso (determinantHom E G f g h)

/-- The determinant comparison concatenates the images of the subbundle sections with the
chosen lifts of the quotient sections, in that order. This formula holds on any open. -/
@[simp]
theorem determinantShortExactIso_hom_app {U : X.Opens}
    (v : Fin n → Γ(E.obj.obj, U)) (z : Fin r → Γ(M, U)) :
    (determinantShortExactIso E G f g h).hom.app U
        (tmulRight DE (G.obj.obj.exteriorPowerSections U r
          (ModuleCat.exteriorPower.mk (g.app U ∘ z)))
          (E.obj.obj.exteriorPowerSections U n (ModuleCat.exteriorPower.mk v))) =
      M.exteriorPowerSections U (n + r)
        (ModuleCat.exteriorPower.mk (Fin.append (f.app U ∘ v) z)) := by
  -- Re-express the displayed tensors and wedges with the local section constructors.
  change (determinantHom E G f g h).app U (tensorWedge E G v (g.app U ∘ z)) =
    wedgeSection (Fin.append (f.app U ∘ v) z)
  refine TopCat.Presheaf.IsSheaf.section_ext (DM).isSheaf fun x hx ↦ ?_
  obtain ⟨_, ⟨V, rfl⟩, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_frameOpens E G) hx
  refine ⟨V.val, hVU, hxV, ?_⟩
  let j : V.val ⟶ U := homOfLE hVU
  rw [← Hom.naturality_apply (determinantHom E G f g h) j, determinantHom_app_frame]
  exact determinantOnFrame_restrict E G f g h j v z

/-- The inverse determinant comparison separates a wedge of subbundle sections and lifts
into the tensor of the subbundle wedge and the wedge of the quotient images. -/
@[simp]
theorem determinantShortExactIso_inv_app {U : X.Opens}
    (v : Fin n → Γ(E.obj.obj, U)) (z : Fin r → Γ(M, U)) :
    (determinantShortExactIso E G f g h).inv.app U
        (M.exteriorPowerSections U (n + r)
          (ModuleCat.exteriorPower.mk (Fin.append (f.app U ∘ v) z))) =
      tmulRight DE (G.obj.obj.exteriorPowerSections U r
        (ModuleCat.exteriorPower.mk (g.app U ∘ z)))
        (E.obj.obj.exteriorPowerSections U n (ModuleCat.exteriorPower.mk v)) := by
  rw [← determinantShortExactIso_hom_app E G f g h v z, ← ConcreteCategory.comp_apply,
    ← Hom.comp_app, Iso.hom_inv_id, Hom.id_app, ConcreteCategory.id_apply]

/-- The formula on wedges with quotient lifts characterizes the determinant comparison.
It suffices to verify the formula on affine opens. -/
theorem determinantShortExactIso_hom_unique (φ : DE ⊗ DG ⟶ DM)
    (hφ : ∀ (U : X.Opens), IsAffineOpen U →
      ∀ (v : Fin n → Γ(E.obj.obj, U)) (z : Fin r → Γ(M, U)),
        φ.app U (tmulRight DE (G.obj.obj.exteriorPowerSections U r
          (ModuleCat.exteriorPower.mk (g.app U ∘ z)))
          (E.obj.obj.exteriorPowerSections U n (ModuleCat.exteriorPower.mk v))) =
        M.exteriorPowerSections U (n + r)
          (ModuleCat.exteriorPower.mk (Fin.append (f.app U ∘ v) z))) :
    φ = (determinantShortExactIso E G f g h).hom := by
  apply hom_ext_of_isBasis (isBasis_frameOpens E G)
  intro U s
  obtain ⟨a, v, z, rfl⟩ := exists_smul_tensorWedge E G f g h U s
  simp only [Hom.app_smul]
  exact congrArg (a • ·) ((hφ U.val U.property.1 v z).trans
    (determinantShortExactIso_hom_app E G f g h v z).symm)

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank

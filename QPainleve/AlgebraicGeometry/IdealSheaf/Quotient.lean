/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.TensorProduct
public import TauCeti.AlgebraicGeometry.IdealSheaf.MayerVietoris
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

import TauCeti.Algebra.Homology.ShortComplex.ShortExact
import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
import TauCeti.AlgebraicGeometry.Modules.Pushforward.Basic
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
import TauCeti.AlgebraicGeometry.Modules.SchemeTheoreticSupport

/-!
# Quotients of ideals by products

The quotient of an ideal sheaf by its product with another ideal sheaf
is the direct image of its restriction to the closed subscheme of the
second ideal. For nested ideals, this quotient is the kernel of the restriction
between the corresponding closed subschemes.
-/

public section

open CategoryTheory Limits MonoidalCategory
open TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

noncomputable section

/-- The ideal inclusion regarded in the category of scheme modules. -/
private abbrev sheafι' (I : X.IdealSheafData) : I.sheaf ⟶ Scheme.Modules.unit X := I.sheafι

/-- The inclusion of one ideal sheaf into a larger ideal sheaf. -/
def sheafHomOfLE {I J : X.IdealSheafData} (h : I ≤ J) : I.sheaf ⟶ J.sheaf :=
  J.sheafLift I.sheafι fun U s ↦ sections_mono h U (I.sheafι_app_mem U s)

/-- Composing the ideal-sheaf inclusion with the inclusion into the structure sheaf
recovers the inclusion of the smaller ideal. -/
@[simp]
theorem sheafHomOfLE_sheafι {I J : X.IdealSheafData} (h : I ≤ J) :
    sheafHomOfLE h ≫ (J.sheafι : J.sheaf ⟶ Scheme.Modules.unit X) = I.sheafι :=
  J.sheafLift_ι _ _

instance {I J : X.IdealSheafData} (h : I ≤ J) : Mono (sheafHomOfLE h) :=
  mono_of_mono_fac (sheafHomOfLE_sheafι h)

/-- On sections, the quotient restriction is the pullback of regular functions along
the inclusion of closed subschemes. -/
theorem pushforwardSubschemeMap_app {I J : X.IdealSheafData} (h : I ≤ J)
    (U : X.Opens) (s : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U)) :
    (pushforwardSubschemeMap h).app U s =
      (inclusion h).appLE (I.subschemeι ⁻¹ᵁ U) (J.subschemeι ⁻¹ᵁ U)
        (le_of_eq (by rw [← Scheme.Hom.comp_preimage, inclusion_subschemeι])) s := by
  let a := inclusion h
  let b := I.subschemeι
  let c := J.subschemeι
  have hab : a ≫ b = c := inclusion_subschemeι h
  let M := Scheme.Modules.unit J.subscheme
  let N := Scheme.Modules.unit I.subscheme
  let φ : N ⟶ (Scheme.Modules.pushforward a).obj M :=
    SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom
  let ψ : I.pushforwardSubscheme ⟶ J.pushforwardSubscheme :=
    (Scheme.Modules.pushforward b).map φ ≫ (Scheme.Modules.pushforwardComp a b).hom.app M ≫
      (Scheme.Modules.pushforwardCongr hab).hom.app M
  have happ (V : X.Opens) (t : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V)) :
      ψ.app V t = a.appLE (b ⁻¹ᵁ V) (c ⁻¹ᵁ V)
        (le_of_eq (by rw [← Scheme.Hom.comp_preimage, hab])) t := by
    exact pushforward_composite_app a b c hab M N φ V t
  have hψ : pushforwardSubschemeMap h = ψ := by
    refine (cancel_epi I.toPushforwardSubscheme).mp
      ((toPushforwardSubscheme_pushforwardSubschemeMap h).trans ?_)
    refine (Scheme.Modules.hom_ext _ _ fun V ↦ ConcreteCategory.hom_ext _ _ fun t ↦ ?_).symm
    have hle : c ⁻¹ᵁ V ≤ a ⁻¹ᵁ b ⁻¹ᵁ V :=
      le_of_eq (by rw [← Scheme.Hom.comp_preimage, hab])
    have hcomp : b.app V ≫ a.appLE (b ⁻¹ᵁ V) (c ⁻¹ᵁ V) hle = c.app V :=
      (Scheme.Hom.comp_appLE a b V (c ⁻¹ᵁ V) hle).symm.trans
        (by simpa only [hab] using (Scheme.Hom.appLE_eq_app (f := c) (U := V)))
    have ht := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcomp) t
    have hI := I.toPushforwardSubscheme_app (U := V) t
    have hJ := J.toPushforwardSubscheme_app (U := V) t
    exact (congrArg (ψ.app V) hI).trans ((happ V (b.app V t)).trans (ht.trans hJ.symm))
  exact (congrArg (fun f ↦ f.app U s) hψ).trans (happ U s)

/-- The inclusion of `J/I` into the direct image of the structure sheaf of `V(I)`,
for nested ideal sheaves `I ≤ J`. -/
def quotientToPushforwardSubscheme {I J : X.IdealSheafData} (h : I ≤ J) :
    cokernel (sheafHomOfLE h) ⟶ I.pushforwardSubscheme :=
  cokernel.desc _ (sheafι' J ≫ I.toPushforwardSubscheme) (by
    exact (Category.assoc _ _ _).symm.trans
      ((sheafHomOfLE_sheafι h =≫ I.toPushforwardSubscheme).trans
        I.sheafι_toPushforwardSubscheme))

/-- On representatives in `J`, the inclusion of `J/I` is reduction modulo `I`. -/
@[reassoc (attr := simp)]
theorem cokernel_π_quotientToPushforwardSubscheme {I J : X.IdealSheafData} (h : I ≤ J) :
    cokernel.π (sheafHomOfLE h) ≫ quotientToPushforwardSubscheme h =
      (J.sheafι : J.sheaf ⟶ Scheme.Modules.unit X) ≫ I.toPushforwardSubscheme :=
  cokernel.π_desc _ _ _

/-- A section of `J/I` vanishes on the subscheme cut out by `J`. -/
@[reassoc (attr := simp)]
theorem quotientToPushforwardSubscheme_pushforwardSubschemeMap {I J : X.IdealSheafData}
    (h : I ≤ J) :
    quotientToPushforwardSubscheme h ≫ pushforwardSubschemeMap h = 0 := by
  rw [← cancel_epi (cokernel.π (sheafHomOfLE h)), comp_zero,
    cokernel_π_quotientToPushforwardSubscheme_assoc]
  exact (Category.assoc (sheafι' J) _ _).trans
    ((sheafι' J ≫= toPushforwardSubscheme_pushforwardSubschemeMap h).trans
      J.sheafι_toPushforwardSubscheme)

/-- For nested ideals `I ≤ J`, the restriction from `V(I)` to `V(J)` has kernel `J/I`.
This identifies Tau Ceti's `cokernelCompSequence` for the two inclusions `I ⟶ J ⟶ 𝒪_X`
with the structure sheaves of the closed subschemes. -/
theorem shortExact_quotientToPushforwardSubscheme {I J : X.IdealSheafData} (h : I ≤ J) :
    (ShortComplex.mk _ _
      (quotientToPushforwardSubscheme_pushforwardSubschemeMap h)).ShortExact := by
  let f := sheafHomOfLE h
  let g := sheafι' J
  let T := TauCeti.cokernelCompSequence f g
  let S := ShortComplex.mk _ _ (quotientToPushforwardSubscheme_pushforwardSubschemeMap h)
  have hcomp : f ≫ g = I.sheafι := sheafHomOfLE_sheafι h
  let e : cokernel (f ≫ g) ≅ I.pushforwardSubscheme :=
    cokernelIsoOfEq hcomp ≪≫ (cokernelIsCokernel _).coconePointUniqueUpToIso
      I.shortExact_toPushforwardSubscheme.gIsCokernel
  let e' : cokernel g ≅ J.pushforwardSubscheme :=
    (cokernelIsCokernel _).coconePointUniqueUpToIso
      J.shortExact_toPushforwardSubscheme.gIsCokernel
  have he : cokernel.π (f ≫ g) ≫ e.hom = I.toPushforwardSubscheme := by
    rw [Iso.trans_hom, π_comp_cokernelIsoOfEq_hom_assoc]
    exact IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
      I.shortExact_toPushforwardSubscheme.gIsCokernel WalkingParallelPair.one
  have he' : cokernel.π g ≫ e'.hom = J.toPushforwardSubscheme :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
      J.shortExact_toPushforwardSubscheme.gIsCokernel WalkingParallelPair.one
  have h₁ : quotientToPushforwardSubscheme h = T.f ≫ e.hom := by
    refine (cancel_epi (cokernel.π f)).mp ?_
    dsimp [T, TauCeti.cokernelCompSequence]
    simp only [cokernel.π_desc_assoc, Category.assoc, he]
    exact cokernel_π_quotientToPushforwardSubscheme h
  have h₂ : e.hom ≫ pushforwardSubschemeMap h = T.g ≫ e'.hom := by
    refine (cancel_epi (cokernel.π (f ≫ g))).mp ?_
    dsimp [T, TauCeti.cokernelCompSequence]
    simp only [cokernel.π_desc_assoc, Category.id_comp, reassoc_of% he, he',
      toPushforwardSubscheme_pushforwardSubschemeMap]
  let i : T ≅ S := ShortComplex.isoMk (Iso.refl _) e e'
    ((Category.id_comp _).trans h₁) h₂
  have : Mono g := inferInstanceAs (Mono (sheafι' J))
  exact ShortComplex.shortExact_of_iso i (TauCeti.cokernelCompSequence_shortExact f g)

/-- The inclusion of a product ideal into the first factor is the tensor of the
second ideal's inclusion with the first factor. -/
@[reassoc]
theorem sheafMul_sheafHomOfLE_mul (I J : X.IdealSheafData) :
    I.sheafMul J ≫ sheafHomOfLE (mul_le_of_le_one_right' (a := I) (b := J) le_top) =
      I.sheaf ◁ (J.sheafι : J.sheaf ⟶ Scheme.Modules.unit X) ≫ (ρ_ I.sheaf).hom := by
  let i := sheafι' I
  let j := sheafι' J
  refine (cancel_mono i).mp ?_
  calc
    _ = (i ⊗ₘ j) ≫ (λ_ (𝟙_ X.Modules)).hom :=
      (Category.assoc _ _ _).trans
        ((I.sheafMul J ≫= sheafHomOfLE_sheafι _).trans (I.sheafMul_sheafι J))
    _ = (I.sheaf ◁ j ≫ (ρ_ I.sheaf).hom) ≫ i := by
      rw [tensorHom_def', unitors_equal, Category.assoc, Category.assoc]
      exact (I.sheaf ◁ j) ≫= rightUnitor_naturality i

/-- The quotient of an ideal sheaf by its product with a second ideal is the
direct image of its restriction to the closed subscheme defined by the second
ideal. -/
theorem isIso_unit_app_cokernel_sheafHomOfLE_mul (I J : X.IdealSheafData) :
    IsIso ((pullbackPushforwardAdjunction J.subschemeι).unit.app
      (cokernel (sheafHomOfLE (mul_le_of_le_one_right' (a := I) (b := J) le_top)))) := by
  let j := sheafHomOfLE (mul_le_of_le_one_right' (a := I) (b := J) le_top)
  let q := cokernel.π j
  apply isIso_unit_app_of_ker_ideal_le_annihilator
  intro U
  rw [J.ker_subschemeι]
  intro a ha
  refine Module.mem_annihilator.mpr fun t ↦ ?_
  obtain ⟨s, rfl⟩ := Hom.app_surjective_of_epi_of_isAffineOpen q U.val U.property t
  let b : Γ(X, U) := I.sheafι.app U s
  have hb : b ∈ I.sections U := I.sheafι_app_mem U s
  have hmem : a * b ∈ (I * J).sections U := by
    rw [I.sections_eq_ideal U] at hb
    rw [sections_eq_ideal, ideal_mul, Pi.mul_apply]
    exact (mul_comm b a) ▸ Ideal.mul_mem_mul hb ha
  let w := (I * J).sectionMk (a * b) hmem
  have hw : j.app U w = a • s := by
    apply I.sheafι_app_injective U
    have h := ConcreteCategory.congr_hom
      (congrArg (fun f : (I * J).sheaf ⟶ Scheme.Modules.unit X ↦ Scheme.Modules.Hom.app f U)
        (sheafHomOfLE_sheafι (mul_le_of_le_one_right' (a := I) (b := J) le_top))) w
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, sheafι_app_sectionMk] at h
    exact h.trans ((I.sheafι.app_smul a s).trans rfl).symm
  rw [← q.app_smul, ← hw]
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f : (I * J).sheaf ⟶ cokernel j ↦ Scheme.Modules.Hom.app f U)
      (cokernel.condition j)) w
  simpa only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app,
    ConcreteCategory.comp_apply, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply] using h

end

end AlgebraicGeometry.Scheme.IdealSheafData

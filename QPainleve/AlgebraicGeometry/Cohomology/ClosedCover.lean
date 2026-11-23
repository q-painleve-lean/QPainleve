/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Cohomology.AmpleCriterion
public import QPainleve.AlgebraicGeometry.Cohomology.SerreVanishing

import QPainleve.AlgebraicGeometry.IdealSheaf.FiniteType
import QPainleve.AlgebraicGeometry.IdealSheaf.Nilpotence
import QPainleve.AlgebraicGeometry.IdealSheaf.Quotient
import QPainleve.AlgebraicGeometry.VectorBundle.ProjectionFormula
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Basic
import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Basic

/-!
# Vanishing for ideal twists from a closed cover

For a finite list of closed subschemes, successive products of their defining
ideals give a filtration of an ideal sheaf. Each successive quotient is carried
by the corresponding closed subscheme. If the product annihilates the starting
ideal, Serre vanishing on the closed subschemes gives vanishing on the whole
ideal twist. This is the ideal-sheaf filtration used in the componentwise
ampleness criterion. For the componentwise ampleness application and the
finite-surjective descent it specializes, see
[Stacks Project, Lemma 33.44.15](https://stacks.math.columbia.edu/tag/0B5Y)
and [30.17.2](https://stacks.math.columbia.edu/tag/0B5V).
-/

public section

open AlgebraicGeometry CategoryTheory Filter Limits MonoidalCategory TopologicalSpace
open Scheme.IdealSheafData Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) [IsProper f]

include f in
private theorem eventually_subsingleton_cohomology_tensorPow_pushforward
    {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
    (G : Y.Modules) [G.IsQuasicoherent] [G.IsFiniteType]
    (L P : InvertibleSheaf X) (hL : (LineBundleClass.pullback i (LineBundleClass.mk L)).IsAmple) :
    ∀ᶠ n : ℕ in atTop, ∀ q : ℕ, 0 < q →
      Subsingleton (Cohomology ((P.tensorProduct (L.tensorPow n)).obj ⊗
        (pushforward i).obj G) q) := by
  let L' := (InvertibleSheaf.pullback i).obj L
  let P' := (Scheme.Modules.pullback i).obj P.obj
  have hL' : (LineBundleClass.mk L').IsAmple := by
    rwa [← LineBundleClass.pullback_mk]
  filter_upwards [(i ≫ f).eventually_subsingleton_cohomology_tensorPow_of_isAmple
    (P' ⊗ G) L' hL'] with n h q hq
  let M := P.tensorProduct (L.tensorPow n)
  let pull := Scheme.Modules.pullback i
  let push := pushforward i
  have hproj := i.isIso_tensorPushforwardHom M G
  obtain ⟨ePow⟩ := L.nonempty_pullback_tensorPow_iso i n
  let e₁ : pull.obj (L.tensorPow n).obj ≅ (L'.tensorPow n).obj :=
    (eqToIso (InvertibleSheaf.pullback_obj_obj i (L.tensorPow n))).symm ≪≫ ePow
  let e₂ : pull.obj M.obj ≅ P' ⊗ (L'.tensorPow n).obj :=
    pull.mapIso (P.tensorProductObjIso (L.tensorPow n)) ≪≫
      ((pullbackTensorLeftIso i P.obj).app (L.tensorPow n).obj) ≪≫ (Iso.refl P' ⊗ᵢ e₁)
  let e₃ : pull.obj M.obj ⊗ G ≅ (P' ⊗ G) ⊗ (L'.tensorPow n).obj :=
    whiskerRightIso e₂ G ≪≫ (α_ _ _ _) ≪≫
      whiskerLeftIso P' (β_ (L'.tensorPow n).obj G) ≪≫ (α_ _ _ _).symm
  let eH := (cohomologyFunctor X q).mapIso
      (asIso (i.tensorPushforwardHom M.obj G) ≪≫ push.mapIso e₃) ≪≫
    cohomologyPushforwardIso i ((P' ⊗ G) ⊗ (L'.tensorPow n).obj) q
  exact eH.addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mpr (h q hq)

include f in
/-- Suppose that an ideal sheaf is annihilated by a product of ideal sheaves.
If a line bundle is ample on each of the closed subschemes defined by the
factors, its high tensor powers, even after a fixed line-bundle twist, kill
the positive cohomology of the original ideal sheaf. -/
theorem eventually_subsingleton_cohomology_tensorPow_ideal_of_mul_prod_eq_bot
    (L P : InvertibleSheaf X) (I : X.IdealSheafData) (l : List X.IdealSheafData)
    (hl : I * l.prod = ⊥)
    (hL : ∀ J ∈ l, (LineBundleClass.pullback J.subschemeι (LineBundleClass.mk L)).IsAmple) :
    ∀ᶠ n : ℕ in atTop, ∀ q : ℕ, 0 < q →
      Subsingleton (Cohomology ((P.tensorProduct (L.tensorPow n)).obj ⊗ I.sheaf) q) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  induction l generalizing I with
  | nil =>
    simp only [List.prod_nil, mul_one] at hl
    subst I
    exact Eventually.of_forall fun n q _ ↦ AddCommGrpCat.subsingleton_of_isZero
      (((cohomologyFunctor X q).map_isZero)
        ((tensorLeft (P.tensorProduct (L.tensorPow n)).obj).map_isZero
          (isZero_sheaf_bot (X := X))))
  | cons J l ih =>
    have hprod : (I * J) * l.prod = ⊥ := by
      simpa only [List.prod_cons, mul_assoc] using hl
    let j := sheafHomOfLE (mul_le_of_le_one_right' (a := I) (b := J) le_top)
    let Q := cokernel j
    let i := J.subschemeι
    let G := (Scheme.Modules.pullback i).obj Q
    have : I.sheaf.IsFiniteType := I.isFiniteType_sheaf
    have : Q.IsFiniteType := isFiniteType_of_epi (cokernel.π j)
    have hIso := isIso_unit_app_cokernel_sheafHomOfLE_mul I J
    let e : Q ≅ (pushforward i).obj G :=
      asIso ((pullbackPushforwardAdjunction i).unit.app Q)
    filter_upwards [ih (I * J) hprod (fun K hK ↦ hL K (List.mem_cons_of_mem _ hK)),
      f.eventually_subsingleton_cohomology_tensorPow_pushforward i G L P
        (hL J List.mem_cons_self)] with n h₁ h₃ q hq
    let M := (P.tensorProduct (L.tensorPow n)).obj
    have hS := shortExact_map_tensorLeft M (TauCeti.cokernelSequence_shortExact j)
    have hQ : Subsingleton (Cohomology (M ⊗ Q) q) :=
      ((cohomologyFunctor X q).mapIso (whiskerLeftIso M e)).addCommGroupIsoToAddEquiv
        |>.toEquiv.subsingleton_congr.mpr (h₃ q hq)
    exact TauCeti.AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_X₂ hS q (h₁ q hq) hQ

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry.LineBundleClass

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}

/-- On a proper scheme over a Noetherian ring carrying an ample class, a line bundle
is ample if and only if its restrictions to a finite closed cover are ample.
The closed subschemes need only cover the underlying space. -/
theorem isAmple_iff_of_closedCover (f : X ⟶ Spec (.of R)) [IsProper f]
    {a A : LineBundleClass X} (hA : A.IsAmple)
    (l : List X.IdealSheafData) (hcover : ∀ x : X, ∃ J ∈ l, x ∈ J.support) :
    a.IsAmple ↔ ∀ J ∈ l, (pullback J.subschemeι a).IsAmple := by
  refine ⟨fun h J _ ↦ h.pullback_of_isAffineHom J.subschemeι, fun h ↦ ?_⟩
  obtain ⟨L, rfl⟩ := mk_surjective a
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := hA.compactSpace
  have : IsNoetherian X := {}
  have hs : l.prod.support = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨J, hJ, hx⟩ := hcover x
    exact support_le_support_list_prod_of_mem hJ hx
  obtain ⟨d, hd⟩ := l.prod.isNilpotent_of_support_eq_top hs
  let l' := (List.replicate d l).flatten
  have hp : l'.prod = 0 := by
    simpa only [l', List.prod_flatten, List.map_replicate, List.prod_replicate] using hd
  have h' (J : X.IdealSheafData) (hJ : J ∈ l') : (pullback J.subschemeι (mk L)).IsAmple := by
    obtain ⟨K, hK, hJK⟩ := List.mem_flatten.mp hJ
    exact h J ((List.eq_of_mem_replicate hK) ▸ hJK)
  apply isAmple_mk_of_subsingleton_cohomology_one_closedPoint L hA
  intro x _ P
  have := f.eventually_subsingleton_cohomology_tensorPow_ideal_of_mul_prod_eq_bot L P
    (X.fromSpecResidueField x).ker l' (by rw [hp, mul_zero]; rfl) h'
  apply Eventually.exists (f := atTop)
  filter_upwards [this, eventually_gt_atTop (0 : ℕ)] with n hvan hn
  exact ⟨hn, hvan 1 Nat.one_pos⟩

/-- A line bundle on a projective scheme over a Noetherian ring is ample precisely
when it is ample on every irreducible component with the reduced structure.
This applies to reducible and nonreduced schemes. -/
theorem isAmple_iff_restrict_irreducibleComponents [X.Over (Spec (.of R))]
    [X.IsProjectiveOver R] (a : LineBundleClass X) :
    a.IsAmple ↔ ∀ C : irreducibleComponents X,
      (pullback (vanishingIdeal (⟨C.val, isClosed_of_mem_irreducibleComponents _ C.property⟩ :
        Closeds X)).subschemeι a).IsAmple := by
  classical
  let f := X ↘ Spec (.of R)
  obtain ⟨A, hA⟩ := X.exists_isAmple_of_isProjectiveOver R
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := hA.compactSpace
  have : IsNoetherian X := {}
  let J (C : irreducibleComponents X) : X.IdealSheafData :=
    vanishingIdeal ⟨C.val, isClosed_of_mem_irreducibleComponents _ C.property⟩
  let : Fintype (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.fintype
  let l := (Finset.univ.toList.map J : List X.IdealSheafData)
  have hl (C : irreducibleComponents X) : J C ∈ l := by simp [l]
  have hcover (x : X) : ∃ I ∈ l, x ∈ I.support := by
    let C : irreducibleComponents X := ⟨irreducibleComponent x,
      irreducibleComponent_mem_irreducibleComponents x⟩
    refine ⟨J C, hl C, ?_⟩
    dsimp only [J]
    rw [← SetLike.mem_coe, coe_support_vanishingIdeal]
    exact mem_irreducibleComponent
  rw [isAmple_iff_of_closedCover f hA l hcover]
  exact ⟨fun h C ↦ h (J C) (hl C), fun h I hi ↦ by
    obtain ⟨C, _, rfl⟩ := List.mem_map.mp hi
    exact h C⟩

end TauCeti.AlgebraicGeometry.LineBundleClass

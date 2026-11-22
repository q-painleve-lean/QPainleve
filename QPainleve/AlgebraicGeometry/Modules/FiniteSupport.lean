/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.LocalRing.Length
public import TauCeti.AlgebraicGeometry.Modules.BaseStalk
public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
public import TauCeti.AlgebraicGeometry.Modules.SchemeTheoreticSupport
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Semilocal
public import TauCeti.AlgebraicGeometry.VectorBundle.ProjectionFormula

/-!
# Sheaves of modules supported at finitely many points

A finite type quasi-coherent sheaf with finite support on a scheme locally of finite type
over a field has a finite scheme-theoretic support. Tensoring with a line bundle preserves
the isomorphism class of the sheaf because the line bundle is trivial on that finite
subscheme. For any sheaf of modules supported on finitely many closed points, global
sections identify with the product of the stalks.

## References

* The Stacks Project, Lemma 33.33.3 (Tag 0AYT).
-/

public section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

section OverField

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The scheme-theoretic support of a quasi-coherent sheaf with finite support on a scheme
locally of finite type over a field is finite over that field. -/
theorem isFinite_annihilator_subschemeι_comp [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (M : X.Modules) [M.IsQuasicoherent]
    (hM : ∀ U : X.affineOpens, Module.Finite Γ(X, U) Γ(M, U))
    (h : {x : X | Nontrivial (M.presheaf.stalk x)}.Finite) :
    IsFinite ((M.annihilator hM).subschemeι ≫ (X ↘ Spec (.of k))) := by
  let I := M.annihilator hM
  have hI : Set.range I.subschemeι = {x : X | Nontrivial (M.presheaf.stalk x)} := by
    rw [I.range_subschemeι]
    exact Set.ext fun _ ↦ M.mem_support_annihilator_iff_nontrivial_stalk hM
  have : Finite (Set.range I.subschemeι) := Set.Finite.to_subtype (hI.symm ▸ h)
  have : Finite I.subscheme :=
    Finite.of_injective (Set.rangeFactorization I.subschemeι)
      (Set.rangeFactorization_injective.mpr I.subschemeι.isEmbedding.injective)
  let f := I.subschemeι ≫ (X ↘ Spec (.of k))
  have : LocallyOfFiniteType f :=
    inferInstanceAs (LocallyOfFiniteType (I.subschemeι ≫ (X ↘ Spec (.of k))))
  have : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_finite_preimage_singleton f fun _ ↦ Set.toFinite _
  exact IsFinite.of_locallyQuasiFinite f

variable (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]

/-- A finite type quasi-coherent sheaf of finite support is the pushforward of a finite type
quasi-coherent sheaf along a closed immersion from a scheme finite over the base field. -/
theorem exists_iso_pushforward_of_finite_support [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (h : {x : X | Nontrivial (M.presheaf.stalk x)}.Finite) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (_ : IsClosedImmersion i)
      (_ : IsFinite (i ≫ (X ↘ Spec (.of k)))),
      Nonempty (M ≅ (pushforward i).obj ((pullback i).obj M)) := by
  let hM (U : X.affineOpens) := M.finite_sections_of_isAffineOpen U.val U.property
  let I := M.annihilator hM
  let i := I.subschemeι
  have hi : IsIso ((pullbackPushforwardAdjunction i).unit.app M) :=
    isIso_unit_app_of_ker_ideal_le_annihilator i M fun U ↦
      (IdealSheafData.le_def.mp (IdealSheafData.ker_subschemeι I).le U).trans_eq
        (M.annihilator_ideal hM U)
  exact ⟨I.subscheme, i, inferInstance, isFinite_annihilator_subschemeι_comp k M hM h,
    ⟨asIso ((pullbackPushforwardAdjunction i).unit.app M)⟩⟩

/-- All points in the finite support of a finite type quasi-coherent sheaf on a scheme locally
of finite type over a field are closed. -/
theorem isClosed_singleton_of_finite_support [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (h : {x : X | Nontrivial (M.presheaf.stalk x)}.Finite)
    {x : X} (hx : Nontrivial (M.presheaf.stalk x)) : IsClosed ({x} : Set X) := by
  let hM (U : X.affineOpens) := M.finite_sections_of_isAffineOpen U.val U.property
  let I := M.annihilator hM
  let f := I.subschemeι ≫ (X ↘ Spec (.of k))
  have : IsFinite f := isFinite_annihilator_subschemeι_comp k M hM h
  have : IsLocallyArtinian I.subscheme := IsLocallyArtinian.of_locallyQuasiFinite f
  have hx' : x ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact (M.mem_support_annihilator_iff_nontrivial_stalk hM).mpr hx
  obtain ⟨y, rfl⟩ := hx'
  simpa only [Set.image_singleton] using
    I.subschemeι.isClosedEmbedding.isClosedMap {y} (isClosed_discrete {y})

/-- Tensoring a finite type quasi-coherent sheaf of finite support with a line bundle yields
an isomorphic sheaf. -/
theorem nonempty_iso_tensor_left_of_finite_support [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (h : {x : X | Nontrivial (M.presheaf.stalk x)}.Finite) (L : InvertibleSheaf X) :
    Nonempty (L.obj ⊗ M ≅ M) := by
  obtain ⟨Z, i, _, hfinite, ⟨e⟩⟩ := exists_iso_pushforward_of_finite_support k M h
  let : Z.Over (Spec (.of k)) := ⟨i ≫ (X ↘ Spec (.of k))⟩
  have : IsFinite (Z ↘ Spec (.of k)) := hfinite
  let E := (InvertibleSheaf.toFixedRankOne X).obj L
  let E' := (FiniteLocallyFreeSheaf.FixedRank.pullback i).obj E
  obtain ⟨t⟩ := E'.nonempty_iso_free_of_isFinite k
  let toModules := FiniteLocallyFreeSheaf.FixedRank.toFiniteLocallyFree Z 1 ⋙
    (Scheme.Modules.isFiniteLocallyFree Z).ι
  let freeToUnit : (toModules.obj (FiniteLocallyFreeSheaf.FixedRank.free Z 1)) ≅
      𝟙_ Z.Modules :=
    eqToIso ((congrArg (fun F : FiniteLocallyFreeSheaf Z ↦ F.obj)
      (FiniteLocallyFreeSheaf.FixedRank.free_obj Z 1)).trans
        (FiniteLocallyFreeSheaf.free_obj Z _)) ≪≫
      (SheafOfModules.freeFunctor (R := Z.ringCatSheaf)).mapIso
        ((Equiv.ofUnique (ULift.{u} (Fin 1)) PUnit).toIso) ≪≫
      TauCeti.SheafOfModules.freePUnitIsoUnit Z.ringCatSheaf
  let L' := (InvertibleSheaf.toFiniteLocallyFree X).obj L
  have hp : E'.obj = (FiniteLocallyFreeSheaf.pullback i).obj L' := by
    simp only [E', E, L', FiniteLocallyFreeSheaf.FixedRank.pullback_obj_obj,
      InvertibleSheaf.toFixedRankOne_obj_obj]
  let G := (pullback i).obj M
  let trivialization := eqToIso (congrArg (fun F : FiniteLocallyFreeSheaf Z ↦ F.obj) hp.symm) ≪≫
    toModules.mapIso t ≪≫ freeToUnit
  exact ⟨tensorIso (Iso.refl _) e ≪≫
    (FiniteLocallyFreeSheaf.pushforwardTensorLeftIso i L').app G ≪≫
    (pushforward i).mapIso (tensorIso trivialization (Iso.refl G) ≪≫ λ_ G) ≪≫ e.symm⟩

end OverField

variable {X : Scheme.{u}} (M : X.Modules)

/-- If a sheaf of modules is supported on a finite set of closed points, a global section
is uniquely specified by its germs at those points. -/
theorem bijective_globalSections_germs
    {S : Set X} (hS : S.Finite) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (M.presheaf.stalk x)) :
    Function.Bijective (fun (s : Γ(M, ⊤)) (x : S) ↦
      M.presheaf.germ ⊤ x (Opens.mem_top _) s) := by
  classical
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨M.presheaf, M.isSheaf⟩
  refine ⟨fun s t h ↦ TopCat.Presheaf.section_ext F _ s t ?_, fun v ↦ ?_⟩
  · intro x hx
    by_cases hxS : x ∈ S
    · exact congrFun h ⟨x, hxS⟩
    · exact (hsupp x hxS).elim _ _
  let germs (x : X) : M.presheaf.stalk x := if hx : x ∈ S then v ⟨x, hx⟩ else 0
  choose V hxV s hs using fun x ↦ M.presheaf.exists_germ_eq (germs x)
  have hremove (x : X) : IsClosed (S \ {x}) := by
    simpa only [Set.biUnion_of_singleton] using
      (hS.sdiff (t := {x})).isClosed_biUnion (f := fun y ↦ ({y} : Set X))
        (fun y hy ↦ hclosed y hy.1)
  -- Shrink each representative's domain so its only possible nonzero stalk is at its center.
  let U (x : X) : X.Opens := V x ⊓ ⟨(S \ {x})ᶜ, (hremove x).isOpen_compl⟩
  let t (x : X) : Γ(M, U x) := M.presheaf.map (homOfLE (inf_le_left : U x ≤ V x)).op (s x)
  have hxU (x : X) : x ∈ U x := ⟨hxV x, by simp⟩
  have ht (x y : X) (hy : y ∈ U x) : M.presheaf.germ (U x) y hy (t x) = germs y := by
    by_cases hyS : y ∈ S
    · have hyx : y = x := by simpa [hyS] using hy.2
      subst y
      exact (M.presheaf.germ_res_apply _ x hy (s x)).trans (hs x)
    · exact (hsupp y hyS).elim _ _
  have hcover : (⊤ : X.Opens) ≤ ⨆ x, U x := fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' F U ⊤ (fun x ↦ (U x).leTop) hcover t
    (fun x y ↦ TopCat.Presheaf.section_ext F _ _ _ fun z hz ↦ by
      calc
        _ = M.presheaf.germ (U x) z hz.1 (t x) :=
          M.presheaf.germ_res_apply (Opens.infLELeft (U x) (U y)) z hz (t x)
        _ = germs z := ht x z hz.1
        _ = M.presheaf.germ (U y) z hz.2 (t y) := (ht y z hz.2).symm
        _ = _ := (M.presheaf.germ_res_apply (Opens.infLERight (U x) (U y)) z hz (t y)).symm)
  refine ⟨g, funext fun x ↦ ?_⟩
  exact (M.presheaf.Γgerm_res_apply x (hxU x) g).symm.trans
    ((congrArg (M.presheaf.germ (U x) x (hxU x)) (hg x)).trans
      ((ht x x (hxU x)).trans (dite_eq_left x.property)))

section BaseRing

variable (R : Type u) [CommRing R] [X.Over (Spec (.of R))]

/-- The linear equivalence from global sections of a sheaf supported at finitely many closed
points to the product of its stalks at those points. -/
def globalSectionsGermsLinearEquiv {S : Set X} (hS : S.Finite)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (M.presheaf.stalk x)) :
    Γ(M, ⊤) ≃ₗ[R] ((x : S) → M.presheaf.stalk x) :=
  LinearEquiv.ofBijective
    ({ toFun s (x : S) := M.presheaf.germ ⊤ x (Opens.mem_top _) s
       map_add' s t := funext fun x ↦
         map_add (M.presheaf.germ ⊤ (x : X) (Opens.mem_top _)).hom s t
       map_smul' r s := funext fun x ↦ by
         simp only [Pi.smul_apply, RingHom.id_apply]
         rw [base_smul_globalSections, germ_smul, base_smul_stalk_def,
           Scheme.baseRingToStalk_apply] }
      : Γ(M, ⊤) →ₗ[R] ((x : S) → M.presheaf.stalk x))
    (M.bijective_globalSections_germs hS hclosed hsupp)

@[simp]
lemma globalSectionsGermsLinearEquiv_apply {S : Set X} (hS : S.Finite)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (M.presheaf.stalk x)) (s : Γ(M, ⊤)) (x : S) :
    globalSectionsGermsLinearEquiv M R hS hclosed hsupp s x =
      M.presheaf.germ ⊤ x (Opens.mem_top _) s :=
  (rfl)

end BaseRing

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]

/-- For a finite-dimensional module stalk, its dimension over the base field is its local length
weighted by the residue degree. -/
theorem finrank_stalk_eq_length_mul (x : X) :
    Module.finrank k (M.presheaf.stalk x) =
      (Module.length (X.presheaf.stalk x) (M.presheaf.stalk x)).toNat *
        Module.finrank k (X.residueField x) := by
  have h := IsLocalRing.length_restrictScalars k (X.presheaf.stalk x) (M.presheaf.stalk x)
  rw [← Module.length_eq_of_surjective (M := IsLocalRing.ResidueField (X.presheaf.stalk x))
    (IsLocalRing.residue_surjective (R := k))] at h
  -- The scheme residue field bundles the local-ring residue field with its base algebra.
  let e : IsLocalRing.ResidueField (X.presheaf.stalk x) ≃ₐ[k] X.residueField x :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.refl _) fun r ↦ by
      rw [IsScalarTower.algebraMap_apply k (X.presheaf.stalk x)
        (IsLocalRing.ResidueField (X.presheaf.stalk x)),
        Scheme.algebraMap_residueField_eq_residue_comp_baseRingToStalk]
      rfl
  rw [← e.toLinearEquiv.finrank_eq]
  simpa only [Module.length_eq_rank, ENat.toNat_mul, Cardinal.toNat_toENat, Module.finrank] using
    congrArg ENat.toNat h

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Word
public import QPainleve.Geometry.Toric.CharacterTorus.Noncollision
public import Mathlib.AlgebraicGeometry.Birational.Composition

/-!
# Center parameters along a cluster word

The integral exponent substitutions of a typed word give a monomial isomorphism of
the center torus. Intersecting the inverse images of the distinct-center opens at all
prefixes gives the open where every intermediate center configuration is noncolliding.
This open is dense over any field and contains a rational point over a separably closed
field. It lets successive elementary transformations use a single initial choice of centers.
When a presentation has been constructed only on the image of a prefix's open, the next step
uses `centerStepPartialMap` to retain the noncollision conditions inherited from that prefix.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open QPainleve QPainleve.Cluster QPainleve.CharacterTorus

namespace Quiver.Path

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
  {B C D : SkewExchangeMatrix ι}

local notation "A" => (ι → ℤ)
local notation "e" j:arg => (Pi.single j (1 : ℤ) : A)

section Ring

variable (k : Type u) [CommRing k]

/-- The center map of a word is induced by its integral exponent substitution. -/
def centerIso (w : Word B C) : scheme k A ≅ scheme k A :=
  mapIso k w.exponentEquiv.toAddEquiv

/-- Pull back center characters by the word's integral substitution. -/
theorem centerIso_hom (w : Word B C) :
    (w.centerIso k).hom = CharacterTorus.map k w.exponentEquiv.toAddEquiv.toAddMonoidHom := by
  rw [centerIso, mapIso_hom]

/-- Pull back center characters through the inverse by the inverse integral substitution. -/
theorem centerIso_inv (w : Word B C) :
    (w.centerIso k).inv = CharacterTorus.map k w.exponentEquiv.symm.toAddEquiv.toAddMonoidHom := by
  rw [centerIso, mapIso_inv]
  rfl

/-- The center isomorphism is over the coefficient ring. -/
@[reassoc (attr := simp)]
theorem centerIso_hom_structureMap (w : Word B C) :
    (w.centerIso k).hom ≫ structureMap k A = structureMap k A := by
  rw [centerIso_hom, map_structureMap]

/-- The center isomorphism as an isomorphism over the coefficient ring. -/
def centerIsoOver (w : Word B C) :
    Over.mk (structureMap k A) ≅ Over.mk (structureMap k A) :=
  Over.isoMk (w.centerIso k) (w.centerIso_hom_structureMap k)

@[simp]
theorem centerIsoOver_hom_left (w : Word B C) :
    (w.centerIsoOver k).hom.left = (w.centerIso k).hom := (rfl)

@[simp]
theorem centerIsoOver_inv_left (w : Word B C) :
    (w.centerIsoOver k).inv.left = (w.centerIso k).inv := (rfl)

/-- The empty word fixes the center torus. -/
@[simp]
theorem centerIso_nil : (Path.nil : Word B B).centerIso k = Iso.refl _ := by
  apply Iso.ext
  rw [centerIso_hom, exponentEquiv_nil]
  exact CharacterTorus.map_id k

/-- The center maps of consecutive words compose in execution order. -/
@[simp]
theorem centerIso_comp (w : Word B C) (v : Word C D) :
    (w.comp v).centerIso k = w.centerIso k ≪≫ v.centerIso k := by
  apply Iso.ext
  simp only [centerIso_hom, exponentEquiv_comp, Iso.trans_hom]
  exact CharacterTorus.map_comp k v.exponentEquiv.toAddEquiv.toAddMonoidHom
    w.exponentEquiv.toAddEquiv.toAddMonoidHom

/-- On rational points, center transport precomposes the character with the word's
exponent substitution. -/
@[reassoc (attr := simp)]
theorem pointsEquiv_symm_comp_centerIso_hom (w : Word B C) (c : Multiplicative A →* kˣ) :
    ((pointsEquiv k A).symm c).val ≫ (w.centerIso k).hom =
      ((pointsEquiv k A).symm
        (c.comp w.exponentEquiv.toAddEquiv.toAddMonoidHom.toMultiplicative)).val := by
  rw [centerIso_hom, pointsEquiv_symm_comp_map]

/-- The inversion step sends a center character to its pointwise inverse. -/
@[reassoc]
theorem pointsEquiv_symm_comp_centerIso_hom_invert (c : Multiplicative A →* kˣ) :
    ((pointsEquiv k A).symm c).val ≫ (((Generator.invert).toStep B).toPath.centerIso k).hom =
      ((pointsEquiv k A).symm c⁻¹).val := by
  rw [pointsEquiv_symm_comp_centerIso_hom, exponentEquiv_toPath, Step.exponentEquiv_invert]
  congr 2
  apply MonoidHom.ext
  intro a
  exact c.map_inv a

variable {N : Type*} [AddCommGroup N]

/-- The open where centers with equal charges are distinct at every prefix of the word,
including the initial and terminal configurations. -/
def centerOpen : {C : SkewExchangeMatrix ι} → Word B C → ChargeSeed B N → (scheme k A).Opens
  | _, .nil, P => distinctCentersOpen k (fun j ↦ P.charge (e j))
  | _, .cons w s, P => centerOpen w P ⊓
      ((w.cons s).centerIso k).hom ⁻¹ᵁ
        distinctCentersOpen k (fun j ↦ ((w.cons s).chargeTarget P).charge (e j))

/-- For the empty word only the initial configuration is tested. -/
@[simp]
theorem centerOpen_nil (P : ChargeSeed B N) :
    (Path.nil : Word B B).centerOpen k P = distinctCentersOpen k (fun j ↦ P.charge (e j)) := (rfl)

/-- Appending a step adds the condition that the new endpoint has distinct centers. -/
theorem centerOpen_cons (w : Word B C) (s : C ⟶ D) (P : ChargeSeed B N) :
    (w.cons s).centerOpen k P = w.centerOpen k P ⊓
      ((w.cons s).centerIso k).hom ⁻¹ᵁ
        distinctCentersOpen k (fun j ↦ ((w.cons s).chargeTarget P).charge (e j)) := (rfl)

/-- The center map sends the word's open into the distinct-center open at its endpoint. -/
theorem centerOpen_le_preimage_distinctCentersOpen (w : Word B C) (P : ChargeSeed B N) :
    w.centerOpen k P ≤ (w.centerIso k).hom ⁻¹ᵁ
      distinctCentersOpen k (fun j ↦ (w.chargeTarget P).charge (e j)) := by
  cases w with
  | nil => simp
  | cons w s => rw [centerOpen_cons]; exact inf_le_right

/-- The simultaneous noncollision open lies in the noncollision open of the initial seed. -/
theorem centerOpen_le_centerOpen_nil (w : Word B C) (P : ChargeSeed B N) :
    w.centerOpen k P ≤ (Path.nil : Word B B).centerOpen k P := by
  induction w with
  | nil => exact le_rfl
  | cons w s ih => exact inf_le_left.trans ih

/-- The domain of a concatenation is the intersection of the first domain with the
inverse image of the second domain. -/
theorem centerOpen_comp (w : Word B C) (v : Word C D) (P : ChargeSeed B N) :
    (w.comp v).centerOpen k P = w.centerOpen k P ⊓
      (w.centerIso k).hom ⁻¹ᵁ v.centerOpen k (w.chargeTarget P) := by
  induction v with
  | nil =>
    simpa using (inf_eq_left.mpr (w.centerOpen_le_preimage_distinctCentersOpen k P)).symm
  | cons v s ih =>
    simp only [comp_cons, centerOpen_cons, ih, Scheme.Hom.preimage_inf, inf_assoc]
    rw [← Scheme.Hom.comp_preimage, ← Iso.trans_hom, ← centerIso_comp,
      ← chargeTarget_comp, comp_cons]

/-- A point lies in the domain exactly when every prefix sends it into the
distinct-center open of that prefix's charge realization. -/
theorem mem_centerOpen_iff (w : Word B C) (P : ChargeSeed B N) (x : scheme k A) :
    x ∈ w.centerOpen k P ↔ ∀ ⦃D : SkewExchangeMatrix ι⦄ (p : Word B D) (q : Word D C),
      p.comp q = w → (p.centerIso k).hom x ∈
        distinctCentersOpen k (fun j ↦ (p.chargeTarget P).charge (e j)) := by
  constructor
  · intro hx D p q h
    rw [← h, centerOpen_comp] at hx
    exact p.centerOpen_le_preimage_distinctCentersOpen k P hx.1
  · induction w with
    | nil =>
      intro h
      simpa using h Path.nil Path.nil rfl
    | cons w s ih =>
      intro h
      rw [centerOpen_cons]
      exact ⟨ih fun {_} p q hpq ↦ h p (q.cons s) (by rw [comp_cons, hpq]),
        h (w.cons s) Path.nil (comp_nil _)⟩

end Ring

variable {K : Type u} [Field K] {N : Type*} [AddCommGroup N]

/-- A center character lies in the domain exactly when its transport along each prefix
separates all different labels with equal charges at that prefix. -/
theorem point_mem_centerOpen_iff (w : Word B C) (P : ChargeSeed B N)
    (c : Multiplicative A →* Kˣ) (x : Spec (.of K)) :
    ((pointsEquiv K A).symm c).val x ∈ w.centerOpen K P ↔
      ∀ ⦃D : SkewExchangeMatrix ι⦄ (p : Word B D) (q : Word D C), p.comp q = w →
        ∀ i j, i ≠ j → (p.chargeTarget P).charge (e i) = (p.chargeTarget P).charge (e j) →
          c (ofAdd (p.exponentEquiv (e i))) ≠ c (ofAdd (p.exponentEquiv (e j))) := by
  rw [mem_centerOpen_iff]
  simp only [← Scheme.Hom.comp_apply, pointsEquiv_symm_comp_centerIso_hom,
    point_mem_distinctCentersOpen_iff, MonoidHom.comp_apply, AddMonoidHom.coe_toMultiplicative,
    Function.comp_apply, toAdd_ofAdd, AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_toAddEquiv]
  -- The evaluation from `toAddMonoidHom` uses the same function as the linear equivalence.
  rfl

attribute [local instance] hasUniqueDiv_of_free_int

/-- The center conditions for a finite word define a nonempty open over any field. -/
theorem nonempty_centerOpen (w : Word B C) (P : ChargeSeed B N) :
    (w.centerOpen K P : Set (scheme K A)).Nonempty := by
  let : IrreducibleSpace (scheme K A) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (AddMonoidAlgebra K A)))
  induction w with
  | nil => rw [centerOpen_nil]; exact nonempty_distinctCentersOpen _
  | cons w s ih =>
    let U := distinctCentersOpen K (fun j ↦ ((w.cons s).chargeTarget P).charge (e j))
    let f := ((w.cons s).centerIso K).hom
    have hU : (U : Set (scheme K A)).Nonempty := nonempty_distinctCentersOpen _
    rw [centerOpen_cons, TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_preimage]
    exact nonempty_preirreducible_inter (w.centerOpen K P).isOpen
      (f.continuous.isOpen_preimage _ U.isOpen) ih (hU.preimage f.homeomorph.surjective)

/-- The center conditions for a finite word hold on a dense open over any field. -/
theorem dense_centerOpen (w : Word B C) (P : ChargeSeed B N) :
    Dense (w.centerOpen K P : Set (scheme K A)) := by
  let : IrreducibleSpace (scheme K A) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (AddMonoidAlgebra K A)))
  exact (w.centerOpen K P).isOpen.dense (w.nonempty_centerOpen P)

variable (K) in
/-- The monomial center map restricted to the simultaneous noncollision open of a word. -/
def centerPartialMap (w : Word B C) (P : ChargeSeed B N) :
    (scheme K A).PartialMap (scheme K A) :=
  (w.centerIso K).hom.toPartialMap.restrict (w.centerOpen K P) (w.dense_centerOpen P) le_top

/-- The center map is the restriction of the regular monomial isomorphism. -/
theorem centerPartialMap_eq_restrict (w : Word B C) (P : ChargeSeed B N) :
    w.centerPartialMap K P =
      (w.centerIso K).hom.toPartialMap.restrict (w.centerOpen K P) (w.dense_centerOpen P) le_top :=
  (rfl)

/-- The center partial map has the simultaneous noncollision open as its domain. -/
@[simp]
theorem centerPartialMap_domain (w : Word B C) (P : ChargeSeed B N) :
    (w.centerPartialMap K P).domain = w.centerOpen K P := (rfl)

/-- The center partial map applies the monomial isomorphism after the open inclusion. -/
theorem centerPartialMap_hom (w : Word B C) (P : ChargeSeed B N) :
    (w.centerPartialMap K P).hom =
      (w.centerPartialMap K P).domain.ι ≫ (w.centerIso K).hom := by
  -- The restriction inserts the inclusion of the domain into the top open.
  change (scheme K A).homOfLE (show w.centerOpen K P ≤ ⊤ from le_top) ≫
    (scheme K A).topIso.hom ≫ (w.centerIso K).hom = _
  rw [Scheme.topIso_hom, Scheme.homOfLE_ι_assoc]
  rfl

instance (w : Word B C) (P : ChargeSeed B N) : IsDominant (w.centerPartialMap K P).hom := by
  have := Opens.isDominant_ι (w.centerPartialMap K P).dense_domain
  rw [centerPartialMap_hom]
  infer_instance

instance (w : Word B C) (P : ChargeSeed B N) : IsOpenImmersion (w.centerPartialMap K P).hom := by
  rw [centerPartialMap_hom]
  infer_instance

/-- The centers reached by a word form the image of its simultaneous noncollision open. -/
theorem centerPartialMap_opensRange (w : Word B C) (P : ChargeSeed B N) :
    (w.centerPartialMap K P).hom.opensRange = (w.centerIso K).inv ⁻¹ᵁ w.centerOpen K P := by
  simp only [centerPartialMap_hom, Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
    centerPartialMap_domain, Scheme.Hom.inv_preimage]

/-- The reached centers of a loop lie in the original noncollision open when the
initial charge kernel equals the exchange kernel. Equal charges are detected by
the basis differences in that kernel. -/
theorem centerPartialMap_opensRange_le_centerOpen_nil (w : Word B B) (P : ChargeSeed B N)
    (hker : B.matrix.mulVecLin.ker = P.charge.ker) :
    (w.centerPartialMap K P).hom.opensRange ≤ (Path.nil : Word B B).centerOpen K P := by
  have h := (w.exchangeKernel_eq_chargeTarget_ker P hker).symm.trans hker
  have hclasses (i j : ι) : (w.chargeTarget P).charge (e i) = (w.chargeTarget P).charge (e j) ↔
      P.charge (e i) = P.charge (e j) := by
    rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, h, LinearMap.mem_ker, map_sub, sub_eq_zero]
  have hU : distinctCentersOpen K (fun i ↦ (w.chargeTarget P).charge (e i)) =
      (Path.nil : Word B B).centerOpen K P := by
    rw [centerOpen_nil]
    apply SetLike.ext
    intro x
    simp only [mem_distinctCentersOpen_iff, hclasses]
  have hpre := w.centerOpen_le_preimage_distinctCentersOpen K P
  rw [hU] at hpre
  rw [centerPartialMap_opensRange, Scheme.Hom.inv_preimage]
  exact ((w.centerIso K).hom.image_mono hpre).trans
    ((w.centerIso K).hom.image_preimage_le _)

instance (w : Word B C) (P : ChargeSeed B N) :
    (w.centerPartialMap K P).IsOver (structureMap K A) (structureMap K A) where
  over := by simp [centerPartialMap_hom]

/-- The center partial map is over the base for the bundled slice objects.
The projected structure morphisms need their own instance for typeclass search. -/
instance (w : Word B C) (P : ChargeSeed B N) :
    (w.centerPartialMap K P).IsOver
      (Over.mk (structureMap K A)).hom (Over.mk (structureMap K A)).hom :=
  inferInstanceAs ((w.centerPartialMap K P).IsOver (structureMap K A) (structureMap K A))

/-- The center map for the empty word is the identity on the initial noncollision open. -/
theorem centerPartialMap_nil (P : ChargeSeed B N) :
    (Path.nil : Word B B).centerPartialMap K P =
      (Scheme.PartialMap.id (scheme K A)).restrict
        ((Path.nil : Word B B).centerOpen K P) (Path.nil.dense_centerOpen P) le_top := by
  simp only [centerPartialMap_eq_restrict, centerIso_nil, Iso.refl_hom, Scheme.PartialMap.id]

/-- The center partial maps compose on exactly the noncollision open of the concatenation. -/
theorem centerPartialMap_comp (w : Word B C) (v : Word C D) (P : ChargeSeed B N) :
    (w.comp v).centerPartialMap K P = (w.centerPartialMap K P).comp
      (v.centerPartialMap K (w.chargeTarget P)) := by
  let f := w.centerPartialMap K P
  let g := v.centerPartialMap K (w.chargeTarget P)
  have hd : (f.comp g).domain = (w.comp v).centerOpen K P := by
    simp only [f, g, Scheme.PartialMap.comp_domain, centerPartialMap_hom,
      Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, centerPartialMap_domain, centerOpen_comp]
  refine (Scheme.PartialMap.ext _ _ (hd.trans (centerPartialMap_domain _ _).symm) ?_).symm
  calc
    (f.comp g).hom = (f.comp g).domain.ι ≫ (w.centerIso K).hom ≫ (v.centerIso K).hom := by
      simp only [Scheme.PartialMap.comp_hom, g, centerPartialMap_hom, Category.assoc,
        morphismRestrict_ι_assoc, f, Scheme.Opens.isoImage_ι_inv_ι_assoc,
        Scheme.homOfLE_ι_assoc]
      rfl
    _ = _ := by
      simp only [centerPartialMap_hom, centerIso_comp, Iso.trans_hom,
        Scheme.isoOfEq_hom, Scheme.homOfLE_ι_assoc]

private theorem dense_centerStepDomain (w : Word B C) (s : C ⟶ D) (P : ChargeSeed B N) :
    let f := w.centerPartialMap K P
    let g := s.toPath.centerPartialMap K (w.chargeTarget P)
    Dense (↑(f.hom.opensRange ⊓ g.domain) : Set (scheme K A)) :=
  let f := w.centerPartialMap K P
  let g := s.toPath.centerPartialMap K (w.chargeTarget P)
  f.hom.denseRange.inter_of_isOpen_right g.dense_domain g.domain.isOpen

variable (K) in
/-- The center map for the next arrow, restricted to centers reached by the prefix
and satisfying the noncollision conditions of the arrow. -/
def centerStepPartialMap (w : Word B C) (s : C ⟶ D) (P : ChargeSeed B N) :
    (scheme K A).PartialMap (scheme K A) :=
  let f := w.centerPartialMap K P
  let g := s.toPath.centerPartialMap K (w.chargeTarget P)
  g.restrict (f.hom.opensRange ⊓ g.domain) (dense_centerStepDomain w s P) inf_le_right

/-- The input of a step lies in the image of the prefix's open and in the local step domain. -/
theorem centerStepPartialMap_domain (w : Word B C) (s : C ⟶ D) (P : ChargeSeed B N) :
    (w.centerStepPartialMap K s P).domain = (w.centerPartialMap K P).hom.opensRange ⊓
      (s.toPath.centerPartialMap K (w.chargeTarget P)).domain :=
  (rfl)

/-- The step domain is the image under the prefix of the appended word's open. -/
theorem centerStepPartialMap_domain_eq_preimage (w : Word B C) (s : C ⟶ D) (P : ChargeSeed B N) :
    (w.centerStepPartialMap K s P).domain = (w.centerIso K).inv ⁻¹ᵁ (w.cons s).centerOpen K P := by
  simp only [← Path.comp_toPath_eq_cons w s, centerStepPartialMap_domain,
    centerPartialMap_opensRange, centerPartialMap_domain, centerOpen_comp,
    Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, Iso.inv_hom_id,
    Scheme.Hom.id_preimage]

/-- Realizations on the local step open can be restricted to the inherited domain. -/
theorem centerStepPartialMap_eq_restrict (w : Word B C) (s : C ⟶ D) (P : ChargeSeed B N) :
    let g := s.toPath.centerPartialMap K (w.chargeTarget P)
    w.centerStepPartialMap K s P =
      g.restrict (w.centerStepPartialMap K s P).domain (w.centerStepPartialMap K s P).dense_domain
        (by rw [centerStepPartialMap_domain]; exact inf_le_right) :=
  (rfl)

/-- The inherited step map has the same monomial formula as the local step map. -/
theorem centerStepPartialMap_hom (w : Word B C) (s : C ⟶ D) (P : ChargeSeed B N) :
    (w.centerStepPartialMap K s P).hom =
      (w.centerStepPartialMap K s P).domain.ι ≫ (s.toPath.centerIso K).hom := by
  rw [centerStepPartialMap_eq_restrict, Scheme.PartialMap.restrict_hom, centerPartialMap_hom,
    Scheme.homOfLE_ι_assoc]
  rfl

instance (w : Word B C) (s : C ⟶ D) (P : ChargeSeed B N) :
    IsOpenImmersion (w.centerStepPartialMap K s P).hom := by
  rw [centerStepPartialMap_hom]
  infer_instance

instance (w : Word B C) (s : C ⟶ D) (P : ChargeSeed B N) :
    IsDominant (w.centerStepPartialMap K s P).hom := by
  have := Opens.isDominant_ι (w.centerStepPartialMap K s P).dense_domain
  rw [centerStepPartialMap_hom]
  infer_instance

instance (w : Word B C) (s : C ⟶ D) (P : ChargeSeed B N) :
    (w.centerStepPartialMap K s P).IsOver (Over.mk (structureMap K A)).hom
      (Over.mk (structureMap K A)).hom where
  over := by simp [centerStepPartialMap_hom]

variable (K) in
/-- Applying the prefix identifies the domain of the appended word with the domain
of its last step. Its inverse recovers the initial center of that word. -/
def centerStepDomainIso (w : Word B C) (s : C ⟶ D) (P : ChargeSeed B N) :
    ((w.cons s).centerPartialMap K P).domain.toScheme ≅ (w.centerStepPartialMap K s P).domain :=
  (w.centerIso K).hom.isoImage ((w.cons s).centerPartialMap K P).domain ≪≫
    (scheme K A).isoOfEq (by
      rw [centerPartialMap_domain, centerStepPartialMap_domain_eq_preimage,
        Scheme.Hom.inv_preimage])

/-- The domain isomorphism evaluates the prefix at the initial center. -/
@[reassoc (attr := simp)]
theorem centerStepDomainIso_hom_ι (w : Word B C) (s : C ⟶ D) (P : ChargeSeed B N) :
    (w.centerStepDomainIso K s P).hom ≫ (w.centerStepPartialMap K s P).domain.ι =
      ((w.cons s).centerPartialMap K P).domain.ι ≫ (w.centerIso K).hom := by
  simp only [centerStepDomainIso, Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι,
    Scheme.Hom.isoImage_hom_ι]

/-- The inverse domain isomorphism recovers the initial center by the inverse
monomial isomorphism of the prefix. -/
@[reassoc (attr := simp)]
theorem centerStepDomainIso_inv_ι (w : Word B C) (s : C ⟶ D) (P : ChargeSeed B N) :
    (w.centerStepDomainIso K s P).inv ≫ ((w.cons s).centerPartialMap K P).domain.ι =
      (w.centerStepPartialMap K s P).domain.ι ≫ (w.centerIso K).inv := by
  rw [← cancel_mono (w.centerIso K).hom, Category.assoc, Category.assoc,
    ← centerStepDomainIso_hom_ι, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- Executing the step after the domain isomorphism evaluates the appended word. -/
@[reassoc (attr := simp)]
theorem centerStepDomainIso_hom_centerStepPartialMap_hom
    (w : Word B C) (s : C ⟶ D) (P : ChargeSeed B N) :
    (w.centerStepDomainIso K s P).hom ≫ (w.centerStepPartialMap K s P).hom =
      ((w.cons s).centerPartialMap K P).hom := by
  rw [centerStepPartialMap_hom, centerStepDomainIso_hom_ι_assoc, centerPartialMap_hom,
    ← Iso.trans_hom, ← centerIso_comp, Path.comp_toPath_eq_cons]

/-- The step reaches exactly the centers obtained by executing the appended word. -/
theorem centerStepPartialMap_opensRange (w : Word B C) (s : C ⟶ D) (P : ChargeSeed B N) :
    (w.centerStepPartialMap K s P).hom.opensRange =
      ((w.cons s).centerPartialMap K P).hom.opensRange := by
  simpa only [centerStepDomainIso_hom_centerStepPartialMap_hom] using
    (Scheme.Hom.opensRange_comp_of_isIso (w.centerStepDomainIso K s P).hom
      (w.centerStepPartialMap K s P).hom).symm

/-- Appending a step composes the prefix with the step on its inherited domain.
The composite is defined on the entire simultaneous noncollision open. -/
theorem centerPartialMap_cons (w : Word B C) (s : C ⟶ D) (P : ChargeSeed B N) :
    (w.cons s).centerPartialMap K P = (w.centerPartialMap K P).comp
      (w.centerStepPartialMap K s P) := by
  let f := w.centerPartialMap K P
  let g := s.toPath.centerPartialMap K (w.chargeTarget P)
  have h := f.comp_restrict_right g (f.hom.opensRange ⊓ g.domain)
    (dense_centerStepDomain w s P) inf_le_right
  have hdom : f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ (f.hom.opensRange ⊓ g.domain)) = (f.comp g).domain := by
    simp only [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange, top_inf_eq,
      Scheme.PartialMap.comp_domain]
  have hrestrict (U : (scheme K A).Opens) (hU : Dense (U : Set (scheme K A)))
      (hle : U ≤ (f.comp g).domain) (heq : U = (f.comp g).domain) :
      (f.comp g).restrict U hU hle = f.comp g := by
    subst U
    exact (f.comp g).restrict_id
  rw [← Path.comp_toPath_eq_cons, centerPartialMap_comp, centerStepPartialMap_eq_restrict]
  exact (h.trans (hrestrict _ _ _ hdom)).symm

/-- Over a separably closed field there is a rational initial center character satisfying
the noncollision conditions at every step. -/
theorem exists_point_mem_centerOpen [IsSepClosed K] (w : Word B C) (P : ChargeSeed B N) :
    ∃ c : Multiplicative A →* Kˣ, ((pointsEquiv K A).symm c).val default ∈ w.centerOpen K P :=
  (denseRange_centerPoints K ι).exists_mem_open (w.centerOpen K P).isOpen
    (w.nonempty_centerOpen P)

end Quiver.Path

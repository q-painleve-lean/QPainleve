/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.PrescribedBlowdown
public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
public import QPainleve.LinearAlgebra.BilinearForm.NegOneProjection
public import TauCeti.AlgebraicGeometry.CartierDivisor.Excision

import Mathlib.Data.List.OfFn
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Class
import QPainleve.AlgebraicGeometry.Chow.Birational
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField

/-!
# Ordered contractions of anticanonical boundary components

Successive Picard elimination tests whether a prescribed list of distinct boundary
components can be blown down at their turns. When every updated class has square
minus one and some component remains, the blowdowns form a nodal boundary tower.
The original labels determine exactly which primes survive the projection.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData LineBundleClass

universe u v w

namespace AlgebraicGeometry.Scheme.NodalCycleNumbering

variable {k : Type u} [Field k]

local notation "S(" k ")" => Spec (CommRingCat.of k)
local notation "K[" k "," X "]" => LineBundleClass.mk (canonicalBundle k X 2)
local notation "g[" k "," X "]" => (X ↘ Spec (CommRingCat.of k))
local notation "B[" k "," X "]" => Chow.intersectionBilinForm k X
local notation "J[" x "]" => vanishingIdeal (Closeds.mk (closure {x}) isClosed_closure)
local notation "Pic" X:arg => Additive (LineBundleClass X)

variable {X : Scheme.{u}} {D : X.IdealSheafData}

local notation "pc[" D "," x "]" => Additive.ofMul (primeDivisorClass (boundaryPrimeEmbedding D x))

private theorem mem_support_vanishingIdeal_boundaryPrime_iff (x y : D.boundaryPrimes) :
    x.val ∈ (J[y.val]).support ↔ x = y := by
  simp only [← SetLike.mem_coe, coe_support_vanishingIdeal, Closeds.coe_mk]
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ subset_closure (Set.mem_singleton _)⟩
  apply D.boundaryPrimeEmbedding.injective
  exact (CodimensionOnePoint.eq_of_specializes (x := D.boundaryPrimeEmbedding x)
    (y := D.boundaryPrimeEmbedding y)
    (specializes_iff_mem_closure.mpr (by simpa only [coe_boundaryPrimeEmbedding] using h))).symm

private noncomputable def eraseBoundaryPrimeEquiv {α : Type w} [DecidableEq α]
    {s : Finset α} (a : s ≃ D.boundaryPrimes) (j : s)
    {Y : Scheme.{u}} {F : Y.IdealSheafData} {f : X ⟶ Y}
    (h : Set.BijOn f (D.boundaryPrimes \ (J[(a j).val]).support) F.boundaryPrimes) :
    (s.erase j.val : Finset α) ≃ F.boundaryPrimes := by
  let e := (Set.equivOfEq (Finset.coe_erase j.val s)).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun x ↦ x ∈ s) (fun x ↦ x ∉ ({j.val} : Set α))).symm
  let b := a.subtypeEquiv (p := fun i ↦ i.val ∉ ({j.val} : Set α))
    (q := fun x ↦ x.val ∉ (J[(a j).val]).support) fun i ↦ by
      rw [Set.mem_singleton_iff, mem_support_vanishingIdeal_boundaryPrime_iff, a.injective.eq_iff]
      exact not_congr Subtype.ext_iff.symm
  let d := Equiv.subtypeSubtypeEquivSubtypeInter
    (fun x ↦ x ∈ D.boundaryPrimes) (fun x ↦ x ∉ (J[(a j).val]).support)
  exact e.trans (b.trans (d.trans (h.equiv f)))

private theorem eraseBoundaryPrimeEquiv_apply_val {α : Type w} [DecidableEq α]
    {s : Finset α} (a : s ≃ D.boundaryPrimes) (j : s)
    {Y : Scheme.{u}} {F : Y.IdealSheafData} {f : X ⟶ Y}
    (h : Set.BijOn f (D.boundaryPrimes \ (J[(a j).val]).support) F.boundaryPrimes)
    (i : (s.erase j.val : Finset α)) :
    (eraseBoundaryPrimeEquiv a j h i).val =
      f (a ⟨i.val, (Finset.mem_erase.mp i.property).2⟩).val := (rfl)

private theorem exists_snoc_numbered_blowdown {Y Z W : Scheme.{u}}
    [Y.Over S(k)] [Z.Over S(k)] {F : Y.IdealSheafData} {G : Z.IdealSheafData}
    {l : ℕ} {T : BlowupTower Z l W}
    (hT : IsNodalBoundaryTower G g[k,Z] (𝟙 Z) T)
    (d : Y ≅ W) (p : Y ⟶ Z) (hd : d.hom ≫ T.toBase = p) [p.IsOver S(k)]
    (hG : (G.comap p).support = F.support)
    {f : X ⟶ Y} {q : Y} (hq : IsClosed ({q} : Set Y))
    (hnode : F.IsNodeOfReducedBoundary g[k,Y] q)
    (e : X ≅ (Y.fromSpecResidueField q).ker.blowup)
    (he : e.hom ≫ (Y.fromSpecResidueField q).ker.blowupToBase = f) :
    let I := (Y.fromSpecResidueField q).ker
    ∃ (J : W.IdealSheafData) (e' : X ≅ J.blowup),
      IsNodalBoundaryTower G g[k,Z] (𝟙 Z) (T.snoc J) ∧ e'.hom ≫ (T.snoc J).toBase = f ≫ p ∧
      (∀ i : Fin l, pullback e'.hom ((T.snoc J).exceptionalClass i.castSucc) =
        pullback f (pullback d.hom (T.exceptionalClass i))) ∧
      pullback e'.hom ((T.snoc J).exceptionalClass (Fin.last l)) =
        pullback e.hom I.blowupExceptionalClass := by
  intro I
  let J := (W.fromSpecResidueField (d.hom q)).ker
  have hIJ : J.comap d.hom = I := d.hom.comap_ker_fromSpecResidueField_apply q
  let b := blowupIso d hIJ.symm
  have hb : b.hom ≫ J.blowupToBase = I.blowupToBase ≫ d.hom :=
    blowupIso_hom_blowupToBase d hIJ.symm
  have hbClass : pullback b.hom J.blowupExceptionalClass = I.blowupExceptionalClass :=
    J.pullback_blowupExceptionalClass d hIJ
  have hq' : IsClosed ({d.hom q} : Set W) := by
    simpa only [Set.image_singleton] using d.hom.isClosedMap _ hq
  have hnode' : ((G.comap T.toBase).comap d.hom).IsNodeOfReducedBoundary
      (d.hom ≫ T.toBase ≫ g[k,Z]) q := by
    rw [← comap_comp, hd, ← Category.assoc, hd, comp_over, ← isNodeOfReducedBoundary_radical,
      ← vanishingIdeal_support, hG, vanishingIdeal_support, isNodeOfReducedBoundary_radical]
    exact hnode
  have hnodeW := ((G.comap T.toBase).isNodeOfReducedBoundary_comap_iff_of_isOpenImmersion
    (T.toBase ≫ g[k,Z]) d.hom q).mp hnode'
  refine ⟨J, e ≪≫ b, hT.snoc (d.hom q) hq' rfl
    (by simpa only [Category.comp_id] using hnodeW), ?_, ?_, ?_⟩
  · calc
      (e ≪≫ b).hom ≫ (T.snoc J).toBase =
          (e.hom ≫ I.blowupToBase) ≫ (d.hom ≫ T.toBase) := by
        simp only [Iso.trans_hom, toBase_snoc, Category.assoc, b, blowupIso_hom_blowupToBase_assoc]
      _ = f ≫ p := by rw [he, hd]
  · intro i
    rw [exceptionalClass_snoc_castSucc, pullback_comp, Iso.trans_hom, Category.assoc,
      hb, ← Category.assoc, he, pullback_comp]
  · rw [exceptionalClass_snoc_last, ← blowupExceptionalClass_def, Iso.trans_hom, ← pullback_comp,
      hbClass]

private theorem pullback_primeDivisorClass_eraseBoundaryPrimeEquiv
    {α : Type w} [DecidableEq α] {s : Finset α} (a : s ≃ D.boundaryPrimes) (j : s)
    {Y : Scheme.{u}} {F : Y.IdealSheafData} {f : X ⟶ Y}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]
    (h : Set.BijOn f (D.boundaryPrimes \ (J[(a j).val]).support) F.boundaryPrimes)
    {β : Type*} (b : β ≃ D.boundaryPrimes) (l : β) (hl : b l = a j)
    (B : LinearMap.BilinForm ℤ (Pic X))
    (hprime : ∀ t ≠ l, ∃ r : F.boundaryPrimes, f (b t).val = r.val ∧
      Additive.ofMul (pullback f (primeDivisorClass (F.boundaryPrimeEmbedding r))) =
        B.projectOffNegOne (pc[D,b l]) (pc[D,b t]))
    (i : (s.erase j.val : Finset α)) :
    let i' : s := ⟨i.val, (Finset.mem_erase.mp i.property).2⟩
    Additive.ofMul (pullback f (primeDivisorClass
      (F.boundaryPrimeEmbedding (eraseBoundaryPrimeEquiv a j h i)))) =
      B.projectOffNegOne (pc[D,a j]) (pc[D,a i']) := by
  intro i'
  let t := b.symm (a i')
  have ht : b t = a i' := b.apply_symm_apply _
  have hne : t ≠ l := by
    intro htl
    have hlabel : i' = j := a.injective (ht.symm.trans ((congrArg b htl).trans hl))
    exact (Finset.mem_erase.mp i.property).1 (congrArg Subtype.val hlabel)
  obtain ⟨r, hr, hrClass⟩ := hprime t hne
  have hr' : r = eraseBoundaryPrimeEquiv a j h i := Subtype.ext (hr.symm.trans
    ((congrArg (fun z : D.boundaryPrimes ↦ f z.val) ht).trans
      (eraseBoundaryPrimeEquiv_apply_val a j h i).symm))
  simpa only [hr', ht, hl] using hrClass

private theorem comp_mem_boundaryPrimes_iff_of_erase {α : Type w} [DecidableEq α]
    {s : Finset α} (a : s ≃ D.boundaryPrimes) (j : s)
    {Y Z : Scheme.{u}} {F : Y.IdealSheafData} {G : Z.IdealSheafData}
    {f : X ⟶ Y} {p : Y ⟶ Z} {z : Z ⟶ S(k)} [SmoothOfRelativeDimension 2 z]
    (h : Set.BijOn f (D.boundaryPrimes \ (J[(a j).val]).support) F.boundaryPrimes)
    {q : Y} (hq : IsClosed ({q} : Set Y)) (hp : IsClosedMap p)
    (hExc : (Y.fromSpecResidueField q).ker.comap f = J[(a j).val])
    {c : List α}
    (hsurv : ∀ i : s.erase j.val, p (eraseBoundaryPrimeEquiv a j h i).val ∈ G.boundaryPrimes ↔
      i.val ∉ c) (i : s) :
    (f ≫ p) (a i).val ∈ G.boundaryPrimes ↔ i.val ∉ j.val :: c := by
  by_cases hi : i.val = j.val
  · have heq : i = j := Subtype.ext hi
    have hfq : f (a j).val = q := by
      have hx := (mem_support_vanishingIdeal_boundaryPrime_iff (a j) (a j)).mpr rfl
      rwa [← hExc, support_comap, ← SetLike.mem_coe, Closeds.coe_preimage,
        Scheme.support_ker_fromSpecResidueField_of_isClosed hq, Set.mem_preimage,
        Set.mem_singleton_iff] at hx
    have hclosed : IsClosed ({p q} : Set Z) := by
      simpa only [Set.image_singleton] using hp _ hq
    have hcoheight := coheight_eq_of_isClosed_of_smoothOfRelativeDimension (n := 2) z hclosed
    rw [heq, Scheme.Hom.comp_apply, hfq]
    refine iff_of_false (fun h ↦ ?_) (not_not_intro (List.mem_cons_self ..))
    exact (by decide : (2 : ℕ∞) ≠ 1) (hcoheight.symm.trans (mem_boundaryPrimes.mp h).2)
  · let i' : s.erase j.val := ⟨i.val, Finset.mem_erase.mpr ⟨hi, i.property⟩⟩
    simpa only [eraseBoundaryPrimeEquiv_apply_val, Scheme.Hom.comp_apply, List.mem_cons,
      hi, false_or] using hsurv i'

private theorem exists_ordered_blowdown [IsAlgClosed k] [NeZero (2 : k)]
    {X : Scheme.{u}} [X.Over S(k)] [X.IsProjectiveOver k] [IsIntegral X]
    [SmoothOfRelativeDimension 2 g[k,X]] [Scheme.IsRationalOver g[k,X]] [IsNoetherian X]
    [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S(k))]
    {ι : Type v} {marks : ι → (D.subscheme ↘ S(k)).smoothLocus}
    {n : ℕ} [NeZero n] (A : NodalCycleNumbering marks n) (hD : D.IsEffectiveCartier)
    {α : Type w} {s : Finset α} (a : s ≃ D.boundaryPrimes)
    (hcan : LineBundleClass.mk hD.toInvertibleSheaf = K[k,X])
    {M : Type*} [AddCommGroup M] [Module ℤ M] (B : LinearMap.BilinForm ℤ M)
    (m : Pic X →ₗ[ℤ] M) (hm : ∀ x y, B (m x) (m y) = B[k,X] x y)
    (C : α → M) (hC : ∀ i : s, C i.val = m (pc[D,a i]))
    (c : List α) (hnodup : c.Nodup) (hmem : ∀ j ∈ c, j ∈ s)
    (hlen : c.length < s.card)
    (hsq : ∀ v ∈ B.orthogonalizeNegOnes (c.map C), B v v = -1) :
    ∃ (Z : Scheme.{u}) (z : Z ⟶ S(k)) (p : X ⟶ Z),
      let : Z.Over S(k) := ⟨z⟩
      ∃ (_ : IsIntegral Z) (_ : Z.IsProjectiveOver k) (_ : SmoothOfRelativeDimension 2 g[k,Z]),
        Scheme.IsRationalOver g[k,Z] ∧ p.IsOver S(k) ∧
        ∃ (G : Z.IdealSheafData) (hG : G.IsEffectiveCartier)
          (_ : PrestableFamily (G.subscheme ↘ S(k))),
          LineBundleClass.mk hG.toInvertibleSheaf = K[k,Z] ∧
          (G.comap p).support = D.support ∧
          (∀ i : s, p (a i).val ∈ G.boundaryPrimes ↔ i.val ∉ c) ∧
          ∃ (W : Scheme.{u}) (T : BlowupTower Z c.length W) (e : X ≅ W),
            IsNodalBoundaryTower G g[k,Z] (𝟙 Z) T ∧ e.hom ≫ T.toBase = p ∧
            (List.ofFn fun i ↦ m (Additive.ofMul (pullback e.hom (T.exceptionalClass i)))) =
              (B.orthogonalizeNegOnes (c.map C)).reverse := by
  classical
  cases c with
  | nil =>
    refine ⟨X, g[k,X], 𝟙 X, ‹_›, ‹_›, ‹_›, ‹_›, ⟨Category.id_comp _⟩, D, hD, ‹_›, hcan, ?_,
      fun i ↦ by simp [(a i).property], X, .nil, Iso.refl _, .nil, ?_, ?_⟩
    · rw [comap_id]
    · simp
    · simp
  | cons j c =>
    -- Keep the tests in the original Picard lattice. Each step replaces the comparison
    -- map by its composition with the new pullback and erases one active label.
    simp only [List.map_cons, LinearMap.BilinForm.orthogonalizeNegOnes_cons, List.mem_cons,
      forall_eq_or_imp] at hsq
    let j' : s := ⟨j, hmem j (List.mem_cons_self ..)⟩
    let l := (A.boundaryPrimeEquiv hD).symm (a j')
    have hl : A.boundaryPrimeEquiv hD l = a j' := (A.boundaryPrimeEquiv hD).apply_symm_apply _
    have hcard : s.card = n := by
      have := Fintype.card_congr (a.trans (A.boundaryPrimeEquiv hD).symm)
      simpa only [Fintype.card_coe, ZMod.card] using this
    have hlsq : B[k,X] (pc[D,A.boundaryPrimeEquiv hD l]) (pc[D,A.boundaryPrimeEquiv hD l]) = -1 :=
      hl ▸ (hm _ _).symm.trans (by simpa only [← hC j'] using hsq.1)
    obtain ⟨Y, y, f, q, hY, hproj, hsm, hRat, hf, hmod, hq, hExc, e, he,
      hF, hpre, hK, hnode, htot, hbij, ⟨n', hn', _, A', _, _, _⟩, -, hprime⟩ :=
      A.exists_numbered_nodal_boundary_blowdown_of_selfIntersection hD hcan
        (by rw [← hcard]; simp only [List.length_cons] at hlen; omega) l hlsq
    let : Y.Over S(k) := ⟨y⟩
    let : IsIntegral Y := hY
    let : Y.IsProjectiveOver k := hproj
    let : SmoothOfRelativeDimension 2 g[k,Y] := hsm
    let : Scheme.IsRationalOver g[k,Y] := hRat
    let : f.IsOver S(k) := hf
    let : IsModification f := hmod
    let : IsNoetherian Y := isNoetherian_of_finiteType g[k,Y]
    let := g[k,Y].uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let F := D.map f
    let : PrestableFamily (F.subscheme ↘ S(k)) := hpre
    let : NeZero n' := hn'
    let E := J[(D.boundaryPrimeEmbedding (a j') : X)]
    have hExc' : (Y.fromSpecResidueField q).ker.comap f = E := by
      simpa only [E, coe_boundaryPrimeEmbedding, hl] using hExc
    have htot' : (F.comap f).support = D.support := by
      rw [htot, support_mul, hl, sup_eq_left.mpr]
      exact closure_minimal (Set.singleton_subset_iff.mpr (mem_boundaryPrimes.mp (a j').property).1)
        D.support.isClosed
    have hbij' : Set.BijOn f (D.boundaryPrimes \ (J[(a j').val]).support) F.boundaryPrimes :=
      by simpa only [F, hl] using hbij
    let a' := eraseBoundaryPrimeEquiv a j' hbij'
    let m' := m.comp (pullbackHom f).toAdditive.toIntLinearMap
    have hm' : ∀ x y, B (m' x) (m' y) = B[k,Y] x y := by
      intro x y
      simpa only [m', LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap,
        MonoidHom.coe_toAdditive, Function.comp_apply, pullbackHom_apply, hm,
        Chow.intersectionBilinForm_apply, toMul_ofMul] using
        f.classIntersectionNumber_pullback_of_birational (k := k)
          (IsModification.birationalOver f) x.toMul y.toMul
    let C' := B.projectOffNegOne (C j) ∘ C
    have hC' : ∀ i : s.erase j, C' i.val = m' (pc[F,a' i]) := by
      intro i
      let i' : s := ⟨i.val, (Finset.mem_erase.mp i.property).2⟩
      have hiC : C i.val = m (pc[D,a i']) := hC i'
      have hjC : C j = m (pc[D,a j']) := hC j'
      have hpull := pullback_primeDivisorClass_eraseBoundaryPrimeEquiv a j' hbij'
        (A.boundaryPrimeEquiv hD) l hl (B[k,X])
        (fun t ht ↦ by simpa only [LinearMap.BilinForm.projectOffNegOne_apply] using hprime t ht) i
      simp only [C', Function.comp_apply, LinearMap.BilinForm.projectOffNegOne_apply, hiC, hjC, hm,
        m', LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditive,
        pullbackHom_apply, toMul_ofMul, a']
      rw [hpull, LinearMap.BilinForm.projectOffNegOne_apply, map_add, m.map_smul]
    have hnmem := (List.nodup_cons.mp hnodup).1
    obtain ⟨Z, z, p, hZ, hprojZ, hsmZ, hRatZ, hp, G, hG, hpreG, hKZ, hsupp, hsurv,
      W, T, d, hT, hd, hclasses⟩ := exists_ordered_blowdown A' hF a' hK B m' hm' C' hC' c
        (List.nodup_cons.mp hnodup).2
        (fun i hi ↦ Finset.mem_erase.mpr
          ⟨fun h ↦ hnmem (by simpa only [h] using hi), hmem i (List.mem_cons_of_mem _ hi)⟩)
        (by rw [Finset.card_erase_of_mem j'.property]; simp only [List.length_cons] at hlen; omega)
        (by simpa only [C', List.map_map] using hsq.2)
    let : Z.Over S(k) := ⟨z⟩
    let : IsIntegral Z := hZ
    let : Z.IsProjectiveOver k := hprojZ
    let : SmoothOfRelativeDimension 2 g[k,Z] := hsmZ
    let : p.IsOver S(k) := hp
    -- The first contraction becomes the last blowup of the tower for the tail.
    obtain ⟨J, e', hU, he', hprior, hlast⟩ :=
      exists_snoc_numbered_blowdown hT d p hd hsupp hq hnode e he
    refine ⟨Z, z, f ≫ p, hZ, hprojZ, hsmZ, hRatZ, inferInstance, G, hG, hpreG, hKZ,
      by rw [comap_comp, support_comap, hsupp, ← support_comap, htot'],
      ?_, J.blowup, T.snoc J, e', hU, he', ?_⟩
    · have hproper : IsProper p := by
        let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g[k,Z]
        let : IsProper T.toBase := T.isProper_toBase
        rw [← hd]
        infer_instance
      exact comp_mem_boundaryPrimes_iff_of_erase (z := g[k,Z]) a j' hbij' hq p.isClosedMap
        (by simpa only [hl] using hExc) hsurv
    · let I := (Y.fromSpecResidueField q).ker
      have hE : E.IsEffectiveCartier :=
        isEffectiveCartier_vanishingIdeal_closure_singleton
          (D.boundaryPrimeEmbedding (a j')).property
      have hlast' : pullback e.hom I.blowupExceptionalClass =
          primeDivisorClass (D.boundaryPrimeEmbedding (a j')) := by
        rw [primeDivisorClass_def]
        exact I.pullback_blowupExceptionalClass_of_comap_eq e.hom hE
          (by rw [← comap_comp, he, hExc'])
      rw [List.ofFn_succ', hlast, hlast', ← hC j', List.map_cons,
        LinearMap.BilinForm.orthogonalizeNegOnes_cons, List.reverse_cons']
      have hprior' (i : Fin c.length) :
          m (Additive.ofMul (pullback e'.hom ((T.snoc J).exceptionalClass i.castSucc))) =
            m' (Additive.ofMul (pullback d.hom (T.exceptionalClass i))) := by
        simp only [hprior, m', LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap,
          MonoidHom.coe_toAdditive, Function.comp_apply, toMul_ofMul, pullbackHom_apply]
      simp only [hprior', hclasses, List.map_map, C', j']
termination_by c.length

variable [IsAlgClosed k]

variable [X.Over S(k)] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 g[k,X]] [Scheme.IsRationalOver g[k,X]]
  [PrestableFamily (D.subscheme ↘ S(k))]
  {ι : Type v} {marks : ι → (D.subscheme ↘ S(k)).smoothLocus}
  {n : ℕ} [NeZero n] (A : NodalCycleNumbering marks n) (hD : D.IsEffectiveCartier)

include A hD in
/-- A list of distinct numbered components of an anticanonical boundary with square
minus one at each successive Picard update is realized by nodal blowdowns, provided
at least one component remains. The resulting projection preserves the boundary
support under inverse image and takes exactly the unlisted primes to boundary primes.
The tower's total exceptional classes are the updated contracted classes in reverse
order because the tower builds the original surface by blowing up the contracted one. -/
theorem exists_nodal_boundary_tower_of_ordered_contractions [NeZero (2 : k)]
    (hcan : LineBundleClass.mk hD.toInvertibleSheaf = K[k,X])
    (c : List (ZMod n)) (hnodup : c.Nodup) (hlen : c.length < n)
    (hsq :
      letI := isNoetherian_of_finiteType g[k,X]
      letI := g[k,X].uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      ∀ v ∈ (B[k,X]).orthogonalizeNegOnes
        (c.map fun i ↦ pc[D,A.boundaryPrimeEquiv hD i]), B[k,X] v v = -1) :
    letI := isNoetherian_of_finiteType g[k,X]
    letI := g[k,X].uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    ∃ (Z : Scheme.{u}) (z : Z ⟶ S(k)) (p : X ⟶ Z),
      let : Z.Over S(k) := ⟨z⟩
      ∃ (_ : IsIntegral Z) (_ : Z.IsProjectiveOver k) (_ : SmoothOfRelativeDimension 2 g[k,Z]),
        Scheme.IsRationalOver g[k,Z] ∧ p.IsOver S(k) ∧
        ∃ (G : Z.IdealSheafData) (hG : G.IsEffectiveCartier)
          (_ : PrestableFamily (G.subscheme ↘ S(k))),
          LineBundleClass.mk hG.toInvertibleSheaf = K[k,Z] ∧
          (G.comap p).support = D.support ∧
          (∀ i : ZMod n, p (A.boundaryPrimeEquiv hD i).val ∈ G.boundaryPrimes ↔ i ∉ c) ∧
          ∃ (W : Scheme.{u}) (T : BlowupTower Z c.length W) (e : X ≅ W),
            IsNodalBoundaryTower G g[k,Z] (𝟙 Z) T ∧ e.hom ≫ T.toBase = p ∧
            (List.ofFn fun i ↦ Additive.ofMul (pullback e.hom (T.exceptionalClass i))) =
              ((B[k,X]).orthogonalizeNegOnes
                (c.map fun i ↦ pc[D,A.boundaryPrimeEquiv hD i])).reverse := by
  let : IsNoetherian X := isNoetherian_of_finiteType g[k,X]
  let := g[k,X].uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let a := (Equiv.subtypeUnivEquiv (fun i : ZMod n ↦ Finset.mem_univ i)).trans
    (A.boundaryPrimeEquiv hD)
  obtain ⟨Z, z, p, hZ, hproj, hsm, hRat, hp, G, hG, hpre, hK, hsupp, hsurv,
    W, T, e, hT, he, hclasses⟩ :=
    exists_ordered_blowdown A hD (s := Finset.univ) a hcan (B[k,X]) LinearMap.id
      (fun _ _ ↦ rfl) (fun i ↦ pc[D,A.boundaryPrimeEquiv hD i]) (fun _ ↦ rfl) c hnodup
      (fun _ _ ↦ Finset.mem_univ _) (by simpa only [Finset.card_univ, ZMod.card] using hlen) hsq
  exact ⟨Z, z, p, hZ, hproj, hsm, hRat, hp, G, hG, hpre, hK, hsupp,
    (fun i ↦ hsurv ⟨i, Finset.mem_univ i⟩), W, T, e, hT, he,
    by simpa only [LinearMap.id_apply] using hclasses⟩

end AlgebraicGeometry.Scheme.NodalCycleNumbering

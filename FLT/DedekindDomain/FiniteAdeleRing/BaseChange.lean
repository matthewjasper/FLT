/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.Mathlib.Algebra.Algebra.Bilinear
import FLT.Mathlib.Algebra.Algebra.Pi
import FLT.Mathlib.Algebra.Module.Submodule.Basic
import FLT.Mathlib.NumberTheory.RamificationInertia.Basic
import FLT.Mathlib.Topology.Algebra.Module.Equiv
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.Topology.Algebra.RestrictedProduct
import FLT.Mathlib.Topology.Algebra.UniformRing
import FLT.Mathlib.Topology.Algebra.Valued.ValuationTopology
import FLT.Mathlib.Topology.Algebra.Valued.WithVal
import FLT.Mathlib.RingTheory.TensorProduct.Basis
import FLT.Mathlib.RingTheory.Finiteness.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Data.Int.WithZero
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Topology.Algebra.Algebra.Equiv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Module.FiniteDimension
import FLT.DedekindDomain.AdicValuation
import FLT.DedekindDomain.Completion.BaseChange
import FLT.DedekindDomain.FiniteAdeleRing.TensorRestrictedProduct

/-!

# Base change of adele rings.

If `A` is a Dedekind domain with field of fractions `K`, if `L/K` is a finite separable
extension and if `B` is the integral closure of `A` in `L`, then `B` is also a Dedekind
domain. Hence the rings of finite adeles `𝔸_K^∞` and `𝔸_L^∞` (defined using `A` and `B`)
are defined. In this file we define the natural `K`-algebra map `𝔸_K^∞ → 𝔸_L^∞` and
the natural `L`-algebra map `𝔸_K^∞ ⊗[K] L → 𝔸_L^∞`, and show that the latter map
is an isomorphism.

## Main definitions

* `FiniteAdeleRing.baseChangeEquiv : L ⊗[K] FiniteAdeleRing A K ≃ₐ[L] FiniteAdeleRing B L`

## Main theorems

* `BaseChange.isModuleTopology` : `FiniteAdeleRing B L` has the
  `FiniteAdeleRing A K`-module topology.

-/

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [FiniteDimensional K L] [Module.Finite A B]
    [IsDedekindDomain B] [IsFractionRing B L]

namespace IsDedekindDomain

open IsDedekindDomain HeightOneSpectrum

open scoped TensorProduct -- ⊗ notation for tensor product

lemma tendsTo_comap_confinite [FaithfulSMul A B] :
    Filter.Tendsto (comap A (B:=B)) Filter.cofinite Filter.cofinite :=
  have : FaithfulSMul A (FractionRing B) := FractionRing.instFaithfulSMul A B
  letI : Algebra (FractionRing A) (FractionRing B) :=
    FractionRing.liftAlgebra A (FractionRing B)
  (Filter.Tendsto.cofinite_of_finite_preimage_singleton <|
    Extension.finite A (FractionRing A) (FractionRing B) B)

omit [IsIntegralClosure B A L] [FiniteDimensional K L] in
lemma confinite_mapsTo_adicCompletionComapSemialgHom :
    ∀ᶠ (w : HeightOneSpectrum B) in Filter.cofinite,
    Set.MapsTo (adicCompletionComapSemialgHom A K L B (comap A w) w rfl)
      (adicCompletionIntegers K (comap A w)) (adicCompletionIntegers L w) := by
  apply Filter.Eventually.of_forall
  intro w
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  have := adicCompletionComapSemialgHom.mapadicCompletionIntegers A K L B (comap A w) w rfl
  exact Set.image_subset_iff.1 this

/-- The ring homomorphism `𝔸_K^∞ → 𝔸_L^∞` for `L/K` an extension of number fields.-/
noncomputable def FiniteAdeleRing.mapRingHom :
    FiniteAdeleRing A K →+* FiniteAdeleRing B L :=
  have := FaithfulSMul.of_field_isFractionRing A B K L;
  RestrictedProduct.mapRingHom
    (fun (v : HeightOneSpectrum A) ↦ v.adicCompletion K)
    (fun (w : HeightOneSpectrum B) ↦ w.adicCompletion L)
    (HeightOneSpectrum.comap A)
    (tendsTo_comap_confinite A B)
    (fun w ↦ adicCompletionComapSemialgHom A K L B (w.comap A) w rfl)
    (confinite_mapsTo_adicCompletionComapSemialgHom A K L B)

/-- The ring homomorphism `𝔸_K^∞ → 𝔸_L^∞` for `L/K` an extension of number fields,
as a morphism lying over the canonical map `K → L`. -/
noncomputable def FiniteAdeleRing.mapSemialgHom :
    FiniteAdeleRing A K →ₛₐ[algebraMap K L] FiniteAdeleRing B L where
      __ := FiniteAdeleRing.mapRingHom A K L B
      map_smul' k a := by
        ext w
        simpa only [Algebra.smul_def'] using
          (adicCompletionComapSemialgHom A K L B (comap A w) w rfl).map_smul' k (a (comap A w))

open scoped TensorProduct.RightActions

noncomputable
instance BaseChange.algebra : Algebra (FiniteAdeleRing A K) (FiniteAdeleRing B L) :=
  RingHom.toAlgebra (FiniteAdeleRing.mapRingHom A K L B)

omit [IsIntegralClosure B A L] [FiniteDimensional K L] in
lemma FiniteAdeleRing.mapSemialgHom_continuous : Continuous (mapSemialgHom A K L B) := by
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  apply Continuous.restrictedProduct_map (tendsTo_comap_confinite A B)
    (confinite_mapsTo_adicCompletionComapSemialgHom A K L B)
  intro w
  apply adicCompletionComapSemialgHom_continuous A K L B _ w rfl

attribute [instance 100] RestrictedProduct.instSMulCoeOfSMulMemClass
-- otherwise
-- #synth SMul (FiniteAdeleRing A K) (FiniteAdeleRing B L)
-- spends 2 seconds failing to find `SMul (FiniteAdeleRing A K) (adicCompletion L w)

noncomputable instance baseChangeAlgebra : Algebra K (FiniteAdeleRing B L) :=
  Algebra.compHom _ (algebraMap K L)

noncomputable instance baseChangeScalarTower : IsScalarTower K L (FiniteAdeleRing B L) :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable instance baseChangeScalarTower' :
    IsScalarTower K (FiniteAdeleRing A K) (FiniteAdeleRing B L) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  nth_rw 2 [RingHom.algebraMap_toAlgebra]
  symm
  exact SemialgHom.commutes (FiniteAdeleRing.mapSemialgHom A K L B) x

noncomputable instance : TopologicalSpace (L ⊗[K] FiniteAdeleRing A K) :=
  moduleTopology (FiniteAdeleRing A K) (L ⊗[K] FiniteAdeleRing A K)

omit [Module.Finite A B] [IsDedekindDomain B] in
theorem range_adicCompletionTensorIntegerCoe_eq_lTensorRestriction (v : HeightOneSpectrum A) :
    LinearMap.range (adicCompletionTensorIntegerCoe A K B v) =
    RestrictedProduct.lTensorRestriction A B (adicCompletion K) (integerSubmodule A K) v := by
  rfl

noncomputable def FiniteAdeleRing.tensor_equiv_tensor :
    L ⊗[K] FiniteAdeleRing A K ≃ₗ[A] B ⊗[A] FiniteAdeleRing A K := by
  exact LinearEquivTensorProductModule A K L B (FiniteAdeleRing A K)

open scoped RestrictedProduct in
noncomputable def FiniteAdeleRing.tensor_equiv_restrictedProduct :
    B ⊗[A] FiniteAdeleRing A K ≃ₗ[A]
      Πʳ v, [B ⊗[A] (adicCompletion K v), RestrictedProduct.lTensorRestriction A
      B (adicCompletion K) (integerSubmodule A K) v]_[Filter.cofinite] := by
  have := Module.finitePresentation_of_finite A B
  have := noZeroSMulDivisors A K L B
  let map :=
    RestrictedProduct.lTensor_equiv A B (adicCompletion K) Filter.cofinite (integerSubmodule A K)
  apply LinearEquiv.trans (TensorProduct.congr (LinearEquiv.refl A B) _) map
  have : ∀ (v : HeightOneSpectrum A), AddSubmonoidClass (ValuationSubring (adicCompletion K v))
    (adicCompletion K v) := by infer_instance
  let f : FiniteAdeleRing A K ≃+
      Πʳ (i : HeightOneSpectrum A), [adicCompletion K i, ↑(integerSubmodule A K i)] :=
    AddEquiv.restrictedProductCongrRight
      (fun v ↦ AddEquiv.refl (adicCompletion K v))
      (by
        apply Filter.Eventually.of_forall
        intro v
        apply Set.bijOn_id)
  exact {
    __ := f
    map_smul' a x := by
      ext v
      change _ = (a • (f x v))
      rw [Algebra.smul_def, Algebra.smul_def]
      rfl
  }

noncomputable instance baseChangeIntegerAlgebra : Algebra A (FiniteAdeleRing B L) :=
  RingHom.toAlgebra <| (algebraMap B _).comp (algebraMap A B)

noncomputable def baseChangeIntegerAlgebra' (w : HeightOneSpectrum B) :
    Algebra A (adicCompletion L w) :=
  by exact instAlgebraAdicCompletion B L w

open scoped RestrictedProduct in
noncomputable def FiniteAdeleRing.restrictedProduct_tensorProduct_equiv_restrictedProduct_prod :
    Πʳ v, [B ⊗[A] (adicCompletion K v), RestrictedProduct.lTensorRestriction A
      B (adicCompletion K) (integerSubmodule A K) v]_[Filter.cofinite] ≃ₗ[A]
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
      Submodule.pi Set.univ fun (w : Extension B v) ↦ (integerSubmodule B L w.val).restrictScalars A
      ]_[Filter.cofinite] :=
  LinearEquiv.restrictedProductCongrRight
    (adicCompletionComapIntegerLinearEquiv A K L B)
    (Filter.Eventually.of_forall <| adicCompletionComapIntegerLinearEquiv_bijOn A K L B)

open scoped RestrictedProduct in
noncomputable def FiniteAdeleRing.restrictedProduct_prod_equiv :
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
    Submodule.pi Set.univ fun (w : Extension B v) ↦ (integerSubmodule B L w.val).restrictScalars A
    ]_[Filter.cofinite] ≃ₗ[A] FiniteAdeleRing B L := by
  have := noZeroSMulDivisors A K L B
  let g' : FiniteAdeleRing B L ≃+ Πʳ (w : HeightOneSpectrum B),
      [adicCompletion L w, (integerSubmodule B L w).restrictScalars A] :=
    AddEquiv.restrictedProductCongrRight
      (fun w ↦ AddEquiv.refl (adicCompletion L w))
      (by
        apply Filter.Eventually.of_forall
        intro v
        apply Set.bijOn_id)
  let g : FiniteAdeleRing B L ≃ₗ[A] Πʳ (w : HeightOneSpectrum B),
      [adicCompletion L w, (integerSubmodule B L w).restrictScalars A] := {
    __ := g'
    map_smul' a x := by
      ext w
      change (a • x) w = (a • (x w))
      rw [← IsScalarTower.algebraMap_smul B a (x w), Algebra.smul_def, Algebra.smul_def]
      rfl
  }
  let f : Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
      Submodule.pi Set.univ fun (w : Extension B v) ↦ (integerSubmodule B L w.val).restrictScalars A
      ]_[Filter.cofinite] →ₗ[A] Πʳ (w : HeightOneSpectrum B),
      [adicCompletion L w, (integerSubmodule B L w).restrictScalars A] :=
    RestrictedProduct.mapLinearMap
      (fun v ↦ (w : Extension B v) → adicCompletion L w.val)
      (fun w ↦ adicCompletion L w) (comap A) (tendsTo_comap_confinite A B)
      (fun w ↦
        let w₁ : Extension B (comap A w) := ⟨w, rfl⟩
        LinearMap.proj w₁)
      (by
        apply Filter.Eventually.of_forall
        intro w x hx
        exact hx ⟨w, rfl⟩ ⟨⟩)
  have hf : Function.Bijective f := by
    constructor
    . rw [injective_iff_map_eq_zero]
      intro a ha
      ext v w
      obtain ⟨w, rfl⟩ := w
      exact RestrictedProduct.ext_iff.mp ha w
    . intro x
      refine ⟨⟨fun v ↦ (fun w ↦ x w.val), ?_⟩, rfl⟩
      have hf := x.prop
      rw [Filter.eventually_cofinite, Set.Finite] at ⊢ hf
      have hf' := @Finite.Set.finite_image _ _ _ (comap A) hf
      convert hf'
      ext v
      simp only [Submodule.coe_pi, Submodule.coe_restrictScalars, Set.mem_pi, Set.mem_univ,
        SetLike.mem_coe, forall_const, not_forall, Set.mem_setOf_eq, Set.mem_image]
      constructor
      . exact fun ⟨w, hw⟩ ↦ ⟨w.val, hw, w.prop⟩
      . exact fun ⟨w, hw, wprop⟩ ↦ ⟨⟨w, wprop⟩, hw⟩
  apply LinearEquiv.trans (LinearEquiv.ofBijective f hf) g.symm

noncomputable def FiniteAdeleRing.baseChangeLinearEquiv :
    L ⊗[K] FiniteAdeleRing A K ≃ₗ[K] FiniteAdeleRing B L :=
  have : IsScalarTower A K (FiniteAdeleRing B L) := by
    have : IsScalarTower A B (FiniteAdeleRing B L) := IsScalarTower.of_algebraMap_eq' rfl
    apply IsScalarTower.of_algebraMap_eq
    intro x
    nth_rw 2 [RingHom.algebraMap_toAlgebra]
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A B (FiniteAdeleRing B L),
      ← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L]
    rfl
  let f := (FiniteAdeleRing.tensor_equiv_tensor A K L B).trans
    (FiniteAdeleRing.tensor_equiv_restrictedProduct A K L B) |>.trans
    (FiniteAdeleRing.restrictedProduct_tensorProduct_equiv_restrictedProduct_prod A K L B)
    |>.trans ((FiniteAdeleRing.restrictedProduct_prod_equiv A K L B).restrictScalars A)
  LinearEquiv.extendScalarsOfIsLocalization (nonZeroDivisors A) K f

theorem FiniteAdeleRing.baseChange_bijective :
    Function.Bijective (SemialgHom.baseChange_of_algebraMap <|
      FiniteAdeleRing.mapSemialgHom A K L B) := by
  suffices ⇑(SemialgHom.baseChange_of_algebraMap <|
      FiniteAdeleRing.mapSemialgHom A K L B) =
      ⇑(FiniteAdeleRing.baseChangeLinearEquiv A K L B) by
      rw [this]
      exact (FiniteAdeleRing.baseChangeLinearEquiv A K L B).bijective
  have : IsScalarTower K L (FiniteAdeleRing B L) := by
    apply IsScalarTower.of_algebraMap_eq' rfl
  show ⇑((SemialgHom.baseChange_of_algebraMap <| FiniteAdeleRing.mapSemialgHom A K L B
        ).toLinearMap.restrictScalars K) =
      ⇑((FiniteAdeleRing.baseChangeLinearEquiv A K L B).toLinearMap)
  apply congr_arg
  have : IsLocalizedModule (nonZeroDivisors A) ((Algebra.linearMap B L).restrictScalars A) := by
    have hlocal := IsIntegralClosure.isLocalization A K L B
    rw [← isLocalizedModule_iff_isLocalization'] at hlocal
    exact {
      map_units x := by
        obtain ⟨x, hx⟩ := x
        simpa only [← IsScalarTower.algebraMap_apply, Module.End.isUnit_iff]
            using hlocal.map_units ⟨_, x, hx, rfl⟩
      surj' y := by
        obtain ⟨⟨b, _, s, hs, rfl⟩, hx⟩ := (hlocal.surj) y
        exact ⟨(b, ⟨s, hs⟩), by simpa [Submonoid.smul_def] using hx⟩
      exists_of_eq {x₁ x₂} e := by
        obtain ⟨⟨_, c, hc, rfl⟩, he⟩ := hlocal.exists_of_eq e
        use ⟨c, hc⟩
        simpa only [Submonoid.smul_def, smul_eq_mul, Algebra.smul_def] using he
    }
  apply IsLocalization.tensorProduct_ext (B:=B) (nonZeroDivisors A) K L
  intro x y
  ext w
  letI := comap_algebra A K L B (rfl : (comap A w) = (comap A w))
  show (algebraMap _ (adicCompletion L w) x) *
    (algebraMap _ (adicCompletion L w) (y (comap A w))) = _
  simp only [baseChangeLinearEquiv, Submodule.coe_pi, Submodule.coe_restrictScalars,
    tensor_equiv_tensor, LinearEquiv.coe_coe, LinearEquiv.extendScalarsOfIsLocalization_apply,
    LinearEquiv.trans_apply, LinearEquivTensorProductModule_tmul, LinearEquiv.restrictScalars_apply]
  show _ = (adicCompletionComapIntegerLinearEquiv A K L B (comap A w) (x ⊗ₜ[A] (y (comap A w))))
    ⟨w, rfl⟩
  rw [adicCompletionComapIntegerLinearEquiv, LinearEquiv.trans_apply,
    LinearEquivTensorProductModule_symm_tmul]
  rfl

/-- The `L`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞`. -/
noncomputable def FiniteAdeleRing.baseChangeAlgEquiv :
    L ⊗[K] FiniteAdeleRing A K ≃ₐ[L] FiniteAdeleRing B L where
  __ := AlgEquiv.ofBijective
    (SemialgHom.baseChange_of_algebraMap <| FiniteAdeleRing.mapSemialgHom A K L B)
    (FiniteAdeleRing.baseChange_bijective A K L B)

/-- The `𝔸_K^∞`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞`. -/
noncomputable def FiniteAdeleRing.baseChangeAdeleAlgEquiv :
    L ⊗[K] FiniteAdeleRing A K ≃ₐ[FiniteAdeleRing A K] FiniteAdeleRing B L where
  __ := SemialgHom.baseChangeRightOfAlgebraMap <| FiniteAdeleRing.mapSemialgHom A K L B
  __ := FiniteAdeleRing.baseChangeAlgEquiv A K L B

open RestrictedProduct in
noncomputable def FiniteAdeleRing.flattenBaseChange :
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → w.val.adicCompletion L,
        AddSubgroup.pi Set.univ fun (w : Extension B v) ↦
        (w.val.adicCompletionIntegers L).toAddSubgroup] ≃ₜ FiniteAdeleRing B L :=
  RestrictedProduct.flatten_homeomorph'
    (G := fun (w : HeightOneSpectrum B) ↦ w.adicCompletion L)
    (fun (w : HeightOneSpectrum B) ↦ w.adicCompletionIntegers L)
    (Filter.Tendsto.cofinite_of_finite_preimage_singleton <| Extension.finite A K L B)

open RestrictedProduct in
omit [IsIntegralClosure B A L] [FiniteDimensional K L] in
@[simp]
lemma FiniteAdeleRing.flattenBaseChange_apply (x : Πʳ (v : HeightOneSpectrum A),
    [(w : Extension B v) → w.val.adicCompletion L,
      AddSubgroup.pi Set.univ fun (w : Extension B v) ↦
      (w.val.adicCompletionIntegers L).toAddSubgroup]) (w : HeightOneSpectrum B) :
    FiniteAdeleRing.flattenBaseChange A K L B x w = x (comap A w) ⟨w, rfl⟩ :=
  rfl

open RestrictedProduct in
set_option maxHeartbeats 400000 in
noncomputable def FiniteAdeleRing.functional_component (v : HeightOneSpectrum A)
    (f : FiniteAdeleRing B L →ₗ[FiniteAdeleRing A K] FiniteAdeleRing A K) :
    ((w : Extension B v) → w.val.adicCompletion L) →ₗ[adicCompletion K v] adicCompletion K v where
  toFun x :=
    letI := Classical.typeDecidableEq (HeightOneSpectrum A)
    let x' : Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → w.val.adicCompletion L,
        AddSubgroup.pi Set.univ fun (w : Extension B v) ↦
        (w.val.adicCompletionIntegers L).toAddSubgroup] :=
      RestrictedProduct.single _ _ v x
    f (FiniteAdeleRing.flattenBaseChange A K L B x') v
  map_add' x y := by
    dsimp only
    rw [← add_apply, ← map_add]
    congr
    ext w
    simp only [flattenBaseChange_apply, add_apply]
    rw [← RestrictedProduct.single_add, ← Pi.add_apply]
    rfl
  map_smul' a x := by
    classical
    dsimp
    let a' : FiniteAdeleRing A K := RestrictedProduct.single _ _ v a
    have hmul (x : FiniteAdeleRing A K) : a * (x v) = (a' * x) v := by
      simp [a']
    rw [hmul, ← Algebra.id.smul_eq_mul, ← map_smul f, Algebra.smul_def a', Algebra.smul_def a]
    congr
    ext w
    simp only [flattenBaseChange_apply, mul_apply]
    letI : Algebra (adicCompletion K (comap A w)) (adicCompletion L w) :=
      comap_algebra A K L B rfl
    by_cases hc : comap A w = v
    . obtain rfl := hc
      simp only [RestrictedProduct.single_apply_same]
      rw [Pi.mul_apply]
      congr
      show _ = algebraMap _ _ (a' (comap A w))
      simp only [single_apply_same, a']
      rfl
    . rw [RestrictedProduct.single_apply_ne _ _ _ hc, RestrictedProduct.single_apply_ne _ _ _ hc,
        Pi.zero_apply, mul_zero]

open scoped Classical in
lemma FiniteAdeleRing.single_mul_apply (x : FiniteAdeleRing A K) (v : HeightOneSpectrum A) :
    x v = ((RestrictedProduct.single _ _ v 1 : FiniteAdeleRing A K) * x) v := by
  simp

open scoped Classical in
lemma FiniteAdeleRing.single_smul_apply (x : FiniteAdeleRing A K) (v : HeightOneSpectrum A) :
    x v = ((RestrictedProduct.single _ _ v 1 : FiniteAdeleRing A K) • x) v := by
  simp

open RestrictedProduct in
noncomputable def FiniteAdeleRing.functional_component_apply_flatten_symm (v : HeightOneSpectrum A)
    (f : FiniteAdeleRing B L →ₗ[FiniteAdeleRing A K] FiniteAdeleRing A K) (x : FiniteAdeleRing B L)
    : f x v = (FiniteAdeleRing.functional_component A K L B v f)
      ((FiniteAdeleRing.flattenBaseChange A K L B).symm x v) := by
  classical
  show _ = (FiniteAdeleRing.functional_component A K L B v f) (fun w ↦ x w.val)
  simp only [functional_component, LinearMap.coe_mk, AddHom.coe_mk]
  rw [FiniteAdeleRing.single_smul_apply, ← map_smul]
  congr
  ext w
  rw [flattenBaseChange_apply]
  show _ * x w = _
  by_cases h : comap A w = v
  . obtain rfl := h
    simp [mapRingHom]
  . simp [mapRingHom, RestrictedProduct.single_apply_ne _ _ _ h]

omit [IsIntegralClosure B A L] in
open RestrictedProduct in
lemma BaseChange.continuous_linearFunctional
    (f : FiniteAdeleRing B L →ₗ[FiniteAdeleRing A K] FiniteAdeleRing A K)
    : Continuous f := by
  classical
  let g := FiniteAdeleRing.flattenBaseChange A K L B
  rw [← Homeomorph.comp_continuous_iff' g]
  let hl (v : HeightOneSpectrum A) : ((w : Extension B v) → w.val.adicCompletion L)
      →ₗ[adicCompletion K v] adicCompletion K v :=
    FiniteAdeleRing.functional_component A K L B v f
  let h' (x : Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.1,
      Set.univ.pi fun w ↦ adicCompletionIntegers L w.1]) :=
    fun (v : HeightOneSpectrum A) ↦ hl v (x v)
  have heq : h' = (DFunLike.coe ∘ f) ∘ g := by
    rw [← Homeomorph.coe_toEquiv, ← Equiv.comp_symm_eq g.toEquiv]
    ext x v'
    rw [Function.comp_apply, Function.comp_apply,
      FiniteAdeleRing.functional_component_apply_flatten_symm]
    rfl
  have hval (x) (v') : h' x v' = f (g x) v' := by
    rw [heq]
    rfl
  have hmap : ∀ᶠ (v : HeightOneSpectrum A) in Filter.cofinite,
      Set.MapsTo (hl v) (Set.univ.pi fun w ↦ adicCompletionIntegers L w.1)
      (adicCompletionIntegers K v) := by
    have p (v : HeightOneSpectrum A) :
        ¬Set.MapsTo (hl v) (Set.univ.pi fun w ↦ adicCompletionIntegers L w.1)
        (adicCompletionIntegers K v) → ∃ x : (Set.univ.pi fun w ↦ adicCompletionIntegers L w.1),
            hl v x.1 ∉ adicCompletionIntegers K v := by
      intro h
      unfold Set.MapsTo at h
      exact Classical.exists_not_of_not_forall (fun m ↦ h (fun x hx ↦ @m ⟨x, hx⟩))
    choose cf hcf using p
    let y (v : HeightOneSpectrum A) : (Set.univ.pi fun (w : Extension B v) ↦
        SetLike.coe (adicCompletionIntegers L w.1)) :=
      if h : Set.MapsTo (hl v) (Set.univ.pi fun w ↦ adicCompletionIntegers L w.1)
        (adicCompletionIntegers K v)
      then
        (0 : AddSubgroup.pi Set.univ
          fun (w : Extension B v) ↦ (adicCompletionIntegers L w.1).toAddSubgroup)
      else
        cf v h
    let x : Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.1,
        Set.univ.pi fun w ↦ adicCompletionIntegers L w.1] :=
      ⟨fun v ↦ y v, by filter_upwards with v using (y v).prop⟩
    filter_upwards [(f (g x)).prop] with v' hv
    by_contra hmap
    change f (g x) v' ∈ _ at hv
    rw [← hval] at hv
    -- change hl v' (x v') ∈ _ at hv
    dsimp [x, h', y] at hv
    rw [dite_cond_eq_false (eq_false hmap)] at hv
    exact hcf v' hmap hv
  let h := RestrictedProduct.congrRight (ℱ := Filter.cofinite)
    (C := (fun v ↦ Set.univ.pi (fun (w : Extension B v) ↦ (adicCompletionIntegers L w.val))))
    (D := (fun v ↦ v.adicCompletionIntegers K)) (fun v ↦ hl v) hmap
  have : f ∘ g = h := by
    ext x v'
    show _ = h' x v'
    rw [hval]
    rfl
  rw [this]
  unfold h
  apply Continuous.restrictedProduct_congrRight
  intro v
  show Continuous (hl v)
  letI := comap_pi_algebra A K L B v |>.toSMul
  have : IsModuleTopology (adicCompletion K v) ((w : Extension B v) → w.val.adicCompletion L) :=
    prodAdicCompletionComap_isModuleTopology A K L B v
  apply IsModuleTopology.continuous_of_linearMap

lemma BaseChange.isModuleTopology :
    IsModuleTopology (FiniteAdeleRing A K) (FiniteAdeleRing B L) := by
  have : Module.Finite (FiniteAdeleRing A K) (FiniteAdeleRing B L) := by
    apply Module.Finite.equiv (FiniteAdeleRing.baseChangeAdeleAlgEquiv A K L B).toLinearEquiv
  have : Module.Free (FiniteAdeleRing A K) (FiniteAdeleRing B L) := by
    apply Module.Free.of_equiv (FiniteAdeleRing.baseChangeAdeleAlgEquiv A K L B).toLinearEquiv
  have htm : IsTopologicalModule (FiniteAdeleRing A K) (FiniteAdeleRing B L) := by
    rw [IsModuleTopology.iff_Continuous_algebraMap]
    apply FiniteAdeleRing.mapSemialgHom_continuous
  have := htm.toContinuousSMul
  letI : Module (FiniteAdeleRing A K) (FiniteAdeleRing B L) :=
    inferInstance
  apply IsModuleTopology.of_finite_continuousFunctionals
  apply BaseChange.continuous_linearFunctional

/-- The continuous `𝔸_K^∞`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞` -/
noncomputable def FiniteAdeleRing.baseChangeAdeleContinuousAlgEquiv :
    L ⊗[K] FiniteAdeleRing A K ≃A[FiniteAdeleRing A K] FiniteAdeleRing B L :=
  have := BaseChange.isModuleTopology A K L B
  IsModuleTopology.continuousAlgEquivOfAlgEquiv <|
    baseChangeAdeleAlgEquiv A K L B

/-- The continuous `L`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞` -/
noncomputable def FiniteAdeleRing.baseChangeContinuousAlgEquiv :
    L ⊗[K] FiniteAdeleRing A K ≃A[L] FiniteAdeleRing B L where
  __ := baseChangeAlgEquiv A K L B
  __ := baseChangeAdeleContinuousAlgEquiv A K L B

lemma FiniteAdeleRing.baseChangeAdeleContinuousAlgEquiv_apply (x : L) (y : FiniteAdeleRing A K) :
    (FiniteAdeleRing.baseChangeAdeleContinuousAlgEquiv A K L B) (x ⊗ₜ y) =
    (algebraMap _ _ x) * (algebraMap _ _ y) :=
  rfl

lemma FiniteAdeleRing.baseChangeContinuousAlgEquiv_apply (x : L) (y : FiniteAdeleRing A K) :
    (FiniteAdeleRing.baseChangeContinuousAlgEquiv A K L B) (x ⊗ₜ y) =
    (algebraMap _ _ x) * (algebraMap _ _ y) :=
  rfl

end IsDedekindDomain

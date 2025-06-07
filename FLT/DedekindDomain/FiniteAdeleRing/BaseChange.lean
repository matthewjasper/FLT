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

/-- The ring homomorphism `𝔸_K^∞ → 𝔸_L^∞` for `L/K` an extension of number fields.-/
noncomputable def FiniteAdeleRing.mapRingHom :
    FiniteAdeleRing A K →+* FiniteAdeleRing B L := RestrictedProduct.mapRingHom
  (fun (v : HeightOneSpectrum A) ↦ v.adicCompletion K)
  (fun (w : HeightOneSpectrum B) ↦ w.adicCompletion L)
  (HeightOneSpectrum.comap A)
  (Filter.Tendsto.cofinite_of_finite_preimage_singleton <| Extension.finite A K L B)
  (fun w ↦ adicCompletionComapSemialgHom A K L B (w.comap A) w rfl)
  (by
    apply Filter.Eventually.of_forall
    intro w
    have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
    have := adicCompletionComapSemialgHom.mapadicCompletionIntegers A K L B (comap A w) w rfl
    exact Set.image_subset_iff.1 this)

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

lemma FiniteAdeleRing.mapSemialgHom_continuous : Continuous (mapSemialgHom A K L B) :=
  sorry

attribute [instance 100] RestrictedProduct.instSMulCoeOfSMulMemClass
-- otherwise
-- #synth SMul (FiniteAdeleRing A K) (FiniteAdeleRing B L)
-- spends 2 seconds failing to find `SMul (FiniteAdeleRing A K) (adicCompletion L w)

lemma BaseChange.isModuleTopology : IsModuleTopology (FiniteAdeleRing A K) (FiniteAdeleRing B L) :=
  sorry -- this should follow from the fact that L_w has the K_v-module topology? Hopefully
  -- **TODO** this needs an issue number.

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

lemma tendsTo_comap_confinite [FaithfulSMul A B] :
    Filter.Tendsto (comap A (B:=B)) Filter.cofinite Filter.cofinite :=
  have : FaithfulSMul A (FractionRing B) := FractionRing.instFaithfulSMul A B
  letI : Algebra (FractionRing A) (FractionRing B) :=
    FractionRing.liftAlgebra A (FractionRing B)
  (Filter.Tendsto.cofinite_of_finite_preimage_singleton <|
    Extension.finite A (FractionRing A) (FractionRing B) B)

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

noncomputable instance baseChangeAlgebra : Algebra K (FiniteAdeleRing B L) :=
  RingHom.toAlgebra <| (algebraMap L _).comp (algebraMap K L)

noncomputable instance baseChangeScalarTower :
    IsScalarTower K (FiniteAdeleRing A K) (FiniteAdeleRing B L) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  nth_rw 2 [RingHom.algebraMap_toAlgebra]
  symm
  exact SemialgHom.commutes (FiniteAdeleRing.mapSemialgHom A K L B) x

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

/-- The continuous `L`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞` -/
noncomputable def FiniteAdeleRing.baseChangeContinuousAlgEquiv :
    L ⊗[K] FiniteAdeleRing A K ≃A[L] FiniteAdeleRing B L where
  __ := FiniteAdeleRing.baseChangeAlgEquiv A K L B
  continuous_toFun := sorry
  continuous_invFun := sorry
  -- TODO needs issue number


end IsDedekindDomain

/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper
-/

import FLT.DedekindDomain.FiniteAdeleRing.TensorPi
import FLT.Mathlib.Topology.Algebra.RestrictedProduct
import Mathlib.RingTheory.Flat.Basic

namespace RestrictedProduct

open TensorProduct

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  {ι : Type*} (N : ι → Type*) [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)]

variable (S : Set ι) (ℱ : Filter ι) (L : ∀ i, Submodule R (N i))

noncomputable def lTensorRestriction (i : ι) : Submodule R (M ⊗[R] N i) :=
  LinearMap.range (LinearMap.lTensor M (Submodule.subtype <| L i))

noncomputable def lTensor :
    M ⊗[R] Πʳ i, [N i, L i]_[ℱ] →ₗ[R] Πʳ i, [M ⊗[R] N i, lTensorRestriction R M N L i]_[ℱ] :=
  have hmap : ∀ (m : M), ∀ᶠ (j : ι) in ℱ, Set.MapsTo
      ((fun i ↦ (TensorProduct.mk R M (N i)) m) j) (L j) (lTensorRestriction R M N L j) := by
    intro m
    apply Filter.Eventually.of_forall
    intro i n hn
    exact ⟨m ⊗ₜ[R] ⟨n, hn⟩, rfl⟩
  TensorProduct.lift {
    toFun m := mapLinearMap N _ id Filter.tendsto_id
      (fun i ↦ TensorProduct.mk R M (N i) m) (hmap m)
    map_add' m n := by
      ext f i
      simp
    map_smul' a m := by
      ext f i
      simp only [map_smul, mapLinearMap_apply, id_eq, LinearMap.smul_apply, TensorProduct.mk_apply,
        RingHom.id_apply]
      rfl
  }

@[simp]
lemma lTensor_tmul (m : M) (f : Πʳ i, [N i, L i]_[ℱ]) (i : ι) :
    lTensor R M N ℱ L (m ⊗ₜ f) i = m ⊗ₜ (f i) :=
  rfl

variable [Module.FinitePresentation R M] [Module.Flat R M]

-- I think this is needed for the lemmas below
noncomputable def m_tensor_l_equiv (i : ι): M ⊗[R] (L i) ≃ₗ[R] lTensorRestriction R M N L i :=
  LinearEquiv.ofInjective (LinearMap.lTensor M (Submodule.subtype <| L i))
    (Module.Flat.lTensor_preserves_injective_linearMap (L i).subtype
      (Submodule.injective_subtype (L i)))

lemma lTensor_principal_bijective : Function.Bijective (lTensor R M N (Filter.principal S) L) :=
  sorry

lemma lTensor_bijective : Function.Bijective (lTensor R M N ℱ L) :=
  sorry

noncomputable def lTensor_equiv :
    M ⊗[R] Πʳ i, [N i, L i]_[ℱ] ≃ₗ[R] Πʳ i, [M ⊗[R] N i, lTensorRestriction R M N L i]_[ℱ] :=
  LinearEquiv.ofBijective (lTensor R M N ℱ L) (lTensor_bijective R M N ℱ L)

@[simp]
lemma lTensor_equiv_tmul (m : M) (f : Πʳ i, [N i, L i]_[ℱ]) (i : ι) :
    lTensor_equiv R M N ℱ L (m ⊗ₜ f) i = m ⊗ₜ (f i) :=
  rfl

end RestrictedProduct

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Module.End.IsSemisimple` and its invariant-complement characterization.
public import Mathlib.LinearAlgebra.Semisimple
-- `Polynomial.Irreducible` and `Polynomial.charpoly` for cuspidal support.
public import Mathlib.LinearAlgebra.Charpoly.Basic
-- `TauCeti.HallAlgebra.blockAverage_mul`, `IsCuspidal`, `moebius`, `greenCuspidal`.
public import TauCeti.RepresentationTheory.CharacterTable.GLn.HallAlgebra.Mackey
-- `LinearMap.blockTriangular` for block upper-triangular endomorphisms.
import TauCeti.LinearAlgebra.Prod
-- `charpoly_eq_charpoly_restrict_mul_charpoly_mapQ` factors charpoly along invariant subspaces.
import TauCeti.LinearAlgebra.Charpoly.Quotient
-- `Submodule.finrank_quotient_add_finrank` and `LinearEquiv.ofInjectiveEndo`.
import Mathlib.LinearAlgebra.Dimension.Finrank
-- `LinearMap.IsIdempotentElem.ker_mem_invtSubmodule_iff` and `Submodule.projection`.
import Mathlib.LinearAlgebra.Projection
-- `Module.End.eventually_isCompl_ker_pow_range_pow` for the Fitting decomposition.
import Mathlib.RingTheory.Artinian.Module
-- `Polynomial.exists_monic_irreducible_factor` and `minpoly` divisibility.
import Mathlib.RingTheory.Polynomial.UniqueFactorization
-- `AlgebraicClosure` and `IsAlgClosed.exists_root` for matching irreducible factors.
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
-- `Matrix.charpoly_toMatrix` and `Matrix.exists_mulVec_eq_zero_iff`.
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
-- `Complex.conj` for `conj_moebius`.
import Mathlib.Basic.Complex.Basic

/-!
# Cuspidal class functions and the Möbius function of the Hall algebra

This file establishes the first half of the theory of cuspidal class functions and the Möbius
function `μ = 𝟙⁻¹` in the Hall algebra `TauCeti.HallAlgebra k` over a finite field `k`:

* **Crapo's complementation lemma** (`TauCeti.HallAlgebra.crapo_complementation`): on a finite
  modular lattice `L`, a function `μ : L → M` with `∑_{U ≤ X} μ U = 0` for all `X ≠ ⊥` and
  `μ ⊤ ≠ 0` forces every element of `L` to be complemented.
* **Semisimplicity from `μ ≠ 0`** (`TauCeti.HallAlgebra.isSemisimple_of_moebius_ne_zero`):
  applying Crapo's lemma to the modular lattice `g.invtSubmodule` shows that if `μ(g) ≠ 0` then
  every `g`-invariant subspace has a `g`-invariant complement, so `g` is semisimple.
* **Block average of `B · μ`** (`TauCeti.HallAlgebra.blockAverage_mul_moebius`): because `μ` is
  multiplicative under block averages (`δμ = μ ⊗ μ`) and vanishes off semisimple endomorphisms,
  `δ(B · μ)(a, b) = μ(a) · μ(b) · B(a ⊕ b)`.
* **Green's cuspidal functions `C_η`** (`TauCeti.HallAlgebra.greenCuspidal_mul_constOne`,
  `TauCeti.HallAlgebra.greenCuspidal_eq_zero_of_dim_eq_zero`,
  `TauCeti.HallAlgebra.isCuspidal_greenCuspidal`): `C_η ∗ 𝟙 = -β_η`, `C_η` vanishes in dimension
  `0`, and `C_η` is cuspidal.
* **Primary support of cuspidal functions**
  (`TauCeti.HallAlgebra.IsCuspidal.exists_charpoly_eq_pow`): if `F` is cuspidal and `F(g) ≠ 0`,
  then the characteristic polynomial of `g` is a power `P ^ j` of an irreducible polynomial `P`.

## References

* H. H. Crapo, *The Möbius function of a lattice*, J. Combinatorial Theory 1 (1966), Theorem 3.
* J. A. Green, *The characters of the finite general linear groups*, Trans. Amer. Math. Soc. 80
  (1955), Theorem 1.
* The proof route follows [grh-lean](https://github.com/lsernau/grh-lean) (Apache 2.0),
  `grh/src/Lib/LocalGL/Green/CuspidalFunctions.lean`; the formalization here is built on
  `TauCeti.HallAlgebra` and generalizes Crapo's lemma to arbitrary additive commutative monoids.
-/

public section

open Module Polynomial Finset Submodule LinearMap ComplexConjugate Matrix

namespace TauCeti.HallAlgebra

open SimilarityClass

/-! ### Crapo's complementation lemma -/

/-- **Crapo's complementation lemma** on a finite modular lattice: if `μ : L → M` satisfies
`∑_{U ≤ X} μ U = 0` for every `X ≠ ⊥` and `μ ⊤ ≠ 0`, then every element of `L` has a
complement. -/
theorem crapo_complementation {L M : Type*} [Lattice L] [BoundedOrder L] [IsModularLattice L]
    [Fintype L] [DecidableRel ((· ≤ ·) : L → L → Prop)] [AddCommMonoid M]
    {μ : L → M} (h_sum : ∀ X ≠ ⊥, ∑ U : L with U ≤ X, μ U = 0) (h_ne : μ ⊤ ≠ 0) (W : L) :
    IsComplemented W := by
  classical
  obtain ⟨C, hC, h_max⟩ : ∃ C : L, Maximal (Disjoint W) C :=
    exists_maximal_of_wellFoundedGT (Disjoint W) ⟨⊥, disjoint_bot_right⟩
  refine ⟨C, hC, codisjoint_iff_le_sup.mpr ?_⟩
  by_contra h_top
  apply h_ne
  suffices h_vanish : ∀ U : L, ¬U ≤ W ⊔ C → μ U = 0 from h_vanish ⊤ h_top
  intro U hU
  induction U using WellFoundedLT.induction with | ind U ih => ?_
  have meet_ne : U ⊓ (W ⊔ C) ≠ ⊥ := by
    intro h_bot
    have hdisj : Disjoint W (C ⊔ U) :=
      hC.disjoint_sup_right_of_disjoint_sup_left (disjoint_iff.mpr (by rwa [inf_comm]))
    have hle : C ⊔ U ≤ C := h_max hdisj le_sup_left
    exact hU ((le_sup_right.trans hle).trans le_sup_right)
  have h_sub : (univ.filter fun A : L ↦ A ≤ U ⊓ (W ⊔ C)) ⊆ (univ.filter fun A : L ↦ A ≤ U) := by
    intro A hA
    simp only [mem_filter, mem_univ, true_and, le_inf_iff] at hA ⊢
    exact hA.1
  have hU_ne : U ≠ ⊥ := ne_bot_of_le_ne_bot meet_ne inf_le_left
  have h_eq := h_sum U hU_ne
  rw [← sum_sdiff h_sub, h_sum _ meet_ne, add_zero] at h_eq
  rw [sum_eq_single U] at h_eq
  · exact h_eq
  · intro A hA hAU
    simp only [mem_sdiff, mem_filter, mem_univ, true_and, le_inf_iff, not_and] at hA
    exact ih A (lt_of_le_of_ne hA.1 hAU) (hA.2 hA.1)
  · intro hU_not
    exfalso
    apply hU_not
    simp [le_inf_iff, hU]

/-! ### Semisimplicity and block averages of `μ` -/

section Moebius

variable {k V : Type*} [Field k] [Finite k]
  [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- At the class of `g`, the sum of `μ(g|_W)` over all `g`-invariant subspaces `W` equals `1(g)`. -/
theorem sum_moebius_ofEnd_invtRestrict (g : Module.End k V) [Fintype g.invtSubmodule] :
    ∑ W : g.invtSubmodule, moebius (ofEnd (g.invtRestrict W.prop)) =
      (1 : HallAlgebra k) (ofEnd g) := by
  have h := congrFun (moebius_mul_constOne (k := k)) (ofEnd g)
  simpa [mul_ofEnd_eq_sum, constOne_apply] using h

omit [Finite k] [Module.Finite k V] in
/-- The lattice of `g`-invariant subspaces is modular. -/
private lemma isModularLattice_invtSubmodule (g : Module.End k V) :
    IsModularLattice g.invtSubmodule :=
  ⟨fun y ↦ sup_inf_le_assoc_of_le (y : Submodule k V)⟩

/-- If `μ(g) ≠ 0`, then `g` is semisimple. -/
theorem isSemisimple_of_moebius_ne_zero {g : Module.End k V}
    (h_ne : moebius (ofEnd g) ≠ 0) : g.IsSemisimple := by
  classical
  have : Finite V := Module.finite_of_finite k
  have : Fintype g.invtSubmodule := Fintype.ofFinite _
  have : IsModularLattice g.invtSubmodule := isModularLattice_invtSubmodule g
  refine Module.End.isSemisimple_iff'.mpr
    (crapo_complementation (μ := fun U : g.invtSubmodule ↦ moebius (ofEnd (g.invtRestrict U.prop)))
      (fun X hX ↦ ?_) ?_)
  · have : Fintype (g.invtRestrict X.prop).invtSubmodule := Fintype.ofFinite _
    have h_sub : ∀ v : (X : Submodule k V),
        (X : Submodule k V).subtype (g.invtRestrict X.prop v) =
          g ((X : Submodule k V).subtype v) := fun v ↦ g.coe_invtRestrict_apply X.prop v
    have h_bij : ∑ U : g.invtSubmodule with U ≤ X, moebius (ofEnd (g.invtRestrict U.prop)) =
        ∑ W : (g.invtRestrict X.prop).invtSubmodule,
          moebius (ofEnd ((g.invtRestrict X.prop).invtRestrict W.prop)) := by
      refine sum_nbij'
        (fun U ↦ ⟨Submodule.comap (X : Submodule k V).subtype U.val,
          Submodule.comap_mem_invtSubmodule _ h_sub U.property⟩)
        (fun W ↦ ⟨W.val.map (X : Submodule k V).subtype, fun y hy ↦ by
          rcases hy with ⟨x, hx, rfl⟩
          exact ⟨g.invtRestrict X.prop x, W.property hx, g.coe_invtRestrict_apply X.prop x⟩⟩)
        ?_ ?_ ?_ ?_ ?_
      · intro U _; exact mem_univ _
      · intro W _
        simp only [mem_filter, mem_univ, true_and]
        exact Submodule.map_subtype_le _ _
      · intro U hU
        simp only [mem_filter, mem_univ, true_and] at hU
        exact Subtype.ext (Submodule.map_comap_eq_self (by simpa using hU))
      · intro W _
        exact Subtype.ext (Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _) _)
      · intro U hU
        simp only [mem_filter, mem_univ, true_and] at hU
        exact (congrArg moebius (ofEnd_invtRestrict_comap (X : Submodule k V).subtype h_sub
          (Submodule.injective_subtype _) U.property (by simpa using hU))).symm
    rw [h_bij, sum_moebius_ofEnd_invtRestrict, one_apply, dim_ofEnd]
    have hfin : finrank k (X : Submodule k V) ≠ 0 := by
      intro h0
      exact hX (Subtype.ext (Submodule.finrank_eq_zero.mp h0))
    simp [hfin]
  · have h_top : ofEnd (g.invtRestrict (⊤ : g.invtSubmodule).prop) = ofEnd g :=
      ofEnd_invtRestrict_eq_of_injective (g := g) LinearMap.id (fun _ ↦ rfl) _
        Function.injective_id LinearMap.range_id
    rwa [h_top]

/-- `μ` takes the value `1` on any zero-dimensional similarity class. -/
theorem moebius_eq_one_of_dim_eq_zero {o : SimilarityClass k} (h : o.dim = 0) :
    moebius o = 1 := by
  classical
  have : Finite (Fin o.dim → k) := Module.finite_of_finite k
  have : Fintype o.rep.invtSubmodule := Fintype.ofFinite _
  have h1 := congrFun (moebius_mul_constOne (k := k)) o
  rw [← ofEnd_rep o, mul_ofEnd_eq_sum] at h1
  have : Subsingleton (Fin o.dim → k) := by rw [h]; infer_instance
  have h_uniq : ∀ W : o.rep.invtSubmodule, W = ⊥ := fun W ↦
    Subtype.ext (Subsingleton.elim _ _)
  rw [Finset.sum_eq_single ⊥ (fun W _ hW ↦ absurd (h_uniq W) hW) (fun h ↦ absurd (mem_univ _) h)]
    at h1
  have hbot : ofEnd (o.rep.invtRestrict (⊥ : o.rep.invtSubmodule).prop) = o :=
    (ofEnd_rep o) ▸ ofEnd_eq_of_finrank_eq_zero (by simp) (by simpa using h)
  simpa [hbot, constOne_apply, one_apply, h] using h1

/-- The block average of the constant function `𝟙` is `𝟙`. -/
private lemma blockAverage_constOne [Fintype k] (c : SimilarityClass k) :
    blockAverage (constOne (k := k)) c = constOne := by
  refine ext_ofEnd fun r z ↦ ?_
  rw [← ofEnd_rep c]
  have : Finite ((Fin r → k) →ₗ[k] (Fin c.dim → k)) := Module.finite_of_finite k
  have : Fintype ((Fin r → k) →ₗ[k] (Fin c.dim → k)) := Fintype.ofFinite _
  rw [blockAverage_ofEnd]
  simp [constOne_apply]

/-- The block average of the unit `1` factors as `1 a * 1 b`. -/
private lemma blockAverage_one [Fintype k] {n m : ℕ}
    (x : Module.End k (Fin n → k)) (y : Module.End k (Fin m → k)) :
    blockAverage (1 : HallAlgebra k) (ofEnd x) (ofEnd y) =
      (1 : HallAlgebra k) (ofEnd x) * (1 : HallAlgebra k) (ofEnd y) := by
  by_cases hx : n = 0
  · rw [blockAverage_of_dim_eq_zero_left _ (by simp [hx])]
    simp [one_apply, dim_ofEnd, hx]
  · by_cases hy : m = 0
    · rw [blockAverage_of_dim_eq_zero_right _ (by simp [hy])]
      simp [one_apply, dim_ofEnd, hx, hy]
    · simp only [one_apply, dim_ofEnd, Module.finrank_fin_fun, hx, ↓reduceIte, zero_mul]
      have : Finite ((Fin m → k) →ₗ[k] (Fin n → k)) := Module.finite_of_finite k
      have : Fintype ((Fin m → k) →ₗ[k] (Fin n → k)) := Fintype.ofFinite _
      rw [blockAverage_ofEnd]
      refine Finset.expect_eq_zero fun T _ ↦ ?_
      rw [one_apply, dim_ofEnd, Module.finrank_prod, Module.finrank_fin_fun,
        Module.finrank_fin_fun]
      simp [Nat.add_eq_zero_iff, hx]

/-- `μ` is multiplicative under block averages: `δμ(a, b) = μ(a) · μ(b)`. -/
theorem blockAverage_moebius [Fintype k] (a b : SimilarityClass k) :
    blockAverage (moebius (k := k)) a b = moebius a * moebius b := by
  have h_eq : blockAverage (moebius (k := k)) a = moebius a • moebius := by
    refine isUnit_constOne.mul_right_cancel (ext_ofEnd fun m y ↦ ?_)
    let F : HallAlgebra k := fun c ↦
      (blockAverage (moebius (k := k)) c * (constOne : HallAlgebra k)) (ofEnd y)
    let F' : HallAlgebra k := fun c ↦
      ((moebius c • (moebius : HallAlgebra k)) * (constOne : HallAlgebra k)) (ofEnd y)
    suffices key : F * constOne = F' * constOne from
      congrFun (isUnit_constOne.mul_right_cancel key) a
    refine ext_ofEnd fun n x ↦ ?_
    classical
    have : Finite (Fin n → k) := Module.finite_of_finite k
    have : Fintype x.invtSubmodule := Fintype.ofFinite _
    have h_mackey := blockAverage_mul (moebius (k := k)) constOne (a := x) (b := y)
    rw [moebius_mul_constOne, finsum_eq_sum_of_fintype] at h_mackey
    have hF : (F * (constOne : HallAlgebra k)) (ofEnd x) =
        blockAverage (1 : HallAlgebra k) (ofEnd x) (ofEnd y) := by
      rw [mul_ofEnd_eq_sum, h_mackey]
      refine Finset.sum_congr rfl fun A _ ↦ ?_
      simp [F, constOne_apply, blockAverage_constOne]
    have hF' : (F' * (constOne : HallAlgebra k)) (ofEnd x) =
        (1 : HallAlgebra k) (ofEnd x) * (1 : HallAlgebra k) (ofEnd y) := by
      rw [mul_ofEnd_eq_sum]
      have h1 : ∀ A : x.invtSubmodule,
          F' (ofEnd (x.invtRestrict A.prop)) * constOne (ofEnd (x.invtQuot A.prop)) =
            moebius (ofEnd (x.invtRestrict A.prop)) * (1 : HallAlgebra k) (ofEnd y) := by
        intro A
        simp [F', constOne_apply, moebius_mul_constOne, smul_apply]
      simp_rw [h1, ← Finset.sum_mul, sum_moebius_ofEnd_invtRestrict]
    rw [hF, hF', blockAverage_one]
  simpa [smul_apply] using congrFun h_eq b

omit [Finite k] in
/-- A block upper-triangular endomorphism that is semisimple is similar to the corresponding block
diagonal endomorphism `a ⊕ b`. -/
private lemma ofEnd_blockTriangular_eq_prodMap_of_isSemisimple
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [Module.Finite k V₁]
    [AddCommGroup V₂] [Module k V₂] [Module.Finite k V₂]
    (a : Module.End k V₁) (b : Module.End k V₂) (x : V₂ →ₗ[k] V₁)
    (hss : (a.blockTriangular b x).IsSemisimple) :
    ofEnd (a.blockTriangular b x) = ofEnd (a.prodMap b) := by
  have h_inv : (⊤ : Submodule k V₁).prod (⊥ : Submodule k V₂) ∈
      (a.blockTriangular b x).invtSubmodule := by
    rintro ⟨v₁, v₂⟩ ⟨_, hv₂⟩
    change v₂ = 0 at hv₂
    subst hv₂
    simp
  obtain ⟨C, C_inv, hC⟩ := Module.End.isSemisimple_iff.mp hss _ h_inv
  have proj_comm :
      projection _ C hC ∘ₗ a.blockTriangular b x ∘ₗ projection _ C hC =
        projection _ C hC ∘ₗ a.blockTriangular b x :=
    (isIdempotentElem_projection hC).ker_mem_invtSubmodule_iff.mp (by simpa using C_inv)
  let φ : V₁ × V₂ →ₗ[k] V₁ × V₂ :=
    (LinearMap.fst k V₁ V₂ ∘ₗ projection _ C hC).prod (LinearMap.snd k V₁ V₂)
  have hφ_inj : Function.Injective φ := by
    rw [_root_.injective_iff_map_eq_zero]
    rintro ⟨v₁, v₂⟩ hv
    have h2 : v₂ = 0 := congrArg Prod.snd hv
    subst h2
    have h1 : (projection _ C hC (v₁, (0 : V₂))).1 = 0 := congrArg Prod.fst hv
    have hp := projection_apply_of_mem_left hC
      (show (v₁, (0 : V₂)) ∈ (⊤ : Submodule k V₁).prod (⊥ : Submodule k V₂) by simp)
    rw [hp] at h1
    exact Prod.ext h1 rfl
  refine ofEnd_eq_of_apply_eq (LinearEquiv.ofInjectiveEndo φ hφ_inj) fun ⟨v₁, v₂⟩ ↦ ?_
  have hproj_snd : (projection _ C hC (v₁, v₂)).2 = 0 :=
    (projection_apply_mem hC (v₁, v₂)).2
  have hcomm := LinearMap.congr_fun proj_comm (v₁, v₂)
  simp only [LinearMap.comp_apply] at hcomm
  have h_left : a.blockTriangular b x (projection _ C hC (v₁, v₂)) =
      (a (projection _ C hC (v₁, v₂)).1, 0) := by
    ext <;> simp [hproj_snd]
  have h_proj_left : projection _ C hC (a (projection _ C hC (v₁, v₂)).1, 0) =
      (a (projection _ C hC (v₁, v₂)).1, 0) :=
    projection_apply_of_mem_left hC (by simp)
  change φ (a.blockTriangular b x (v₁, v₂)) = (a.prodMap b) (φ (v₁, v₂))
  ext
  · simp only [φ, LinearMap.prod_apply, Function.prod_apply, LinearMap.comp_apply, fst_apply,
      prodMap_apply]
    rw [← hcomm, h_left, h_proj_left]
  · simp [φ]

/-- For any class function `B`, the block average of the pointwise product `B · μ` at `(a, b)`
equals `μ(a) · μ(b) · B(a ⊕ b)`. -/
theorem blockAverage_mul_moebius [Fintype k] (B : HallAlgebra k) (a b : SimilarityClass k) :
    blockAverage (fun c ↦ B c * moebius c) a b =
      moebius a * moebius b * B (ofEnd (a.rep.prodMap b.rep)) := by
  classical
  have : Finite ((Fin b.dim → k) →ₗ[k] (Fin a.dim → k)) := Module.finite_of_finite k
  have : Fintype ((Fin b.dim → k) →ₗ[k] (Fin a.dim → k)) := Fintype.ofFinite _
  rw [← blockAverage_moebius, ← ofEnd_rep a, ← ofEnd_rep b,
    blockAverage_ofEnd, blockAverage_ofEnd, mul_comm, Finset.mul_expect]
  refine Finset.expect_congr rfl fun X _ ↦ ?_
  by_cases h_ne : moebius (ofEnd (a.rep.blockTriangular b.rep X)) = 0
  · simp [h_ne]
  · rw [ofEnd_blockTriangular_eq_prodMap_of_isSemisimple _ _ _
      (isSemisimple_of_moebius_ne_zero h_ne), ofEnd_rep, ofEnd_rep, mul_comm]

/-- `μ` is real-valued: `conj (μ c) = μ c` for every similarity class `c`. -/
@[simp]
theorem conj_moebius (c : SimilarityClass k) : conj (moebius c) = moebius c := by
  let μ' : HallAlgebra k := fun x ↦ conj (moebius x)
  have h_inv : μ' * (constOne : HallAlgebra k) = moebius * constOne := ext_ofEnd fun n g ↦ by
    classical
    have : Finite (Fin n → k) := Module.finite_of_finite k
    have : Fintype g.invtSubmodule := Fintype.ofFinite _
    have h1 := sum_moebius_ofEnd_invtRestrict g
    have h2 : (μ' * (constOne : HallAlgebra k)) (ofEnd g) =
        conj ((1 : HallAlgebra k) (ofEnd g)) := by
      rw [mul_ofEnd_eq_sum, ← h1, map_sum]
      simp [μ', constOne_apply]
    rw [h2, moebius_mul_constOne, one_apply]
    split_ifs <;> simp
  exact congrFun (isUnit_constOne.mul_right_cancel h_inv) c

end Moebius

/-! ### Green's cuspidal functions `C_η` -/

section GreenCuspidal

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K] (η : K → ℂ)

omit [Finite k] in
/-- The eigenvalue sum `β_η` is additive on an invariant subspace and its quotient. -/
private lemma eigenvalueSum_invtRestrict_add_invtQuot {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (g : Module.End k V) {W : Submodule k V} (hW : W ∈ g.invtSubmodule) :
    eigenvalueSum K η (ofEnd (g.invtRestrict hW)) + eigenvalueSum K η (ofEnd (g.invtQuot hW)) =
      eigenvalueSum K η (ofEnd g) := by
  simp only [eigenvalueSum_ofEnd]
  have hcp := charpoly_eq_charpoly_restrict_mul_charpoly_mapQ (W := W) g hW
  have hsub : (g.invtRestrict hW).charpoly = (g.restrict hW).charpoly := by
    rw [← charpoly_ofEnd, ← charpoly_ofEnd]
    exact congrArg SimilarityClass.charpoly
      (ofEnd_eq_of_apply_eq (LinearEquiv.refl k W)
        (fun x ↦ Subtype.ext (g.coe_invtRestrict_apply hW x)))
  have hquot : (g.invtQuot hW).charpoly = (W.mapQ W g hW).charpoly := by
    rw [← charpoly_ofEnd, ← charpoly_ofEnd]
    refine congrArg SimilarityClass.charpoly
      (ofEnd_eq_of_apply_eq (LinearEquiv.refl k (V ⧸ W)) fun x ↦ ?_)
    induction x using Submodule.Quotient.induction_on with
    | H v => exact g.invtQuot_mk hW v
  have hcp_eq : g.charpoly = (g.invtRestrict hW).charpoly * (g.invtQuot hW).charpoly := by
    rw [hsub, hquot]
    exact hcp
  rw [hcp_eq, Polynomial.aroots_mul (mul_ne_zero (LinearMap.charpoly_monic _).ne_zero
    (LinearMap.charpoly_monic _).ne_zero), Multiset.map_add, Multiset.sum_add]

/-- `C_η ∗ 𝟙 = -β_η`: multiplying Green's cuspidal function by the constant function recovers minus
the eigenvalue sum. -/
@[simp]
theorem greenCuspidal_mul_constOne :
    greenCuspidal K η * constOne = (-eigenvalueSum K η : HallAlgebra k) := by
  suffices h : greenCuspidal K η + moebius * eigenvalueSum K η = (0 : HallAlgebra k) by
    have h1 := congrArg (· * constOne) h
    simp only [add_mul, zero_mul, mul_assoc, mul_comm (eigenvalueSum K η) constOne] at h1
    rw [← mul_assoc, moebius_mul_constOne, one_mul] at h1
    exact eq_neg_of_add_eq_zero_left h1
  refine ext_ofEnd fun n g ↦ ?_
  classical
  have : Finite (Fin n → k) := Module.finite_of_finite k
  have : Fintype g.invtSubmodule := Fintype.ofFinite _
  rw [add_apply, zero_apply, greenCuspidal_ofEnd, mul_ofEnd_eq_sum, finsum_eq_sum_of_fintype,
    ← Finset.sum_add_distrib]
  have hterm (W : g.invtSubmodule) :
      eigenvalueSum K η (ofEnd (g.invtRestrict W.prop)) *
          moebius (ofEnd (g.invtRestrict W.prop)) +
        moebius (ofEnd (g.invtRestrict W.prop)) *
          eigenvalueSum K η (ofEnd (g.invtQuot W.prop)) =
      eigenvalueSum K η (ofEnd g) * moebius (ofEnd (g.invtRestrict W.prop)) := by
    rw [← eigenvalueSum_invtRestrict_add_invtQuot η g W.prop]
    ring
  simp_rw [hterm, ← Finset.mul_sum, sum_moebius_ofEnd_invtRestrict, one_apply, dim_ofEnd,
    Module.finrank_fin_fun]
  split_ifs with h0
  · have hcp : g.charpoly = 1 :=
      Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic g)
        (by rw [LinearMap.charpoly_natDegree, Module.finrank_fin_fun, h0])
    simp [eigenvalueSum_ofEnd, hcp]
  · simp

/-- Green's cuspidal function `C_η` vanishes on every zero-dimensional similarity class. -/
theorem greenCuspidal_eq_zero_of_dim_eq_zero {c : SimilarityClass k} (hc : c.dim = 0) :
    greenCuspidal K η c = 0 := by
  classical
  have : Finite (Fin c.dim → k) := Module.finite_of_finite k
  have : Fintype c.rep.invtSubmodule := Fintype.ofFinite _
  have h1 := congrFun (greenCuspidal_mul_constOne (k := k) (K := K) η) c
  rw [← ofEnd_rep c, mul_ofEnd_eq_sum] at h1
  have : Subsingleton (Fin c.dim → k) := by rw [hc]; infer_instance
  have h_uniq : ∀ W : c.rep.invtSubmodule, W = ⊥ := fun W ↦ Subtype.ext (Subsingleton.elim _ _)
  rw [Finset.sum_eq_single ⊥ (fun W _ hW ↦ absurd (h_uniq W) hW) (fun h ↦ absurd (mem_univ _) h)]
    at h1
  have hbot : ofEnd (c.rep.invtRestrict (⊥ : c.rep.invtSubmodule).prop) = c :=
    (ofEnd_rep c) ▸ ofEnd_eq_of_finrank_eq_zero (by simp) (by simpa using hc)
  have hcp : c.rep.charpoly = 1 :=
    Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _)
      (by rw [LinearMap.charpoly_natDegree, Module.finrank_fin_fun, hc])
  have hβ : eigenvalueSum K η c = 0 := by
    rw [← ofEnd_rep c, eigenvalueSum_ofEnd, hcp]
    simp
  simpa [hbot, constOne_apply, neg_apply, hβ] using h1

omit [Finite k] in
/-- The eigenvalue sum `β_η` is additive on direct sums `a ⊕ b`. -/
private lemma eigenvalueSum_prodMap_rep (a b : SimilarityClass k) :
    eigenvalueSum K η (ofEnd (a.rep.prodMap b.rep)) =
      eigenvalueSum K η a + eigenvalueSum K η b := by
  simp only [eigenvalueSum_ofEnd, LinearMap.charpoly_prodMap,
    Polynomial.aroots_mul (mul_ne_zero (LinearMap.charpoly_monic _).ne_zero
      (LinearMap.charpoly_monic _).ne_zero), Multiset.map_add, Multiset.sum_add]
  rw [← eigenvalueSum_ofEnd, ← eigenvalueSum_ofEnd, ofEnd_rep, ofEnd_rep]

/-- Green's cuspidal function `C_η` is cuspidal. -/
theorem isCuspidal_greenCuspidal [Fintype k] : (greenCuspidal (k := k) K η).IsCuspidal := by
  rw [isCuspidal_iff]
  intro a b ha hb
  rw [← ofEnd_rep a, ← ofEnd_rep b,
    greenCuspidal_eq_mul_constOne K η (F := fun c ↦ eigenvalueSum K η c * moebius c) (fun _ ↦ rfl),
    blockAverage_mul]
  classical
  have : Finite (Fin a.dim → k) := Module.finite_of_finite k
  have : Fintype a.rep.invtSubmodule := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  have hterm (A : a.rep.invtSubmodule) :
      (blockAverage (fun c ↦ eigenvalueSum K η c * moebius c) (ofEnd (a.rep.invtRestrict A.prop)) *
        blockAverage constOne (ofEnd (a.rep.invtQuot A.prop))) (ofEnd b.rep) =
      (eigenvalueSum K η (ofEnd (a.rep.invtRestrict A.prop)) *
          moebius (ofEnd (a.rep.invtRestrict A.prop)) * (1 : HallAlgebra k) (ofEnd b.rep)) +
      (moebius (ofEnd (a.rep.invtRestrict A.prop)) *
          greenCuspidal K η (ofEnd b.rep)) := by
    have : Finite (Fin b.dim → k) := Module.finite_of_finite k
    have : Fintype b.rep.invtSubmodule := Fintype.ofFinite _
    rw [blockAverage_constOne, mul_ofEnd_eq_sum, greenCuspidal_ofEnd, finsum_eq_sum_of_fintype,
      Finset.mul_sum]
    rw [← sum_moebius_ofEnd_invtRestrict b.rep, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun B _ ↦ ?_
    rw [constOne_apply, mul_one, blockAverage_mul_moebius, eigenvalueSum_prodMap_rep]
    ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.sum_mul, sum_moebius_ofEnd_invtRestrict,
    one_apply, dim_ofEnd, Module.finrank_fin_fun]
  simp [ha, hb]

end GreenCuspidal

/-! ### Primary support of cuspidal class functions -/

section CuspidalSupport

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- The minimal polynomial of `g` annihilates the base-changed matrix of `g` over an extension
field `K`. -/
private lemma aeval_minpoly_map_toMatrix {K : Type*} [Field K] [Algebra k K]
    (g : Module.End k V) :
    Polynomial.aeval
      ((LinearMap.toMatrix (finBasis k V) (finBasis k V) g).map (algebraMap k K))
      (minpoly k g) = 0 := by
  let b := finBasis k V
  have hM0 : Polynomial.aeval (LinearMap.toMatrix b b g) (minpoly k g) = 0 := by
    have h1 : (LinearMap.toMatrixAlgEquiv b) (Polynomial.aeval g (minpoly k g)) = 0 := by
      rw [minpoly.aeval, map_zero]
    exact (Polynomial.aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b).toAlgHom g
      (minpoly k g)).trans h1
  have hmap := congrArg (RingHom.mapMatrix (algebraMap k K)) hM0
  have heval : RingHom.mapMatrix (algebraMap k K)
      (Polynomial.aeval (LinearMap.toMatrix b b g) (minpoly k g)) =
      Polynomial.aeval ((LinearMap.toMatrix b b g).map (algebraMap k K)) (minpoly k g) := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
    congr 1
    ext c i j
    simp only [RingHom.coe_comp, Function.comp_apply, Algebra.algebraMap_eq_smul_one,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp [Algebra.smul_def]
  rw [heval, map_zero] at hmap
  exact hmap

/-- Every irreducible factor of the characteristic polynomial of `g` divides its minimal
polynomial. -/
private lemma dvd_minpoly_of_irreducible_dvd_charpoly {g : Module.End k V} {P : k[X]}
    (hP_irred : Irreducible P) (hdvd : P ∣ g.charpoly) : P ∣ minpoly k g := by
  let K := AlgebraicClosure k
  have hP_deg : (P.map (algebraMap k K)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (algebraMap k K).injective]
    intro h0
    exact hP_irred.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr h0)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (P.map (algebraMap k K)) hP_deg
  have hα_char : Polynomial.IsRoot (g.charpoly.map (algebraMap k K)) α := by
    obtain ⟨Q, hQ⟩ := hdvd
    rw [hQ, Polynomial.map_mul, Polynomial.IsRoot.def, Polynomial.eval_mul, hα.eq_zero, zero_mul]
  let b := finBasis k V
  let MK := (LinearMap.toMatrix b b g).map (algebraMap k K)
  have hdet : (Matrix.scalar (Fin (finrank k V)) α - MK).det = 0 := by
    have h1 : MK.charpoly = g.charpoly.map (algebraMap k K) := by
      rw [← LinearMap.charpoly_toMatrix g b, Matrix.charpoly_map]
    have h2 : MK.charpoly.eval α = (Matrix.scalar (Fin (finrank k V)) α - MK).det := by
      change (Polynomial.evalRingHom α) (Matrix.charmatrix MK).det = _
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [Matrix.charmatrix, Matrix.diagonal_apply, Matrix.scalar_apply]
      split_ifs <;> simp
    rw [← h2, h1]
    exact hα_char.eq_zero
  obtain ⟨v, hv_ne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hMv : MK *ᵥ v = α • v := (sub_eq_zero.mp (by simpa [Matrix.sub_mulVec, Matrix.scalar_apply]
    using hv)).symm
  have hMpow (n : ℕ) : MK ^ n *ᵥ v = α ^ n • v := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hMv, smul_smul,
        mul_comm, pow_succ']
  have haeval_v (q : k[X]) : (Polynomial.aeval MK q) *ᵥ v = (Polynomial.aeval α q) • v := by
    induction q using Polynomial.induction_on' with
    | add p q hp hq => simp [map_add, Matrix.add_mulVec, add_smul, hp, hq]
    | monomial n a =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul, smul_mul_assoc, one_mul, Matrix.smul_mulVec, hMpow, smul_assoc]
  have hα_min : Polynomial.aeval α (minpoly k g) = 0 := by
    have h0 := haeval_v (minpoly k g)
    rw [aeval_minpoly_map_toMatrix g, Matrix.zero_mulVec] at h0
    exact (smul_eq_zero.mp h0.symm).resolve_right hv_ne
  have hP_dvd_minα : minpoly k α ∣ P :=
    minpoly.dvd k α (by rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]; exact hα.eq_zero)
  have hP_assoc : Associated P (minpoly k α) :=
    ((minpoly.irreducible
      (IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic α))).associated_of_dvd
      hP_irred hP_dvd_minα).symm
  exact hP_assoc.dvd_iff_dvd_left.mpr (minpoly.dvd k α hα_min)

/-- An irreducible factor `P` of `g.charpoly` gives a non-invertible operator `P(g)`. -/
private lemma not_isUnit_aeval_of_irreducible_dvd_charpoly {g : Module.End k V} {P : k[X]}
    (hP_irred : Irreducible P) (hdvd : P ∣ g.charpoly) : ¬IsUnit (Polynomial.aeval g P) := by
  intro h_inv
  obtain ⟨Q, hQ⟩ := dvd_minpoly_of_irreducible_dvd_charpoly hP_irred hdvd
  have hQ0 : Polynomial.aeval g Q = 0 := by
    have h0 : Polynomial.aeval g P * Polynomial.aeval g Q = 0 := by
      rw [← map_mul, ← hQ]; exact minpoly.aeval k g
    exact h_inv.mul_right_eq_zero.mp h0
  have hdvdQ : minpoly k g ∣ Q := minpoly.dvd k g hQ0
  have hne : Q ≠ 0 := fun h0 ↦ by
    rw [h0, mul_zero] at hQ
    exact minpoly.ne_zero (Algebra.IsIntegral.isIntegral g) hQ
  have hdeg := Polynomial.natDegree_le_of_dvd hdvdQ hne
  rw [hQ, Polynomial.natDegree_mul hP_irred.ne_zero hne] at hdeg
  have hPpos := hP_irred.natDegree_pos
  omega

/-- If `P(g)` is nilpotent for a monic irreducible polynomial `P`, then the characteristic
polynomial of `g` is a power of `P`. -/
theorem charpoly_eq_pow_of_isNilpotent {g : Module.End k V} {P : k[X]}
    (hP_irred : Irreducible P) (hP_monic : P.Monic) (h_nilp : IsNilpotent (Polynomial.aeval g P)) :
    g.charpoly = P ^ (finrank k V / P.natDegree) := by
  obtain ⟨m, hm⟩ := h_nilp
  have hmin_dvd : minpoly k g ∣ P ^ m :=
    minpoly.dvd k g (by simpa [map_pow] using hm)
  have h_all : ∀ Q : k[X], Irreducible Q → Q ∣ g.charpoly → Associated Q P := by
    intro Q hQ_irred hQ_dvd
    have hQ_pow : Q ∣ P ^ m :=
      (dvd_minpoly_of_irreducible_dvd_charpoly hQ_irred hQ_dvd).trans hmin_dvd
    exact hQ_irred.associated_of_dvd hP_irred (hQ_irred.prime.dvd_of_dvd_pow hQ_pow)
  have h_pow : ∀ n (f : k[X]), f.natDegree = n → f ≠ 0 →
      (∀ Q, Irreducible Q → Q ∣ f → Associated Q P) → ∃ j : ℕ, Associated f (P ^ j) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ d ih =>
      intro f hf_deg hf_ne hf_all
      by_cases hu : IsUnit f
      · exact ⟨0, by simpa using associated_one_iff_isUnit.mpr hu⟩
      · obtain ⟨Q, _, hQ_irred, hQ_dvd⟩ := Polynomial.exists_monic_irreducible_factor f hu
        have hQP := hf_all Q hQ_irred hQ_dvd
        obtain ⟨R, hR⟩ := hQP.dvd_iff_dvd_left.mp hQ_dvd
        have hR_ne : R ≠ 0 := fun h0 ↦ hf_ne (by simp [hR, h0])
        have hR_lt : R.natDegree < d := by
          rw [← hf_deg, hR, Polynomial.natDegree_mul hP_irred.ne_zero hR_ne]
          have := hP_irred.natDegree_pos
          omega
        obtain ⟨j, hj⟩ := ih R.natDegree hR_lt R rfl hR_ne
          fun Q' hQ' hQ'R ↦ hf_all Q' hQ' (hQ'R.trans ⟨P, by rw [hR, mul_comm]⟩)
        exact ⟨j + 1, by rw [hR, pow_succ']; exact hj.mul_left P⟩
  obtain ⟨j, hj⟩ := h_pow _ g.charpoly rfl (LinearMap.charpoly_monic g).ne_zero h_all
  have h_eq : g.charpoly = P ^ j :=
    Polynomial.eq_of_monic_of_associated (LinearMap.charpoly_monic g) (hP_monic.pow j) hj
  have h_deg : finrank k V = j * P.natDegree := by
    rw [← LinearMap.charpoly_natDegree g, h_eq, Polynomial.natDegree_pow]
  rw [h_eq, h_deg, Nat.mul_div_cancel _ hP_irred.natDegree_pos]

/-- On a Fitting component `C = ker(P(g)^N)` with `IsCompl C (range(P(g)^N))`, every block
upper-triangular endomorphism with diagonal blocks `g|_C` and `g|_{V/C}` is similar to `g`. -/
private lemma ofEnd_blockTriangular_fitting_eq {g : Module.End k V} {P : k[X]} {N : ℕ}
    (hN : IsCompl (LinearMap.ker (Polynomial.aeval g P ^ N))
      (LinearMap.range (Polynomial.aeval g P ^ N)))
    (hC : LinearMap.ker (Polynomial.aeval g P ^ N) ∈ g.invtSubmodule)
    (x : (V ⧸ LinearMap.ker (Polynomial.aeval g P ^ N)) →ₗ[k]
      LinearMap.ker (Polynomial.aeval g P ^ N)) :
    ofEnd ((g.invtRestrict hC).blockTriangular (g.invtQuot hC) x) = ofEnd g := by
  let C : Submodule k V := LinearMap.ker (Polynomial.aeval g P ^ N)
  have comm (Y : Module.End k V) (hY : ∀ v : V, Y (g v) = g (Y v)) (v : V) :
      Y ((Polynomial.aeval g P ^ N) v) = (Polynomial.aeval g P ^ N) (Y v) :=
    LinearMap.congr_fun ((Algebra.commute_of_mem_adjoin_singleton_of_commute
      (Polynomial.aeval_mem_adjoin_singleton k g)
      (LinearMap.ext hY : Commute Y g)).pow_right N).eq v
  let sylvester : Module.End k ((V ⧸ C) →ₗ[k] C) :=
    (g.invtRestrict hC).compRight k - LinearMap.lcomp k _ (g.invtQuot hC)
  have sylvester_inj : Function.Injective sylvester := by
    rw [_root_.injective_iff_map_eq_zero]
    intro y hy
    refine Submodule.linearMap_qext _ <|
      LinearMap.ext_on_codisjoint hN.codisjoint ((Submodule.ker_mkQ _).ge.trans
        (LinearMap.ker_le_ker_comp _ y)) ?_
    rintro _ ⟨v, rfl⟩
    refine Subtype.ext ((comm (C.subtype ∘ₗ y ∘ₗ Submodule.mkQ _) (fun u ↦ ?_) v).trans (y _).prop)
    have hu := congrArg Subtype.val
      (LinearMap.congr_fun (sub_eq_zero.mp hy) (Submodule.Quotient.mk u))
    simpa only [LinearMap.comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply,
      LinearMap.lcomp_apply, LinearMap.compRight_apply, Module.End.coe_invtRestrict_apply,
      Module.End.invtQuot_mk] using hu.symm
  obtain ⟨y, rfl⟩ := LinearMap.surjective_of_injective sylvester_inj x
  refine ofEnd_eq_of_apply_eq
    ((LinearEquiv.prodComm k C (V ⧸ C)).trans
      ((LinearEquiv.skewProd (LinearMap.quotKerEquivRange _) (LinearEquiv.refl k C) y).trans
        (Submodule.prodEquivOfIsCompl _ _ hN.symm))) ?_
  rintro ⟨⟨v₁, hv₁⟩, v₂⟩
  induction v₂ using Submodule.Quotient.induction_on with
  | H v =>
    simp [sylvester, C, comm g (fun _ ↦ rfl), Module.End.coe_invtRestrict_apply,
      Module.End.invtQuot_mk]
    abel

/-- If `F` is cuspidal and `F(g) ≠ 0`, then the characteristic polynomial of `g` is a power `P ^ j`
of an irreducible polynomial `P`. -/
theorem IsCuspidal.exists_charpoly_eq_pow [Fintype k] {F : HallAlgebra k} (hF : F.IsCuspidal)
    {g : Module.End k V} (hF_ne : F (ofEnd g) ≠ 0) :
    ∃ (P : k[X]) (j : ℕ), Irreducible P ∧ g.charpoly = P ^ j := by
  by_cases h_unit : IsUnit g.charpoly
  · exact ⟨X, 0, Polynomial.irreducible_X, (LinearMap.charpoly_monic g).eq_one_of_isUnit h_unit⟩
  obtain ⟨P, hP_monic, hP_irred, hdvd⟩ :=
    Polynomial.exists_monic_irreducible_factor g.charpoly h_unit
  have not_unit := not_isUnit_aeval_of_irreducible_dvd_charpoly hP_irred hdvd
  obtain ⟨N, hN, hN₀⟩ :=
    ((Polynomial.aeval g P).eventually_isCompl_ker_pow_range_pow.and
      (Filter.eventually_ne_atTop 0)).exists
  have hC : LinearMap.ker (Polynomial.aeval g P ^ N) ∈ g.invtSubmodule := by
    intro x hx
    simp only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢
    have hcomm : Commute g (Polynomial.aeval g P ^ N) :=
      (Algebra.commute_of_mem_adjoin_singleton_of_commute
        (Polynomial.aeval_mem_adjoin_singleton k g) rfl).pow_right N
    rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← hcomm.eq,
      Module.End.mul_eq_comp, LinearMap.comp_apply, hx, map_zero]
  refine ⟨P, _, hP_irred, charpoly_eq_pow_of_isNilpotent hP_irred hP_monic ⟨N, ?_⟩⟩
  have hcusp := hF.blockAverage_eq_zero
    (a := ofEnd (g.invtRestrict hC)) (b := ofEnd (g.invtQuot hC))
  have : Finite ((V ⧸ LinearMap.ker (Polynomial.aeval g P ^ N)) →ₗ[k]
      LinearMap.ker (Polynomial.aeval g P ^ N)) := Module.finite_of_finite k
  have : Fintype ((V ⧸ LinearMap.ker (Polynomial.aeval g P ^ N)) →ₗ[k]
      LinearMap.ker (Polynomial.aeval g P ^ N)) := Fintype.ofFinite _
  rw [blockAverage_ofEnd] at hcusp
  have hmean : (Finset.univ.expect fun x : (V ⧸ LinearMap.ker (Polynomial.aeval g P ^ N)) →ₗ[k]
      LinearMap.ker (Polynomial.aeval g P ^ N) ↦
      F (ofEnd ((g.invtRestrict hC).blockTriangular (g.invtQuot hC) x))) = F (ofEnd g) := by
    simp [ofEnd_blockTriangular_fitting_eq hN hC]
  rw [hmean] at hcusp
  have hC_ne : finrank k (LinearMap.ker (Polynomial.aeval g P ^ N)) ≠ 0 := by
    intro h0
    have hker : LinearMap.ker (Polynomial.aeval g P ^ N) = ⊥ := Submodule.finrank_eq_zero.mp h0
    have hbij : Function.Bijective (Polynomial.aeval g P ^ N) :=
      LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp hker) |>
        fun hsurj ↦ ⟨LinearMap.ker_eq_bot.mp hker, hsurj⟩
    have hunit_pow : IsUnit (Polynomial.aeval g P ^ N) := by
      let e := LinearEquiv.ofBijective (Polynomial.aeval g P ^ N) hbij
      exact ⟨⟨e.toLinearMap, e.symm.toLinearMap,
        LinearMap.ext fun v ↦ e.apply_symm_apply v,
        LinearMap.ext fun v ↦ e.symm_apply_apply v⟩, rfl⟩
    exact not_unit ((isUnit_pow_iff hN₀).mp hunit_pow)
  have hQ_zero : finrank k (V ⧸ LinearMap.ker (Polynomial.aeval g P ^ N)) = 0 := by
    by_contra hQ
    exact hF_ne (hcusp (by simpa using hC_ne) (by simpa using hQ))
  have hC_top : LinearMap.ker (Polynomial.aeval g P ^ N) = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp (Module.finrank_zero_iff.mp hQ_zero)
  ext v
  exact LinearMap.mem_ker.mp (hC_top ▸ Submodule.mem_top : v ∈ LinearMap.ker _)

end CuspidalSupport

end TauCeti.HallAlgebra

import Mathlib.Analysis.NormedSpace.CompactOperator
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic


attribute [-instance] Real.instPowReal

section hilbert_schmidt

-- Let V and W be Hilbert spaces over ℝ.
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ  V] [CompleteSpace V]
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ  W] [CompleteSpace W]


/-- The property that `∑ i, ⟪T (e i), T (e i)⟫` is summable for a given Hilbert basis `e`. -/
def HilbertBasis.HilbertSchmidtSummable (e : HilbertBasis I ℝ  V) (T : V →ₗ[ℝ ] W) :=
  Summable (fun i ↦ ⟪T (e i), T (e i)⟫_ℝ )

/-- The sum `∑ i, ⟪T (e i), T (e i)⟫`, i.e., the HS norm squared. -/
noncomputable def HilbertBasis.HilbertSchmidtNormSq (e : HilbertBasis I ℝ  V) (T : V →ₗ[ℝ ] W) :=
  ∑' i, ⟪T (e i), T (e i)⟫_ℝ 

/-- Hilbert-Schmidt operators. -/
class HilbertSchmidt (T : V →ₗ[ℝ ] W) where
  exists_summable : ∃ (e : HilbertBasis I ℝ V), e.HilbertSchmidtSummable T

/-Definition of square of norm-/
lemma normsq (x : W): ⟪x , x⟫_ℝ = ‖x‖ ^ 2 := by
  simp only [real_inner_self_eq_norm_sq]

/-Theorem: If A , B are Hilber Schmidt operator then A+B also-/


lemma expansion_normsq_add ( u v : W ):  ⟪(u + v), (u + v)⟫_ℝ = ‖u‖ ^ 2 + ‖v‖ ^ 2 + ⟪u , v⟫_ℝ  + ⟪v , u⟫_ℝ :=by
  rw[inner_add_left,inner_add_right,inner_add_right]
  rw [normsq u ,normsq v]
  simp only [add_assoc] 
  simp only [add_comm (⟪v ,u⟫_ℝ  ) (‖v‖^2)]
  simp 
  rw [add_left_comm]


lemma smul_le (a b:ℝ ): a≤ (b)/2→ 2*a ≤ b := by

  intro H
  refine Iff.mp (le_div_iff' ?hc) H
  simp
  
lemma arithmetic_mean_le_geometric_mean (a b : ℝ) :
  (a^2 + b^2) / 2 ≥  (a * b) :=by
   
  have h₁ : 0 < 2 :=by norm_num
  have h₂ : 0 ≤  (a - b) ^ 2 := by 
    exact sq_nonneg (a - b)
  have h₃ : 0 ≤  a ^ 2 - 2 * a * b + b ^ 2:= by 
    rw [sub_sq a b] at h₂
    exact h₂
  have h₄ :2*a*b ≤ a^2 + b^2:= by linarith 
  have h₅ : a*b ≤ (a^2 + b^2)/2 := by 
    linarith 
  exact h₅

lemma NormSq_eq_Norm_NormSq (u : W ): ⟪ u,u⟫_ℝ = ‖⟪ u,u⟫_ℝ‖ := by
  have ta : 0 ≤ ⟪u,u⟫_ℝ := by exact real_inner_self_nonneg
  exact Eq.symm (Real.norm_of_nonneg ta)
  
lemma Simplification ( u v : W ): ‖⟪ u+v ,u+v ⟫_ℝ‖ ≤ 2 *(‖⟪ u, u ⟫_ℝ‖ + ‖⟪ v, v ⟫_ℝ‖ ) := by
/- ‖
 <u+v, u+v>= normsq(u)+normsq(v) + <u,v > + < v, u>=

  =normsq(u)+normsq(v) + 2* re (<u,v >) <= normsq(u)+normsq(v) + 2 * | <u,v >|

  <= normsq(u)+normsq(v) + 2* norm(u) norm(v) <=2(normsq(u)+normsq(v) )
-/  
  calc ‖⟪ u+v ,u+v ⟫_ℝ‖ 
      = ‖( ‖u‖^2 + ‖ v‖^2 + ⟪u, v⟫_ℝ + ⟪v, u⟫_ℝ )‖ := by
        rw [expansion_normsq_add]
        
    _=‖( ‖u‖^2 + ‖ v‖^2 + 2* ⟪u, v⟫_ℝ  )‖:= by 
      rw [← inner_conj_symm v u]
      have := Complex.add_conj
      simp only [this, add_assoc]
      norm_cast
      simp
      congr 
      rw [real_inner_comm v u]
      exact Eq.symm (two_mul ⟪v,u⟫_ℝ )

    _≤ ‖ ‖u‖^2‖ +‖ ‖ v‖^2‖ + ‖2* ⟪u, v⟫_ℝ‖:= by 
      exact norm_add₃_le _ _ _
    _≤ ‖u‖^2 + ‖ v‖^2 + 2*‖⟪u, v⟫_ℝ‖:=by
      simp
      
      
    _≤ ‖u‖^2 + ‖ v‖^2 + 2*(‖u‖*‖v‖) :=by
      simp
      simp [norm_inner_le_norm u v]
      exact abs_real_inner_le_norm u v
      
    _≤‖u‖^2 + ‖ v‖^2+ 2*((1/2)*(‖u‖^2 + ‖v‖^2) ):= by 
      simp
      apply smul_le
      exact arithmetic_mean_le_geometric_mean ‖u‖ ‖v‖
    _=2*(‖ u‖^2 + ‖ v‖^2) :=by 
      simp
      exact Eq.symm (two_mul (‖u‖ ^ 2 + ‖v‖ ^ 2))
    _=2*(⟪u,u⟫_ℝ  + ⟪ v,v⟫_ℝ  ):=by 
      simp
      congr
      · exact Eq.symm (normsq u)
      · exact Eq.symm (normsq v) 
    _= 2 *(‖⟪ u, u ⟫_ℝ‖ + ‖⟪ v, v ⟫_ℝ‖ ):=by
      
      rw [NormSq_eq_Norm_NormSq u,NormSq_eq_Norm_NormSq v]
      simp

    
    
lemma Abs_Summanle_Summable (f : ℕ → ℝ  ) : Summable f ↔ Summable (fun  i ↦ ‖f i‖) := by
  rw [Iff.comm]
  exact summable_norm_iff
  


theorem HilbertBasis.HilbertSchmidtSummable_add (e : HilbertBasis I ℝ V) (T₁ T₂ : V →ₗ[ℝ] W)
  (h₁ : e.HilbertSchmidtSummable T₁) (h₂ : e.HilbertSchmidtSummable T₂) :
    e.HilbertSchmidtSummable (T₁ + T₂) := by
  /- <(T₁ + T₂)e i,(T₁ + T₂)e i>= normsq(T₁ e i)+normsq(T₂ e i) + <T₁ e i,T₂ e i > + < T₂ e i, T₁ e i>=

  =normsq(T₁ e i)+normsq(T₂ e i) + 2* re (<T₁ e i,T₂ e i >) <= normsq(T₁ e i)+normsq(T₂ e i) + 2 * | <T₁ e i,T₂ e i >|

  <= normsq(T₁ e i)+normsq(T₂ e i) + 2* norm(T₁ e i) norm(T₂ e i) <=2(normsq(T₁ e i)+normsq(T₂ e i) )

  -/
  --simp only [HilbertSchmidtSummable]
  unfold HilbertSchmidtSummable at *
  apply summable_norm_iff.1
  -- simp only [LinearMap.add_apply]
  --simp only [inner_add_left,inner_add_right]
  --simp only [HilbertBasis.HilbertSchmidtSummable] 
  --simp only [HilbertBasis.repr_symm_single]
  --simp only [InnerProductSpace.Core.inner_add_add_self]--to expand inner(x+y)(x+y)
  apply summable_of_nonneg_of_le
  · exact fun b =>
    norm_nonneg _ 
  · intro b 
    exact Simplification _ _
  · apply Summable.mul_left
    apply Summable.add 
    · apply summable_norm_iff.2
      exact h₁
    · apply summable_norm_iff.2
      exact h₂
--have := @inner_mul_inner_self_le -- This is Cauchy-Schwarz inequality.

/-Theorem: Set ( Not space at that point because we did not yet prove : set of all HS operators is a vector space) of all HS operators is closed under scalar multiplication-/
theorem HilbertBasis.HilbertSchmidtSummable_smul (e : HilbertBasis I ℝ V) (c : ℝ) (T : V →ₗ[ℝ] W)
  (h : e.HilbertSchmidtSummable T) :
    e.HilbertSchmidtSummable (c • T) := by
unfold HilbertSchmidtSummable at *
simp only [LinearMap.smul_apply, inner_smul_left,inner_smul_right]
apply Summable.mul_left
apply Summable.mul_left
exact h

/-Proving that set of all HS operators is a subspace-/
def HilbertSchmidt_SubSpace (e : HilbertBasis I ℝ V) : Submodule ℝ (V →ₗ[ℝ] W) where
  carrier := {T | e.HilbertSchmidtSummable T}
  add_mem' := by 
    intro a
    intro b 
    intro ha 
    intro hb
    exact HilbertBasis.HilbertSchmidtSummable_add _ a b ha hb
  zero_mem' := by
    simp
    simp only [HilbertBasis.HilbertSchmidtSummable ]
    simp
    exact summable_zero
  smul_mem' := by 
    intro c 
    intro x
    intro hx 
    exact HilbertBasis.HilbertSchmidtSummable_smul _ _ _ hx

open ContinuousLinearMap (adjoint)

/-HS summability is independent of Hilbert Basis-/
lemma HilbertSchmidtSummable_key (e : HilbertBasis I ℝ V) (f : HilbertBasis J ℝ W) 
  (T : V →L[ℝ] W) (h : e.HilbertSchmidtSummable (T : V →ₗ[ℝ] W)) : 
    f.HilbertSchmidtSummable (adjoint T : W →ₗ[ℝ] V) := by
  unfold HilbertBasis.HilbertSchmidtSummable at *
  rcases h with ⟨A, hA⟩
  have claim1 : ∀ i, HasSum (fun j ↦ ‖⟪f j, T (e i)⟫_ℝ‖^2) ⟪T (e i), T (e i)⟫_ℝ := by
    sorry
  have claim2 : HasSum (fun (ij : I × J) ↦ ‖⟪f ij.2, T (e ij.1)⟫_ℝ‖^2) A := by
    sorry
  sorry

theorem HilbertBasis.HilbertSchmidtSummable' (e : HilbertBasis I ℝ V) (T : V →ₗ[ℝ] W)
  (h : e.HilbertSchmidtSummable T) (f : HilbertBasis I ℝ V) :
    f.HilbertSchmidtSummable T := by

  
  sorry

open LinearMap (range)
open Filter

/-Definition of finite rank operator-/
def IsFiniteRank (T : V →ₗ[ℝ] W) : Prop := FiniteDimensional ℝ (range T)

/-Theorem: Every finite rank operator is compact-/
theorem IsFiniteRank.IsCompactOperator (T : V →ₗ[ℝ] W) (H : IsFiniteRank T) : 
    IsCompactOperator T := by
  
  sorry

/-Theorem: Every compact operator is a limit of a sequence of finite rank operators-/
theorem IsCompactOperator_lim_IsFiniteRank (T : V →L[ℝ] W) (H : IsCompactOperator T) : ∃ U : ℕ → V →L[ℝ] W,
    Tendsto U (AtTop) (nhds T) := 
  
  sorry

end hilbert_schmidt -- section
--Radhe Radhe

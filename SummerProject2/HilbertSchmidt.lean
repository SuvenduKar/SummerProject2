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
lemma HilbertSchmidtSummable_Adjoint (e : HilbertBasis I ℝ V) (f : HilbertBasis J ℝ W) 
  (T : V →L[ℝ] W) (h : e.HilbertSchmidtSummable (T : V →ₗ[ℝ] W)) : 
    f.HilbertSchmidtSummable (adjoint T : W →ₗ[ℝ] V) := by
  unfold HilbertBasis.HilbertSchmidtSummable at *
  rcases h with ⟨A, hA⟩
  have claim1 : ∀ i, HasSum (fun j ↦ ‖⟪f j, T (e i)⟫_ℝ‖^2) ⟪T (e i), T (e i)⟫_ℝ := by
    intro i
    have hf: ∀ i, 0≤ (fun j ↦ ‖⟪f j, T (e i)⟫_ℝ‖^2)  := by 
      intro i j
      apply sq_nonneg
    convert f.hasSum_inner_mul_inner (T (e i)) (T (e i)) with j
    simp only [real_inner_comm (f j) (T (e i))]
    simp
    exact sq ⟪ ( f j), T (e i)⟫_ℝ 

  have claim2 : HasSum (fun (ij : I × J) ↦ ‖⟪f ij.2, T (e ij.1)⟫_ℝ‖^2) A := by
    have : Summable (fun (ij : I × J) ↦ ‖⟪f ij.2, T (e ij.1)⟫_ℝ‖^2) := by
      convert claim1
      constructor 
      · intro h 
        exact claim1
        
      · intro hy 
        rw [summable_prod_of_nonneg]
        constructor 
        · intro i
          exact HasSum.summable (claim1 i)
          
        · simp_rw [(claim1 _).tsum_eq]
          exact HasSum.summable hA
        · intro (i, j)
          apply sq_nonneg
          
          

    rcases this with ⟨B, hB⟩
    convert hB
    apply HasSum.unique hA
    apply HasSum.prod_fiberwise hB
    exact claim1
  --have claim3 : ∀ i, HasSum (fun j ↦ ‖⟪(e i), (adjoint T) (f j)⟫_ℝ‖^2) ⟪T (e i), T (e i)⟫_ℝ := by
    --intro i 
    --simp_rw [ContinuousLinearMap.adjoint_inner_right T ( e _) ( f _)]
    --simp_rw [Eq.symm (norm_inner_symm ( f _) (T ( e i))) ]
    --convert f.hasSum_inner_mul_inner (T (e i)) (T (e i)) with j
    --simp only [real_inner_comm (f j) (T (e i))]
    --simp
    --exact sq ⟪ ( f j), T (e i)⟫_ℝ 
  have claim4 : HasSum (fun (ji : J × I) ↦ ‖⟪ (e ji.2),(adjoint T) (f ji.1)⟫_ℝ‖^2) A := by
    simp_rw [ContinuousLinearMap.adjoint_inner_right T ( e _) ( f _)]
    simp_rw [Eq.symm (norm_inner_symm ( f _) (T ( e _))) ]
    rw [← (Equiv.prodComm _ _).hasSum_iff]
    exact claim2
  have claim5 : ∀ j, HasSum (fun i ↦ ‖⟪e i, (adjoint T) (f j)⟫_ℝ‖^2) ⟪(adjoint T) ( f j), (adjoint T) ( f j)⟫_ℝ := by
    intro j
    convert e.hasSum_inner_mul_inner ((adjoint T) (f j)) ((adjoint T) (f j)) with i
    simp only [real_inner_comm (e i) ((adjoint T) (f j))]
    simp
    exact sq ⟪ ( e i),(adjoint T) (f j) ⟫_ℝ 
  exact (HasSum.prod_fiberwise claim4 claim5).summable
/-Hilber Schmidt summability of an operator is independent of Hilbert basis.-/
theorem HilbertBasis.HilbertSchmidtSummable' (e : HilbertBasis I ℝ V) (T : V →L[ℝ] W)
  (h : e.HilbertSchmidtSummable (T : V →ₗ[ℝ] W)) (f : HilbertBasis I ℝ V)(g : HilbertBasis I ℝ W) :
    f.HilbertSchmidtSummable (T : V →ₗ[ℝ] W) := by
  have claim1: g.HilbertSchmidtSummable (adjoint T : W →ₗ[ℝ] V):= by 

    exact HilbertSchmidtSummable_Adjoint e g T h
  
  rw [Eq.symm (ContinuousLinearMap.adjoint_adjoint T)]
  exact HilbertSchmidtSummable_Adjoint _ _ (adjoint T) claim1
  

open LinearMap (range)
open Filter

/-Definition of finite rank operator-/
def IsFiniteRank (T : V →ₗ[ℝ] W) : Prop := FiniteDimensional ℝ (range T)

open BigOperators

theorem IsFiniteRank_Sum_of_FiniteRank (s : Finset I) (T : I → V →ₗ[ℝ] W) (h : ∀ i, IsFiniteRank (T i)) :
    IsFiniteRank (∑ i in s, T i) := by
  unfold IsFiniteRank at *
  have fact1 : range (∑ i in s, T i) ≤ Finset.sup s fun i ↦ range (T i) := by
    induction' s using Finset.cons_induction with i s h IH
    . rw [Finset.sum_empty, Finset.sup_empty, LinearMap.range_zero]
    . rw [Finset.sum_cons, Finset.sup_cons]
      calc range (T i + ∑ x in s, T x) 
        _ ≤ range (T i) ⊔ range (∑ x in s, T x) := by
          rw [LinearMap.range_eq_map, LinearMap.range_eq_map, LinearMap.range_eq_map]
          exact Submodule.map_add_le _ _ _
        _ ≤ range (T i) ⊔ Finset.sup s fun i ↦ range (T i) := sup_le_sup_left IH _
  have fact2 : FiniteDimensional ℝ (Finset.sup s fun i ↦ range (T i) : Submodule ℝ W) := by
    let h := h
    apply Submodule.finiteDimensional_finset_sup
  apply Submodule.finiteDimensional_of_le fact1

/-Theorem: Every finite rank operator is compact-/
theorem IsFiniteRank.IsCompactOperator (T : V →L[ℝ] W) (H : IsFiniteRank (T : V →ₗ[ℝ] W)) : 
    IsCompactOperator (T : V →ₗ[ℝ] W) := by
  haveI : FiniteDimensional ℝ (range T) := H
  rw [isCompactOperator_iff_isCompact_closure_image_ball _ one_pos]
  let S : Set W := (↑) '' (Metric.closedBall 0 ‖T‖ : Set (range T))
  have obs: IsCompact S:= by 
    apply IsCompact.image _ _
    · exact ProperSpace.isCompact_closedBall _ _
    · exact continuous_subtype_val
  
  apply isCompact_of_isClosed_subset obs
  · exact isClosed_closure
    
  · apply closure_minimal 
    · intro x hx 
      rcases hx with ⟨y, hy, hxy⟩
      use ⟨T y, LinearMap.mem_range_self T y⟩
      constructor
      · rw [mem_closedBall_zero_iff]
        rw [mem_ball_zero_iff] at hy
        exact ContinuousLinearMap.unit_le_op_norm T y hy.le
      · exact hxy
    · exact IsCompact.isClosed obs

/-Every finite rank operator is also a HilbertSchmidt operator-/
theorem IsFiniteRank.IsHilbertSchmidtOperator (T : V →L[ℝ] W) (H : IsFiniteRank (T : V →ₗ[ℝ] W)) (e : HilbertBasis I ℝ V): 
    e.HilbertSchmidtSummable (T : V →ₗ[ℝ] W):= by

  sorry
/-Every HilbertSchmidt Operator is compact operator-/
theorem IsHilbertSchmidtOperator.IsCompactOperator (T : V →L[ℝ] W) (e : HilbertBasis I ℝ V) (h:e.HilbertSchmidtSummable (T : V →ₗ[ℝ] W)): 
    IsCompactOperator (T : V →ₗ[ℝ] W):= by

  sorry

/-Theorem: Every compact operator is a limit of a sequence of finite rank operators-/
theorem IsCompactOperator_lim_IsFiniteRank (T : V →L[ℝ] W) (H : IsCompactOperator T) : ∃ U : ℕ → V →L[ℝ] W,
    Tendsto U (AtTop) (nhds T) := by
  
  sorry


section FinalTheorem

variable (T : V →L[ℝ] W) (e : HilbertBasis I ℝ V) (h : e.HilbertSchmidtSummable (T : V →ₗ[ℝ] W))

noncomputable def U : (Finset I) → V →L[ℝ] W :=
  fun s ↦ ∑ i in s, (innerSL ℝ (e i)).smulRight (T (e i))

lemma U_def (s : Finset I) (x : V) : U T e s x = ∑ k in s, ⟪e k, x⟫_ℝ • (T (e k)) := by
  exact ContinuousLinearMap.sum_apply _ _ _

lemma U_isFiniteRank (s : Finset I) : IsFiniteRank (U T e s : V →ₗ[ℝ] W) := by
  convert IsFiniteRank_Sum_of_FiniteRank s
    (fun i ↦ ((innerSL ℝ (e i)).smulRight (T (e i)) : V →ₗ[ℝ] W)) _
  · ext x
    norm_cast
  · intro i
    unfold IsFiniteRank
    have : FiniteDimensional ℝ (Submodule.span ℝ {T (e i)}) := by
      infer_instance
    have : range ((innerSL ℝ (e i)).smulRight (T (e i)) : V →ₗ[ℝ] W) ≤ Submodule.span ℝ {T (e i)} := by
      intro x hx
      rw [LinearMap.mem_range] at hx
      cases' hx with y hy
      rw [← hy]
      change ⟪e i, y⟫_ℝ • T (e i) ∈ Submodule.span ℝ {T (e i)}
      apply Submodule.smul_mem
      exact Submodule.mem_span_singleton_self _
    apply Submodule.finiteDimensional_of_le this
  
lemma U_of_not_mem (s : Finset I) (i : I) (hi : i ∉ s) :  U T e s (e i) = 0 := by
  rw [U_def]
  apply Finset.sum_eq_zero
  intro k hk 
  have := HilbertBasis.orthonormal e
  rw [this.2]
  · exact zero_smul _ _
  · intro hki
    rw [hki] at hk
    contradiction

lemma U_of_mem (s : Finset I) (i : I) (hi : i ∈ s) :  U T e s (e i) = T (e i) := by
  classical
  rw [U_def]
  have ortho := HilbertBasis.orthonormal e 
  have : T (e i) = ⟪e i, e i⟫_ℝ • T (e i) := by
    rw [orthonormal_iff_ite] at ortho
    rw [ortho, if_pos (rfl : i = i), one_smul]
  rw [this]
  apply Finset.sum_eq_single
  · intro k hk hki
    rw [ortho.2 hki]
    exact zero_smul _ _
  · intro hi
    contradiction

lemma U_tendsto : Tendsto (fun s ↦ e.HilbertSchmidtNormSq (T - U T e s : V →ₗ[ℝ] W)) (atTop) (nhds 0) := by
  classical
  convert tendsto_tsum_compl_atTop_zero (fun i ↦ ⟪T (e i), T (e i)⟫_ℝ) with s
  unfold HilbertBasis.HilbertSchmidtNormSq
  change (∑' i, _) = ∑' i : (sᶜ : Set I), _
  rw [tsum_subtype (sᶜ : Set I) (fun i : I ↦ ⟪T (e i), T (e i)⟫_ℝ)]
  congr
  ext i
  rw [Set.indicator_apply]
  split_ifs with hi
  · rw [LinearMap.sub_apply]
    norm_cast
    rw [U_of_not_mem T e s i hi, sub_zero]
  · rw [LinearMap.sub_apply]
    norm_cast
    rw [U_of_mem T e s i (of_not_not hi), sub_self, inner_zero_left]


/-Finite rank operators are dense in the space of Hilbert Schmidt operator-/
theorem IsHilbertSchmidtOperator_lim_IsFiniteRank_HSNorm (T : V →L[ℝ] W) (e : HilbertBasis I ℝ V) (h: e.HilbertSchmidtSummable (T : V →ₗ[ℝ] W)) : 
    ∃ U : (Finset I) → V →L[ℝ] W, (∀ n, IsFiniteRank (U n : V →ₗ[ℝ] W)) ∧ Tendsto (fun n ↦ e.HilbertSchmidtNormSq (T - U n : V →ₗ[ℝ] W)) (atTop) (nhds 0) := by 
  classical
  use U T e
  constructor
  · exact U_isFiniteRank T e
  · exact U_tendsto T e

end FinalTheorem




noncomputable def HilbertBasis.HilbertSchmidtNorm (e : HilbertBasis I ℝ V) : Seminorm ℝ (HilbertSchmidt_SubSpace e : Submodule ℝ (V →ₗ[ℝ] W)) where
  toFun f := Real.sqrt (e.HilbertSchmidtNormSq (f : V →ₗ[ℝ] W))
  map_zero' := by 
    unfold HilbertSchmidtNormSq 
    simp only [map_zero] 
    simp 
  add_le' := by 
    
    sorry
  neg' := by 
    sorry
  smul' := by
    unfold HilbertSchmidtNormSq 
    intro a 
    intro x 
     
    sorry

noncomputable instance (e : HilbertBasis I ℝ V) : SeminormedAddCommGroup (HilbertSchmidt_SubSpace e : Submodule ℝ (V →ₗ[ℝ] W)) :=
  e.HilbertSchmidtNorm.toSeminormedAddCommGroup

/-Finite rank operators are dense in the space of Hilbert Schmidt operator-/
theorem IsHilbertSchmidtOperator_lim_IsFiniteRank (T : V →L[ℝ] W) (e : HilbertBasis I ℝ V) (h: e.HilbertSchmidtSummable (T : V →ₗ[ℝ] W)) : ∃ U : ℕ → V →L[ℝ] W,
    Tendsto U (AtTop) (nhds T) :=by 
  
  sorry


end hilbert_schmidt -- section
--Radhe Radhe

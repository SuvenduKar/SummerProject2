import Mathlib.Analysis.NormedSpace.CompactOperator
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.LibrarySearch

-- Let V and W be inner product spaces over ℂ.
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

#check tsum
#check OrthonormalBasis
#check LinearMap

/-- The trace of a linear map with respect to a given `OrthonormalBasis`.

Comment by Kalle:
 * The inner product in Mathlib is in fact linear with respect to the second argument, so I changed
   the definition accordingly. -/
noncomputable def OrthonormalBasis.trace [Fintype I] (e : OrthonormalBasis I ℂ V) (T : V →ₗ[ℂ] V) : ℂ :=
  ∑' i, ⟪e i, T (e i)⟫_ℂ 

noncomputable def HilbertBasis.trace (e : HilbertBasis I ℂ V) (T : V →ₗ[ℂ] V) : ℂ :=
  ∑' i, ⟪e i, T (e i)⟫_ℂ 

lemma OrthonormalBasis.trace_eq_trace [Fintype I] [Fintype J] 
  (e : OrthonormalBasis I ℂ V) (f : OrthonormalBasis J ℂ V) (T : V →ₗ[ℂ] V) : 
    e.trace T = f.trace T := by
  sorry

/-- Trace class operators are those linear maps for which the series defining the trace
w.r.t. some Hilbert basis is summable. -/
class TraceClass (T : V →ₗ[ℂ] V) where
  exists_trace : ∃ (e : HilbertBasis I ℂ V), Summable (fun i ↦ ⟪e i, T (e i)⟫_ℂ)

/-- For a trace class operator, the series defining the trace w.r.t. any Hilbert
basis is summable. -/
lemma TraceClass.summable (T : V →ₗ[ℂ] V) [TraceClass T] (e : HilbertBasis I ℂ V) : 
    Summable (fun i ↦ ⟪e i, T (e i)⟫_ℂ) := by
  sorry

lemma TraceClass.trace_eq_trace (T : V →ₗ[ℂ] V) [TraceClass T]
  (e : HilbertBasis I ℂ V) (f : HilbertBasis J ℂ V) : 
    e.trace T = f.trace T := by
  sorry

lemma HilbertBasis.trace_add (e : HilbertBasis I ℂ V) (T₁ T₂ : V →ₗ[ℂ] V)
  [TraceClass T₁] [TraceClass T₂] : 
    e.trace (T₁ + T₂) = e.trace T₁ + e.trace T₂ := by
  -- Math proof?
  --   tr(T₁ + T₂)
  -- = ∑' i, ⟪e i, (T₁ + T₂) (e i)⟫_ℂ                       
  -- = ∑' i, ⟪e i, T₁ (e i) + T₂ (e i)⟫_ℂ
  -- = ∑' i, (⟪e i, T₁ (e i)⟫_ℂ + ⟪e i, T₂ (e i)⟫_ℂ)
  -- = ∑' i, ⟪e i, T₁ (e i)⟫_ℂ + ∑' i, ⟪e i, T₂ (e i)⟫_ℂ
  -- = tr(T₁) + tr(T₂)
  repeat rw [trace]
  simp only [LinearMap.add_apply]
  simp only [inner_add_right]
  rw [tsum_add]
  ·
    exact TraceClass.summable T₁ e
  --exact TraceClass.summable T₂ e
  . exact TraceClass.summable T₂ e 

lemma OrthonormalBasis.trace_add [Fintype I]  
  (e : OrthonormalBasis I ℂ V) (T₁ T₂ : V →ₗ[ℂ] V) : 
    e.trace (T₁ + T₂) = e.trace T₁ + e.trace T₂ := by
  -- Math proof?
  --   tr(T₁ + T₂)
  -- = ∑' i, ⟪e i, (T₁ + T₂) (e i)⟫_ℂ                       
  -- = ∑' i, ⟪e i, T₁ (e i) + T₂ (e i)⟫_ℂ
  -- = ∑' i, (⟪e i, T₁ (e i)⟫_ℂ + ⟪e i, T₂ (e i)⟫_ℂ)
  -- = ∑' i, ⟪e i, T₁ (e i)⟫_ℂ + ∑' i, ⟪e i, T₂ (e i)⟫_ℂ
  -- = tr(T₁) + tr(T₂)
  repeat rw [trace]
  -- rw [LinearMap.add_apply] -- Doesn't work, doesn't rewrite under binders.
  simp only [LinearMap.add_apply]
  simp only [inner_add_right]
  rw [tsum_add]
  · have observe_first := @hasSum_fintype ℂ I _ _ _ (fun i ↦ ⟪e i, T₁ (e i)⟫_ℂ) 
    --have then_it_follows := observe_first.summable 
    --have then_it_follows := HasSum.summable observe_first
    exact observe_first.summable
  · have observe_second := @hasSum_fintype ℂ I _ _ _ (fun i ↦ ⟪e i, T₂ (e i)⟫_ℂ)
    exact observe_second.summable


  
 
--trace(α • T)=α * T , for a traceclass operator T.
lemma HilbertBasis.trace_smul (e : HilbertBasis I ℂ V) (α : ℂ) (T : V →ₗ[ℂ] V)
  [TraceClass T] :
   e.trace (α • T) = α * e.trace T := by
   simp only  [trace]
   simp only [LinearMap.smul_apply]
   simp only [inner_smul_right]
   rw [tsum_mul_left]
   
   --set_option maxHeartbeats 0
    
    --simp only [inner_smul_right]





   
   
   
  
  

lemma OrthonormalBasis.trace_smul [Fintype I] 
  (e : OrthonormalBasis I ℂ V) (α : ℂ) (T : V →ₗ[ℂ] V) : 
    e.trace (α • T) = α * e.trace T := by
  sorry

variable [Fintype I] [DecidableEq I] (e : OrthonormalBasis I ℂ V) (i : I) 

#check e.repr_self i 

#check EuclideanSpace.single

#check OrthonormalBasis.sum_repr 

#check tsum_eq_sum 

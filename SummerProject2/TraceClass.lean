import Mathlib.Analysis.NormedSpace.CompactOperator
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.LibrarySearch

-- Let V and W be inner product spaces over ℂ.
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

#check tsum
#check OrthonormalBasis
#check HilbertBasis
#check LinearMap
/-WARNING:This Whole Document is Only for The Operators for which T = | T | , holds -/
/-- The trace of a linear map with respect to a given `HilbertBasis`.-/
noncomputable def HilbertBasis.trace (e : HilbertBasis I ℂ V) (T : V →ₗ[ℂ] V) : ℂ :=
  ∑' i, ⟪e i, T (e i)⟫_ℂ 

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
  · -- library_search
    exact TraceClass.summable T₁ e
  · exact TraceClass.summable T₂ e


--#check e.repr_self i 
#check EuclideanSpace.single
#check OrthonormalBasis.sum_repr 
#check tsum_eq_sum 



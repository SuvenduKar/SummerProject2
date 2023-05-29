import Mathlib.Analysis.NormedSpace.CompactOperator
import Mathlib.Analysis.InnerProductSpace.PiL2


#check IsCompactOperator 

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

#eval 2+2

#eval 2*5

#check tsum

#check OrthonormalBasis

#check LinearMap

noncomputable def OrthonormalBasis.trace [Fintype I] (e : OrthonormalBasis I ℂ V) (T : V →ₗ[ℂ] V) : ℂ :=
  ∑' i, ⟪T (e i), e i⟫_ℂ 


lemma OrthonormalBasis.trace_eq_trace [Fintype I] [Fintype J] 
  (e : OrthonormalBasis I ℂ V) (f : OrthonormalBasis J ℂ V) (T : V →ₗ[ℂ] V) : 
    e.trace T = f.trace T := by
  sorry

lemma OrthonormalBasis.trace_add [Fintype I]  
  (e : OrthonormalBasis I ℂ V) (T₁ T₂ : V →ₗ[ℂ] V) : 
    e.trace (T₁ + T₂) = e.trace T₁ + e.trace T₂ := by
  sorry

lemma OrthonormalBasis.trace_smul [Fintype I] 
  (e : OrthonormalBasis I ℂ V) (α : ℂ) (T : V →ₗ[ℂ] V) : 
    e.trace (α • T) = α * e.trace T := by
  sorry

variable [Fintype I] [DecidableEq I] (e : OrthonormalBasis I ℂ V) (i : I) 

#check e.repr_self i 

#check EuclideanSpace.single

#check OrthonormalBasis.sum_repr 

#check tsum_eq_sum 






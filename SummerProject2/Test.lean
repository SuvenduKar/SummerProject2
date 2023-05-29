import Mathlib.Analysis.NormedSpace.CompactOperator
import Mathlib.Analysis.InnerProductSpace.PiL2


#check IsCompactOperator 

variable (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]

variable (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]

#eval 2+2

#eval 2*5

#check tsum

#check OrthonormalBasis

#check LinearMap

noncomputable def OrthonormalBasis.trace [Fintype I] (e : OrthonormalBasis I ℂ V) (T : V →ₗ[ℂ] V) : ℂ :=
  ∑' i, ⟪T (e i), e i⟫_ℂ 






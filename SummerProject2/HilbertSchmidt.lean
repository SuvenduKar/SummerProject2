import Mathlib.Analysis.NormedSpace.CompactOperator
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.GCongr



section hilbert_schmidt

-- Let V and W be Hilbert spaces over ℂ.
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]


/-- The property that `∑ i, ⟪T (e i), T (e i)⟫` is summable for a given Hilbert basis `e`. -/
def HilbertBasis.HilbertSchmidtSummable (e : HilbertBasis I ℂ V) (T : V →ₗ[ℂ] W) :=
  Summable (fun i ↦ ⟪T (e i), T (e i)⟫_ℂ)

/-- The sum `∑ i, ⟪T (e i), T (e i)⟫`, i.e., the HS norm squared. -/
noncomputable def HilbertBasis.HilbertSchmidtNormSq (e : HilbertBasis I ℂ V) (T : V →ₗ[ℂ] W) :=
  ∑' i, ⟪T (e i), T (e i)⟫_ℂ

/-- Hilbert-Schmidt operators. -/
class HilbertSchmidt (T : V →ₗ[ℂ] W) where
  exists_summable : ∃ (e : HilbertBasis I ℂ V), e.HilbertSchmidtSummable T

lemma HilbertBasis.HilbertSchmidtSummable_add (e : HilbertBasis I ℂ V) (T₁ T₂ : V →ₗ[ℂ] W)
  (h₁ : e.HilbertSchmidtSummable T₁) (h₂ : e.HilbertSchmidtSummable T₂) :
    e.HilbertSchmidtSummable (T₁ + T₂) := by
    --simp only [HilbertSchmidtSummable]
    --unfold HilbertSchmidtSummable at *
  

    --have := @inner_mul_inner_self_le -- This is Cauchy-Schwarz inequality.
  sorry

lemma HilbertBasis.HilbertSchmidtSummable_smul (e : HilbertBasis I ℂ V) (c : ℂ) (T : V →ₗ[ℂ] W)
  (h : e.HilbertSchmidtSummable T) :
    e.HilbertSchmidtSummable (c • T) := by
    --Mathematical Proof: We have T is HS and thus ∑'i,⟪T eᵢ,T eᵢ⟫ exists finitely where is e is Hilbert Basis.
    --Now for a complex number c ,  ∑'i,⟪c • T eᵢ, c •T eᵢ⟫ = sqr(mod(c))∑'i,⟪T eᵢ,T eᵢ⟫, which is again finite.
    --Thus c• T is an HS.
    unfold HilbertSchmidtSummable at *
    simp only [HilbertSchmidtSummable]
    simp only [LinearMap.smul_apply]
    simp only [LinearMap.smul_apply] 
    simp only [inner_smul_left]
    simp only [inner_smul_right]
    --simp only [HilbertBasis.repr_symm_single]
    --simp only [lp.summable_inner]
    simp [ OrthogonalFamily.summable_of_lp]
    --simp [HilbertBasis.repr_self]
    -- HilbertBasis.summable_inner_mul_inner
    sorry

lemma HilbertBasis.HilbertSchmidtSummable' (e : HilbertBasis I ℂ V) (T : V →ₗ[ℂ] W)
  (h : e.HilbertSchmidtSummable T) (f : HilbertBasis I ℂ V) :
    f.HilbertSchmidtSummable T := by
  sorry


end hilbert_schmidt -- section

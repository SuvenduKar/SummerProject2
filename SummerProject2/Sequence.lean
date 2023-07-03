import Mathlib.Tactic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Real.Basic
 

/-
· A sequence of real/complex numplex numbers is a function λ : ℕ → ℝ/ℂ
· Hereby we will give definitions of limit of a sequence and we will prove some theorem about them.
-/

def f : ℕ → ℝ := λ n ↦ n + 1 --Thats how we define a sequence of real numbers.

--Limit of a Sequence

/- Let (aₙ ) be a sequence converges to t, iff for every pre-assigned ε >0 , ∃ a natural number B such that ∀ n >B , | aₙ -t | < ε -/

--Let us define it in Lean.
def TendsTo ( a :ℕ→ ℝ  ) ( t : ℝ ) : Prop :=
∀ ε > 0 , ∃ B : ℕ , ∀ n, B < n → |a n - t| < ε  

--Lets prove that above condition of convergence is necessary as well as sufficient.

theorem TendsTo_def {a : ℕ → ℝ } {t : ℝ } :
  TendsTo a t ↔ ∀ ε , 0 < ε → ∃ B : ℕ, ∀ n, B < n → |a n -t|< ε := by
  
exact Iff.rfl

--Limit of a constant sequence is constant

theorem TendsTo_Const (c : ℝ ) : TendsTo (λ n ↦ c ) c := by

  rw [TendsTo]
  intros ε hε 
  use 1
  intros n hn
  --refine GT.gt.lt ?h
  simp
  exact hε

--If we shift a convergent sequence by a constant (i.e. if we add or substract each term of a sequence by a contstant), then it's limit will also be shifted by same measure.

theorem TendsTo_Add_Const {a : ℕ→ ℝ  } {t  : ℝ } (c : ℝ ) (h : TendsTo a t) :
  TendsTo ( λ n ↦ a n +c ) (t+c) := by

rw [TendsTo]
simp
exact h

--If {aₙ }↦ c , then {- aₙ}↦ (-c)

theorem TendsTo_Neg {a : ℕ → ℝ } {t :ℝ } (ha : TendsTo a t):
  TendsTo (λ n ↦ -a n) (-t):= by

  unfold TendsTo at *
  simp
  have observation : ∀ (x :ℝ ), |(-x)| = |x|
  · exact fun x => abs_neg x
  · intros ε hε 
    specialize ha ε hε
    cases ha with 
    | intro B hB =>
      use B 
      intros n hn
      specialize hB n hn
      rw [ ← observation] 
      simp 
      have obs : ∀ ( x y : ℝ ), |(x-y)|=|(-y+x)|
      · intros x y
        --rw [sub_eq_neg_add]
        congr
        exact sub_eq_neg_add x y
      · rw [← obs]
        assumption


--If (aₙ ) and (bₙ ) are two sequences converging to t,u respectively , then the sequence (aₙ + bₙ ) is also convergent and converges to t+u
lemma obs1 ( X Y n: ℝ ) : max X Y <  n ↔ X < n ∧ Y < n := by 
  exact max_lt_iff

lemma obs2 (x y a :ℝ ) (ha : -(a/2) < x) (hb: -(a/2) < y) : -a< x+y := by
  linarith
  

theorem   TendsTo_Add { a b : ℕ → ℝ  } {t u : ℝ }
  (ha : TendsTo a t) (hb : TendsTo b u) :
  TendsTo (λ n ↦ a n + b n) (t + u) := by
  unfold TendsTo at *
  intros ε hε
  specialize ha (ε/2) (by linarith)
  specialize hb (ε/2) ( by linarith)
  cases ha with
  | intro X hX => 
  cases hb with 
  | intro Y hY => 
  use max X Y 
  intros n hn 
  specialize hX n _
  · rw [max_lt_iff] at hn
    cases hn with
    | intro fX fY => 
      exact fX
  · rw [max_lt_iff] at hn 
    specialize hY n _
    · cases hn with 
      | intro fX fY => 
        exact fY 
    rw [abs_lt] at *
    constructor
    · --linarith
      cases hX with 
      | intro h1 h2 => 
      cases hY with
      | intro h3 h4 => 
        simp only [neg_lt_sub_iff_lt_add]
        linarith
      --exact obs2 (a n -t) (b n - u) ε h1 h3 (by linarith)

      
    · cases hX with 
      | intro h1 h2 => 
      cases hY with
      | intro h3 h4 => 
      simp
      linarith

--If (aₙ ) and (bₙ ) are two sequences converging to t,u respectively , then the sequence (aₙ - bₙ ) is also convergent and converges to t-u

theorem TendsTo_Sub { a b : ℕ → ℝ  } {t u : ℝ }
  (ha : TendsTo a t) (hb : TendsTo b u) :
  TendsTo (λ n ↦ a n - b n) (t - u) := by

  simp only [sub_eq_add_neg]
  apply TendsTo_Add
  · exact ha
  · exact TendsTo_Neg hb


--Let {aₙ} be a sequence converging to t and c be a scalar.Then {c. aₙ} is a convergent sequence and converges to c.t
--When c is positive
lemma obs3 (ε  c : ℝ ) (hc : 0<c): ε  > 0 → (ε /c) > 0 := by
  exact fun a_1 => div_pos a_1 hc

lemma  pos_mul_inv_eq_one (c :ℝ ) (hc :0< c) :  c * c⁻¹ =1 := by
  rw [inv_eq_one_div]
  --refine mul_one_div_cancel ?h
  rw [mul_one_div_cancel]
  exact ne_of_gt hc 




lemma mod_ope ( a b c :ℝ ) (hc : 0 < c)(hb: b > 0) : |a|< b/c → |c*a|<b := by
  simp only [abs_lt] at *
  intro f 
  cases f with 
  | intro f1 f2 => 
    constructor
    · refine Iff.mp (div_lt_iff' hc) ?intro.left.a
      simp at f1
      rw [neg_div c b]
      exact f1
    · exact Iff.mp (lt_div_iff' hc) f2


  

lemma obs4 ( a b c ε  : ℝ ) (hc: 0<c) (hε: ε > 0 ) ( ha :|a-b|<ε /c) : |c*a-c*b|<ε := by 
  rw [Eq.symm (mul_sub c a b)]
  exact mod_ope (a - b) ε c hc hε ha
  


    


  

theorem TendsTo_Pos_Smul {a : ℕ → ℝ } {t : ℝ } ( ha : TendsTo a t)
  {c : ℝ  }( hc: 0 < c) : TendsTo (λ n ↦ c* a n ) (c * t):= by

  unfold TendsTo at * 
  intro ε hε 
  specialize ha (ε/c) _
  · exact obs3 ε c hc hε
  · cases ha with
    | intro B hB => 
    use B
    intro n hn
    specialize hB n hn
    exact obs4 (a n) t c ε hc hε hB
    
--Wnen c is negetive

theorem TendsTo_Neg_Smul {a : ℕ → ℝ } {t : ℝ } ( ha : TendsTo a t)
  {c : ℝ  }( hc: c < 0) : TendsTo (λ n ↦ c* a n ) (c * t):= by

  have h : 0 < -c := by exact Iff.mpr neg_pos hc
  unfold TendsTo at *
  intro ε hε 
  specialize ha (ε/(-c)) _
  · exact obs3 ε (-c) h hε
    
  · cases ha with
    | intro X hX => 
    use X 
    intro n hn 
    specialize hX n hn 
    rw [← mul_sub,abs_mul,abs_of_neg hc]
    exact Iff.mp (lt_div_iff' h) hX



--When c is in general a constant

theorem TendsTo_Cons_Smul {a : ℕ → ℝ } {t : ℝ } ( ha : TendsTo a t)
  (c : ℝ  ) : TendsTo (λ n ↦ c* a n ) (c * t):= by

  obtain (hc | hc | hc) := lt_trichotomy 0 c --have + cases
  · exact TendsTo_Pos_Smul ha hc
    
  · unfold TendsTo at *
    intro ε hε 
    specialize ha ε hε 
    cases ha with
    | intro B hB => 
      use B 
      intro n hn 
      specialize hB n hn 
      rw [← mul_sub, mul_eq_zero_of_left (id (Eq.symm hc)) ( a n -t)]
      simp 
      exact hε 

  · exact TendsTo_Neg_Smul ha hc

theorem TendsTo_Smul_Const {a : ℕ → ℝ } {t : ℝ } ( ha : TendsTo a t)
  (c : ℝ  ) : TendsTo (λ n ↦ a n * c ) (t * c):= by

  convert TendsTo_Cons_Smul ha c using 1
  · refine Eq.symm (funext ?h.e'_1.h)
    intro x 
    exact mul_comm c (a x)
    
  · exact mul_comm t c
    


--Theorem: Let (aₙ),(bₙ) be two sequences and (aₙ - bₙ ) converges to t , (bₙ) tends to u.Then (aₙ) is convergent and converges to t+u.

theorem TendsTo_of_TendsTo_Sub { a b : ℕ → ℝ } { t u : ℝ }
  (h1: TendsTo (λ n ↦ a n -b n) (t)) (h2 : TendsTo b u) : TendsTo a (t+u) := by
  
  have : (a-b)+b =a := by simp
  rw [← this]
  exact TendsTo_Add h1 h2
  

--Theorem: Let (aₙ ) be a sequence tends to t , then ( aₙ -t ) tends to 0.

theorem TendsTo_Sub_Lim_Iff {a : ℕ → ℝ } {t : ℝ } : TendsTo a t ↔ TendsTo (λ n ↦ a n -t) 0 := by

  constructor 
  intro h 
  · have :0=t-t :=by simp
    rw [this]
    exact TendsTo_Sub h (TendsTo_Const t)
    
  · intro h 
    have : t=0+t := by simp
    have i : ∀ (n : ℕ), a n = (a n-t)+t := by simp
    rw [ this]
    refine TendsTo_of_TendsTo_Sub h (TendsTo_Const t)

--Theorem: Let (aₙ), (bₙ) both tends to zero.Then (aₙ * bₙ ) also tends to zero.

theorem TendsTo_Zero_Mul_TendsTo_Zero { a b : ℕ → ℝ } (ha : TendsTo a 0) (hb : TendsTo b 0) : TendsTo (λ n ↦ a n * b n ) 0 := by

  unfold TendsTo at *
  intro ε hε 
  specialize ha ε hε 
  specialize hb 1 (by simp) 
  cases ha with 
  | intro B hB => 
  cases hb with 
  | intro X hX => 
  use max B X 
  intro n hn 
  specialize hB n _
  · rw [max_lt_iff ] at hn 
    cases hn with
    | intro k l => 
      exact k
     
  · specialize hX n _ 
    · rw [max_lt_iff] at hn
      cases hn with 
      | intro k l => 
        exact l
      
    · simp [abs_mul] at *
      refine mul_lt_of_lt_of_le_one_of_nonneg hB ?intro.intro.ha ?intro.intro.hb
      · exact LT.lt.le hX
        
      · exact abs_nonneg (a n)
--Theorem: Every convergent sequences are bounded.
def BddSeq ( a :ℕ→ ℝ  )  : Prop :=
 ∃ C : ℝ , ∀ (n : ℕ) ,  |a n|≤  C 

theorem TendsTo_Bdd {a :ℕ → ℝ   } {t :ℝ }(ha: TendsTo a t ): BddSeq a := by 
  unfold BddSeq at *
  unfold TendsTo at *
  specialize ha 1 (by simp)
  cases ha with 
  | intro B hB => 
  sorry  

--Theorem: Let, (aₙ ), (bₙ ) be two sequences converges to t , u respectively. Then the sequence (aₙ*bₙ) is convergent snd converges to t*u.

theorem TendsTo_of_Mul_TendsTo { a b : ℕ → ℝ } {t u :ℝ } (ha : TendsTo a t) (hb : TendsTo b u) : TendsTo (λ n ↦ a n * b n ) (t*u) := by

 rw [TendsTo_Sub_Lim_Iff] at *
 have h : ∀ n, a n * b n - t* u = ( a n - t)* ( b n -u)+ t * ( b n -u) + ( a n -t)*u 
 ·ring_nf
  simp 
  
 ·simp [h]
  rw [ show ( 0 : ℝ ) = 0+0+0  by simp]
  refine TendsTo_Add ?ha ?hb
  refine TendsTo_Add ?ha.ha ?ha.hb
  · exact TendsTo_Zero_Mul_TendsTo_Zero ha hb
    
  · have y : 0=0*t
    exact Eq.symm (zero_mul t)
    rw [y]
    rw [mul_comm 0 t]
    exact TendsTo_Cons_Smul hb t
    

  have z : 0=0*u 
  exact Eq.symm (zero_mul u)
  rw [z]
  exact TendsTo_Smul_Const ha u

--Theorem: If a sequence is convergent , then converge to a unique limit point.


lemma lt_max_plus_one ( x y : ℕ  ): x < (max x y )+1 := by 
  obtain( f| g| h) := lt_trichotomy x y
  · rw [max_def]
    split_ifs with h
    · refine lt_add_of_lt_of_pos' f ?inl.ha
      exact Nat.zero_lt_one
    
    · simp
    
  · rw [max_def]
    split_ifs with h1
    · rw [g]
      simp
      
    · simp
      
     
  · rw [max_def]
    split_ifs with h 
    refine lt_add_of_le_of_pos h ?inr.inr.inl.ha
    · simp
    · simp
 
theorem TendsTo_Unique { a : ℕ → ℝ } { s t : ℝ }
  ( ha : TendsTo a s) (hb : TendsTo a t) : s=t :=by
  unfold TendsTo at *
  obtain ( f| g | h) := lt_trichotomy t s
  · set ε :=s -t with hε 
    have hε : 0< ε :=by exact Iff.mpr sub_pos f
    specialize ha (ε/2 ) (by linarith)
    specialize hb (ε/2 ) (by linarith)
    cases ha with
    | intro X hX => 
    cases hb with
    | intro Y hY => 
    specialize hX ((max X Y) +1) _
    · refine Iff.mpr Nat.lt_succ ?inl.intro.intro.a
      simp
      
    · specialize hY ((max X Y) +1) _
      · rw [Eq.symm (Nat.max_comm Y X)]
        exact lt_max_plus_one Y X 
        
      · rw [abs_lt ] at hX hY 
        linarith
      
  · rw [g]
  · set ε :=t-s with hε 
    have hε : 0< ε :=by exact Iff.mpr sub_pos h
    specialize ha (ε/2 ) (by linarith)
    specialize hb (ε/2 ) (by linarith)
    cases ha with
    | intro X hX => 
    cases hb with
    | intro Y hY => 
    specialize hX ((max X Y) +1) _
    · exact lt_max_plus_one X Y
      
    · specialize hY ((max X Y) +1) _
      · rw [Eq.symm (Nat.max_comm Y X)]
        exact lt_max_plus_one Y X 
        
      · rw [abs_lt ] at hX hY 
        linarith
    
















                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                
import Mathlib.Tactic.Basic
import Mathlib.Tactic.LibrarySearch
--import Mathlib.Tactic.LeftRight


lemma and_or_distrib_left (P Q R : Prop) : P ∧  (Q ∨ R ) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  · intro h 
    cases h with
    | intro hP hQR =>
      cases hQR with
      | inl hQ =>
        left
        constructor
        exact hP
        exact hQ
      | inr hR =>
        right 
        constructor
        exact hP
        exact hR
  · intro g
    constructor
    cases g with
    | inl hPQ =>
      cases hPQ with
      | intro hP hQ =>
        exact hP
    | inr hPR =>
      cases hPR with
      | intro hP hR =>
        exact hP
    cases g with
    | inl hPQ =>
      left
      cases hPQ with
      | intro hP hQ =>
        exact hQ
    | inr hQR =>
      right 
      cases hQR with
      | intro hQ hR =>
        exact hR
        
        


lemma equiv_neg_neg_self ( P: Prop) : ¬¬P ↔ P := by

constructor
intro h 
· --change ¬ P → False at h
  --change (P → False)→False at h
  by_cases P
  · exact h
  · exfalso
    contradiction 
· intros g a 
  contradiction 


  
  
    





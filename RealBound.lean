import RealModel
import IntegerBound

namespace SidonCompression

/-- The Ruzsa-template lower bound for Sidon subsets of arbitrary finite real sets.
A prime parameter can be chosen separately for each input size. -/
theorem real_sidon_bound (A : Finset ℝ) (q : ℕ) [Fact q.Prime] :
    ∃ S ⊆ A, SidonOn S (fun a b c d => a+b=c+d) ∧
      (2*((q-1)*q))*(q-1)*A.card ≤
        (2*((q-1)*q))*(2*((q-1)*q))*S.card + (q-1)*(A.card.choose 2) := by
  let P (n k : ℕ) := (2*((q-1)*q))*(q-1)*n ≤
    (2*((q-1)*q))*(2*((q-1)*q))*k + (q-1)*(n.choose 2)
  have integerBound (Z : Finset ℤ) : ∃ B ⊆ Z, P Z.card B.card ∧
      ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, ∀ d ∈ B, a+b=c+d →
        (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
    obtain ⟨B,hsub,hs,hn⟩ := integer_sidon_bound Z q
    exact ⟨B,hsub,hn,hs⟩
  obtain ⟨S,hSA,hn,hs⟩ := real_sidon_bound_of_integer P integerBound A
  exact ⟨S,hSA,hs,hn⟩

#print axioms real_sidon_bound
end SidonCompression

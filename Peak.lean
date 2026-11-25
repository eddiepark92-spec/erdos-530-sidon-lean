import RealBound
import Mathlib.Tactic.Linarith

namespace SidonCompression

/-- The rounding error along the optimal sequence of input sizes. -/
private theorem peak_shape (m n : ℕ) (hm : 3 ≤ m) (hn : n=4*m/3) :
    32*m*m + 9*n*n ≤ 36*m*n + 9*n := by
  have hlo : 3*n ≤ 4*m := by omega
  have hhi : 4*m ≤ 3*n+2 := by omega
  zify at hm hlo hhi ⊢
  let r : ℤ := 4*m-3*n
  have hr : 0 ≤ r := by dsimp [r]; omega
  have hr' : r ≤ 2 := by dsimp [r]; omega
  have prod : (4*(m:ℤ))*r ≤ 4*m*2 := by
    exact mul_le_mul_of_nonneg_left hr' (by omega)
  have sq : r*r ≤ 2*2 := mul_le_mul hr' hr' hr (by decide)
  dsimp [r] at prod sq hr'
  nlinarith only [prod,sq,hr',hm]

/-- On the input sizes n=floor(4q(q-1)/3), the optimal leading value of the
second-moment estimate is attained up to integer rounding. -/
theorem real_sidon_peak (A : Finset ℝ) (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q)
    (hn : A.card = 4*((q-1)*q)/3) :
    ∃ S ⊆ A, SidonOn S (fun a b c d => a+b=c+d) ∧ 4*(q-1) ≤ 9*S.card := by
  let m := (q-1)*q
  let b := q-1
  have hp : 0 < q-1 := by omega
  have hm : 3 ≤ m := hq.trans (Nat.le_mul_of_pos_left q hp)
  obtain ⟨S,hSA,hs,h⟩ := real_sidon_bound A q
  refine ⟨S,hSA,hs,?_⟩
  change (2*m)*b*A.card ≤ (2*m)*(2*m)*S.card+b*(A.card.choose 2) at h
  have hc : 2*A.card.choose 2 + A.card ≤ A.card*A.card := by
    rw [Nat.choose_two_right]
    have er : 2 * (A.card * (A.card-1) / 2) ≤ A.card*(A.card-1) := by omega
    have add : A.card*(A.card-1)+A.card=A.card*A.card := by
      cases h : A.card with
      | zero => simp
      | succ a => simp [Nat.mul_succ]
    omega
  have shape := peak_shape m A.card hm hn
  have bound : (8*m*m)*(4*b) ≤ (8*m*m)*(9*S.card) := by
    nlinarith only [Nat.mul_le_mul_left b shape,Nat.mul_le_mul_left (9*b) hc,
      Nat.mul_le_mul_left 18 h]
  exact Nat.le_of_mul_le_mul_left bound (Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega))

#print axioms real_sidon_peak
end SidonCompression

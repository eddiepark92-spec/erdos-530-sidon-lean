import RealBound
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace SidonCompression

private theorem quarter_arithmetic (T Q B S K : ℝ) (ht : 0 < T)
    (hb : 3*T ≤ B) (hl : 2*T ≤ Q) (hu : Q ≤ 6*T) (hk : 2*K ≤ (16*T^2)^2)
    (h : 2*B*Q*(16*T^2) ≤ 4*B*Q^2*S+K) : T ≤ S := by
  have hprod := mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hu)
  have hq : 12*T^2 ≤ Q*(8*T-Q) := by nlinarith only [hprod]
  have hb0 : 0 ≤ B := by linarith
  have hg : 36*T^3 ≤ B*(Q*(8*T-Q)) := calc
    36*T^3 = (3*T)*(12*T^2) := by ring
    _ ≤ _ := mul_le_mul hb hq (by positivity) hb0
  by_contra! hs
  have hs' := mul_le_mul_of_nonneg_left hs.le (show 0 ≤ 4*B*Q^2 by positivity)
  have hg' := mul_le_mul_of_nonneg_left hg (show 0 ≤ 4*T by positivity)
  have hp : 0 < T^4 := by positivity
  nlinarith only [hg',hs',hp,h,hk]

/-- An explicit threshold valid even at small cardinalities. -/
theorem real_sidon_sixteen (A : Finset ℝ) (t : ℕ) (ht : 0 < t) (hA : 16*t^2 ≤ A.card) :
    ∃ S ⊆ A, SidonOn S (fun a b c d => a+b=c+d) ∧ t ≤ S.card := by
  obtain ⟨Z,hZA,hn⟩ := Finset.exists_subset_card_eq hA
  obtain ⟨q,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (3*t) (by omega)
  letI : Fact q.Prime := ⟨hp⟩
  obtain ⟨S,hSZ,hS,h⟩ := real_sidon_bound Z q
  refine ⟨S,hSZ.trans hZA,hS,?_⟩
  let b := q-1
  change (2*(b*q))*b*Z.card ≤ (2*(b*q))*(2*(b*q))*S.card + b*(Z.card.choose 2) at h
  have hcan : b*(2*b*q*Z.card) ≤ b*(4*b*q^2*S.card+Z.card.choose 2) := by nlinarith only [h]
  have hb : 3*t ≤ b := by dsimp [b]; omega
  have hcan' := Nat.le_of_mul_le_mul_left hcan (show 0 < b by omega)
  have hc : 2*Z.card.choose 2 ≤ Z.card^2 := by
    rw [Nat.choose_two_right, pow_two]
    have H := Nat.mul_le_mul_left Z.card (Nat.sub_le Z.card 1)
    omega
  rw [hn] at hcan' hc
  have ht' : (0:ℝ) < t := by exact_mod_cast ht
  have hb' : (3:ℝ)*t ≤ b := by exact_mod_cast hb
  have hl' : (2:ℝ)*t ≤ q := by exact_mod_cast (show 2*t ≤ q by omega)
  have hu' : (q:ℝ) ≤ 6*t := by exact_mod_cast (show q ≤ 6*t by omega)
  have step := quarter_arithmetic (t:ℝ) q b S.card ((16*t^2).choose 2) ht' hb' hl' hu'
    (by exact_mod_cast hc) (by exact_mod_cast hcan')
  exact_mod_cast step

#print axioms real_sidon_sixteen
end SidonCompression

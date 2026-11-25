import IntegerBound
import RealModel
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! An explicit all-cardinality consequence of the cyclic template bound,
using Bertrand's postulate for the target prime. -/
namespace SidonCompression

private theorem cubic {k q : ℤ} (hk : 1 < k) (hlo : k ≤ q) (hhi : q ≤ 2*k) :
    0 ≤ (q-1)*q*(7*k-3*q) - 4*k*k*(k-1) := by
  have bound : 0 ≤ (q-k)*(2*k-q)*(3*q+2*k) :=
    mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
  have adj : 0 ≤ (q-k)*(q*(7*k-3*q)) :=
    mul_nonneg (by omega) (mul_nonneg (by omega) (by omega))
  apply nonneg_of_mul_nonneg_left (b := k) _ (by omega)
  nlinarith only [mul_nonneg bound (show 0 ≤ k-1 by omega), adj]

private theorem arithmetic {r q s : ℤ} (hr : 0 < r) (hlo : 7*r ≤ q) (hhi : q ≤ 14*r)
    (h : 4*(q-1)*q*(16*r*(7*r-1)) ≤
      8*(q-1)*q*q*s + (16*r*(7*r-1))*(16*r*(7*r-1))) :
    24*(7*r-1) ≤ 49*s := by
  have key := cubic (k := 7*r) (q := q) (by omega) hlo (by omega)
  have hkey := mul_nonneg (show 0 ≤ 64*(7*r-1) by omega) key
  have hmul : 0 ≤ (8*(q-1)*q*q)*(49*s-24*(7*r-1)) := by
    nlinarith only [h, hkey]
  have qpos : 0 < q := by omega
  have qpos' : 0 < q-1 := by omega
  have hh := nonneg_of_mul_nonneg_right hmul (by positivity)
  omega

private theorem choose_bound (n : ℕ) : 2*n.choose 2 ≤ n*n := by
  rw [Nat.choose_two_right, Nat.mul_comm 2]
  exact (Nat.div_mul_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

/-- For sets of at least 16r(7r−1) integers the selected Sidon subset
has at least 24(7r−1)/49 elements. -/
theorem bertrand_scale (A : Finset ℤ) (r : ℕ) (hr : 0 < r)
    (hn : 16*r*(7*r-1) ≤ A.card) :
    ∃ S ⊆ A, SidonOn S (fun a b c d => a+b=c+d) ∧ 24*(7*r-1) ≤ 49*S.card := by
  obtain ⟨T, hT, ht⟩ := Finset.exists_subset_card_eq hn
  obtain ⟨q, hq, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (7*r) (by omega)
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨S, hS, hsid, h⟩ := integer_sidon_bound T q
  let b := q-1
  have hb : 0 < b := by dsimp [b]; omega
  have h' : (2*(b*q))*T.card ≤ (4*b*q*q)*S.card + T.card.choose 2 := by
    apply Nat.le_of_mul_le_mul_left _ hb
    change (2*(b*q))*b*T.card ≤ (2*(b*q))*(2*(b*q))*S.card+b*T.card.choose 2 at h
    convert h using 1 <;> ring
  have hd := Nat.mul_le_mul_left 2 h'
  have hn' : 4*b*q*T.card ≤ 8*b*q*q*S.card + T.card*T.card := by
    nlinarith only [hd, choose_bound T.card]
  rw [ht] at hn'
  have q1 : 1 ≤ q := by omega
  have r1 : 1 ≤ 7*r := by omega
  have hh : (4:ℤ)*(q-1)*q*(16*r*(7*r-1)) ≤
      8*(q-1)*q*q*S.card + (16*r*(7*r-1))*(16*r*(7*r-1)) := by
    dsimp [b] at hn'
    exact_mod_cast hn'
  have hs := arithmetic (r := r) (q := q) (s := S.card) (by exact_mod_cast hr)
    (by exact_mod_cast hlo.le) (by exact_mod_cast (show q ≤ 14*r by omega)) hh
  refine ⟨S, hS.trans hT, hsid, ?_⟩
  exact_mod_cast hs

/-- Every integer set of size n contains a Sidon subset of size at least
(6/(7√7))√n − 4. The displayed form is the equivalent integral inequality. -/
theorem strong_bertrand_sidon (A : Finset ℤ) :
    ∃ S ⊆ A, SidonOn S (fun a b c d => a+b=c+d) ∧
      36*A.card ≤ 343*(S.card+4)^2 := by
  let r := Nat.sqrt (A.card / 112)
  have hlow := Nat.sqrt_le (A.card / 112)
  have hhigh := Nat.lt_succ_sqrt (A.card / 112)
  change r*r ≤ A.card / 112 at hlow
  change A.card / 112 < (r+1)*(r+1) at hhigh
  have nlo : 112*(r*r) ≤ A.card := by omega
  have nhi : A.card < 112*((r+1)*(r+1)) := by omega
  by_cases hr : r = 0
  · refine ⟨∅, Finset.empty_subset _, by simp [SidonOn], ?_⟩
    simp [hr] at nhi
    simp only [Finset.card_empty, zero_add]
    omega
  have scale : 16*r*(7*r-1) ≤ A.card := by
    calc
      _ ≤ 16*r*(7*r) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = 112*(r*r) := by ring
      _ ≤ _ := nlo
  obtain ⟨S, hS, hsid, hs⟩ := bertrand_scale A r (by omega) scale
  refine ⟨S, hS, hsid, ?_⟩
  have linear : 24*(r+1) ≤ 7*(S.card+4) := by omega
  have square := Nat.mul_le_mul linear linear
  nlinarith only [square, nhi]
/-- The same bound for every finite set of real numbers. -/
theorem strong_bertrand_sidon_real (A : Finset ℝ) :
    ∃ S ⊆ A, SidonOn S (fun a b c d => a+b=c+d) ∧
      36*A.card ≤ 343*(S.card+4)^2 := by
  let P (n k : ℕ) := 36*n ≤ 343*(k+4)^2
  obtain ⟨S,hsub,hn,hs⟩ := real_sidon_bound_of_integer P (fun Z => by
    obtain ⟨B,hB,hSidon,hcount⟩ := strong_bertrand_sidon Z
    exact ⟨B,hB,hcount,hSidon⟩) A
  exact ⟨S,hsub,hs,hn⟩

#print axioms strong_bertrand_sidon_real
#print axioms strong_bertrand_sidon
end SidonCompression

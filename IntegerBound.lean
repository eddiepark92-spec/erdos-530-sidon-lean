import Compression
import Ruzsa
import LargePrime
import Rounding

namespace SidonCompression

/-- The template bound for every integer input set, after removing the auxiliary
hash field and the associated floors by integrality. -/
theorem template_bound (A : Finset ℤ) {m : ℕ} [hm : NeZero m]
    (B : Finset (ZMod m)) (hB : SidonOn B (fun a b c d => a+b=c+d)) :
    ∃ S ⊆ A, SidonOn S (fun a b c d => a+b=c+d) ∧
      (2*m)*B.card*A.card ≤ (2*m)*(2*m)*S.card + B.card*(A.card.choose 2) := by
  obtain ⟨N,hN⟩ := SidonAffine.eventually_injOn_intCast A
  let d := 2*m
  have hd : 0 < d := Nat.mul_pos (by decide) (Nat.pos_of_ne_zero hm.out)
  let T := d*d*(B.card*A.card)
  obtain ⟨P,hP,prime⟩ := Nat.exists_infinite_primes (max N (T+1))
  letI : Fact P.Prime := ⟨prime⟩
  have hPN := (le_max_left N (T+1)).trans hP
  have hPT : T < P := (le_max_right N (T+1)).trans hP
  let w := P / d
  have hlo : d*w ≤ P := by simpa [w, Nat.mul_comm] using Nat.div_mul_le_self P d
  have hhi : P ≤ d*w+d := by
    simpa only [w, Nat.mul_add, Nat.mul_one] using (Nat.lt_mul_div_succ P hd).le
  have hwindow : 2*(m*w) ≤ P := by simpa only [d,Nat.mul_assoc] using hlo
  obtain ⟨S,hsub,hsid,hcount⟩ := finite_sidon_bound A B (hN P hPN) hwindow hB
  exact ⟨S,hsub,hsid,remove_rounding _ _ _ _ d P w prime.pos hPT hlo hhi hcount⟩

/-- Integer Sidon-subset lower bound for every cardinality and every prime q. -/
theorem integer_sidon_bound (A : Finset ℤ) (q : ℕ) [hq : Fact q.Prime] :
    ∃ S ⊆ A, SidonOn S (fun a b c d => a+b=c+d) ∧
      (2*((q-1)*q))*(q-1)*A.card ≤
        (2*((q-1)*q))*(2*((q-1)*q))*S.card + (q-1)*(A.card.choose 2) := by
  have hq2 := hq.out.two_le
  letI : NeZero ((q-1)*q) := ⟨Nat.mul_ne_zero (by omega) hq.out.ne_zero⟩
  obtain ⟨B, hcard, hB⟩ := ruzsa_target q
  simpa only [hcard] using template_bound A B hB

#print axioms integer_sidon_bound
end SidonCompression

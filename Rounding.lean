import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

namespace SidonCompression

/-- Remove finite-field window rounding: the integral conclusion loses no error
once the auxiliary field size exceeds the displayed elementary threshold. -/
theorem remove_rounding (b n t s d P w : ℕ)
    (hp : 0 < P) (ht : d*d*(b*n) < P)
    (hlo : d*w ≤ P) (hhi : P ≤ d*w+d)
    (h : b*(n*(P*w)) ≤ (P*P)*s+b*(t*(w*w))) :
    d*b*n ≤ d*d*s+b*t := by
  have he : P*(P*(d*b*n)) ≤ P*(P*(d*d*s+b*t)+d*d*(b*n)) := calc
    P*(P*(d*b*n)) = (d*b*n*P)*P := by ring
    _ ≤ (d*b*n*P)*(d*w+d) := Nat.mul_le_mul_left _ hhi
    _ = d*d*(b*(n*(P*w)))+P*(d*d*(b*n)) := by ring
    _ ≤ d*d*((P*P)*s+b*(t*(w*w)))+P*(d*d*(b*n)) := by gcongr
    _ = P*P*(d*d*s) + (b*t)*((d*w)*(d*w)) + P*(d*d*(b*n)) := by ring
    _ ≤ P*P*(d*d*s) + (b*t)*(P*P) + P*(d*d*(b*n)) := by gcongr
    _ = P*(P*(d*d*s+b*t)+d*d*(b*n)) := by ring
  have hc : P*(d*b*n) ≤ P*(d*d*s+b*t)+d*d*(b*n) := (Nat.le_of_mul_le_mul_left he hp)
  by_contra! hf
  have hgap : d*d*s+b*t+1 ≤ d*b*n := hf
  have hm := (Nat.mul_le_mul_left P hgap).trans hc
  rw [Nat.mul_add, Nat.mul_one] at hm
  omega

#print axioms remove_rounding
end SidonCompression

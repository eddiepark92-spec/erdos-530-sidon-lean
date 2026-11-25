import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Sqrt

namespace SidonCompression

open Filter
open scoped Topology

/-- The conventional natural-variable formulation of the prime number theorem. -/
def PrimeCountingPNT : Prop :=
  Tendsto (fun n : ℕ => (n.primeCounting : ℝ) / ((n : ℝ) / Real.log n)) atTop (𝓝 1)

/-- The prime-counting function at a fixed positive multiple of n, normalized
by n/log n. This formulation makes the use of the prime number theorem explicit. -/
theorem scaled_primeCounting (hPNT : PrimeCountingPNT) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n : ℕ => ((⌊r*n⌋₊).primeCounting : ℝ) / ((n : ℝ) / Real.log n))
      atTop (𝓝 r) := by
  let k (n : ℕ) := ⌊r*n⌋₊
  have hk : Tendsto k atTop atTop := tendsto_nat_floor_mul_atTop r hr
  have hfrac : Tendsto (fun n : ℕ => (k n : ℝ) / n) atTop (𝓝 r) :=
    (tendsto_nat_floor_mul_div_atTop hr.le).comp tendsto_natCast_atTop_atTop
  have hbig : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnpos : ∀ᶠ n : ℕ in atTop, 1 < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop 1
  have hkpos : ∀ᶠ n : ℕ in atTop, 1 < (k n : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp hk).eventually_gt_atTop 1
  have hlog : Tendsto (fun n : ℕ => Real.log (k n) / Real.log n) atTop (𝓝 1) := by
    have hz := (hfrac.log hr.ne').div_atTop hbig
    have hc : Tendsto (fun n : ℕ => 1 + Real.log ((k n : ℝ) / n) / Real.log n)
        atTop (𝓝 1) := by simpa using tendsto_const_nhds.add hz
    apply hc.congr'
    filter_upwards [hnpos, hkpos] with n h1 h2
    rw [Real.log_div (by positivity) (by positivity)]
    field_simp [ne_of_gt (Real.log_pos h1)]

  have hp := (show Tendsto _ _ _ from hPNT).comp hk
  have hr' := (hp.mul hfrac).div hlog one_ne_zero
  have t : Tendsto (fun n : ℕ =>
      (((k n).primeCounting : ℝ) / ((k n : ℝ) / Real.log (k n)) * ((k n : ℝ)/n)) /
        (Real.log (k n) / Real.log n)) atTop (𝓝 r) := by
    simpa [Function.comp_def] using hr'
  apply t.congr'
  filter_upwards [hnpos, hkpos] with n h1 h2
  change _ = (↑(k n).primeCounting : ℝ) / ((n : ℝ) / Real.log n)
  field_simp [ne_of_gt (Real.log_pos h1), ne_of_gt (Real.log_pos h2),
    ne_of_gt (zero_lt_one.trans h1), ne_of_gt (zero_lt_one.trans h2)]
  ring

/-- Given the PNT, every fixed multiplicative interval (n,r*n] eventually contains
a prime, with no restriction on the size of the positive relative excess r−1. -/
theorem eventually_prime_in_ratio (hPNT : PrimeCountingPNT) {r : ℝ} (hr : 1 < r) :
    ∀ᶠ n : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ n < p ∧ (p : ℝ) ≤ r*n := by
  have hhi := scaled_primeCounting hPNT (zero_lt_one.trans hr)
  have order := (show Tendsto _ _ _ from hPNT).eventually_lt hhi hr
  have hnpos : ∀ᶠ n : ℕ in atTop, 1 < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop 1
  filter_upwards [order, hnpos] with n h1 hn
  have h2 : n.primeCounting < (⌊r*n⌋₊).primeCounting := by
    exact_mod_cast (div_lt_div_iff_of_pos_right
      (div_pos (zero_lt_one.trans hn) (Real.log_pos hn))).1 h1
  have hcard : (n+1).primesBelow.card < (⌊r*n⌋₊+1).primesBelow.card := by
    simpa only [Nat.primesBelow_card_eq_primeCounting'] using h2
  obtain ⟨p,hp,hp'⟩ := Finset.exists_mem_not_mem_of_card_lt_card hcard
  obtain ⟨hsmall,hpr⟩ := Nat.mem_primesBelow.mp hp
  refine ⟨p,hpr,?_,?_⟩
  · by_contra! hle
    exact hp' (Nat.mem_primesBelow.mpr ⟨by omega, hpr⟩)
  · exact (Nat.cast_le.mpr (Nat.le_of_lt_succ hsmall)).trans
      (Nat.floor_le (mul_nonneg (zero_lt_one.trans hr).le (Nat.cast_nonneg _)))

/-- If every fixed-ratio real interval eventually contains a prime, there is
a prime asymptotic to c√n for each positive c. The chosen prime is the least
prime strictly above c√n. -/
theorem prime_sequence_of_intervals
    (interval : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ x : ℝ in atTop,
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) < (1+ε)*x)
    {c : ℝ} (hc : 0 < c) :
    ∃ q : ℕ → ℕ, (∀ n, (q n).Prime) ∧
      Tendsto (fun n => (q n : ℝ) / Real.sqrt n) atTop (𝓝 c) := by
  classical
  let x (n : ℕ) : ℝ := c*Real.sqrt n
  have hx n : ∃ p : ℕ, p.Prime ∧ x n < p := by
    obtain ⟨k, hk⟩ := exists_nat_gt (x n)
    obtain ⟨p,hkp,hp⟩ := Nat.exists_infinite_primes k
    exact ⟨p,hp,hk.trans_le (Nat.cast_le.mpr hkp)⟩
  let q n := Nat.find (hx n)
  have hq n : (q n).Prime ∧ x n < q n := Nat.find_spec (hx n)
  refine ⟨q,fun n => (hq n).1,?_⟩
  have hs : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (b*b)] with n hn
    exact Real.le_sqrt_of_sq_le (by simpa [pow_two] using hn)
  have hxt : Tendsto x atTop atTop := hs.const_mul_atTop hc
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ints := hxt.eventually (interval (div_pos hε hc))
  filter_upwards [ints,hs.eventually_gt_atTop 0] with n hI hpos
  obtain ⟨p,hp,hlo,hhi⟩ := hI
  have hmin : (q n : ℝ) ≤ p := Nat.cast_le.mpr (Nat.find_min' (hx n) ⟨hp,hlo⟩)
  have qlo : c < (q n : ℝ)/Real.sqrt n := (lt_div_iff₀ hpos).2 (hq n).2
  have qhi : (q n : ℝ)/Real.sqrt n < c+ε := by
    apply (div_lt_iff₀ hpos).2
    apply (hmin.trans_lt hhi).trans_le
    dsimp [x]
    rw [← mul_assoc, add_mul, one_mul, div_mul_cancel₀ _ hc.ne']
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr qlo.le)]
  linarith

#print axioms prime_sequence_of_intervals
#print axioms eventually_prime_in_ratio

end SidonCompression

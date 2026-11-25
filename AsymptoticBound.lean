import RealBound
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp

open Filter Topology
namespace SidonCompression

private noncomputable def profile (x y : ℝ) : ℝ :=
  1 / (2*x) - 1 / (8*y*x^2)

private theorem profile_bound (A : Finset ℝ) (q : ℕ) [hq : Fact q.Prime]
    (hn : 0 < A.card) :
    ∃ S ⊆ A, SidonOn S (fun a b c d => a+b=c+d) ∧
      profile (q / Real.sqrt A.card) ((q-1 : ℕ) / Real.sqrt A.card) *
        Real.sqrt A.card ≤ S.card := by
  obtain ⟨S,hSA,hs,h⟩ := real_sidon_bound A q
  let b := q-1
  have q2 := hq.out.two_le
  have hb : 0 < b := by dsimp [b]; omega
  have h' : (2*(b*q))*A.card ≤ (4*b*q*q)*S.card + A.card.choose 2 := by
    apply Nat.le_of_mul_le_mul_left _ hb
    change (2*(b*q))*b*A.card ≤ (2*(b*q))*(2*(b*q))*S.card+b*A.card.choose 2 at h
    convert h using 1 <;> ring
  have hchoose : 2*A.card.choose 2 ≤ A.card*A.card := by
    rw [Nat.choose_two_right, Nat.mul_comm 2]
    exact (Nat.div_mul_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have hn' : 4*b*q*A.card ≤ 8*b*q*q*S.card + A.card*A.card := by
    nlinarith only [Nat.mul_le_mul_left 2 h',hchoose]
  have hh : (4:ℝ)*b*q*A.card ≤ 8*b*q*q*S.card + A.card*A.card := by exact_mod_cast hn'
  have br : 0 < (b : ℝ) := by exact_mod_cast hb
  have qr : 0 < (q : ℝ) := by exact_mod_cast hq.out.pos
  let r := Real.sqrt A.card
  have hr : 0 < r := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hr2 : r^2 = A.card := Real.sq_sqrt (by positivity)
  have hform : profile (q/r) (b/r)*r =
      (4*b*q*A.card-(A.card:ℝ)^2)/(8*b*(q:ℝ)^2) := by
    rw [← hr2]
    unfold profile
    field_simp [ne_of_gt hr, ne_of_gt qr, ne_of_gt br]
    ring
  refine ⟨S,hSA,hs,?_⟩
  change profile (q/r) (b/r)*r ≤ _
  rw [hform]
  apply (div_le_iff₀ (by positivity)).2
  nlinarith only [hh]

private theorem sqrt_nat_atTop : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop := by
  apply tendsto_atTop.2
  intro x
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually_ge_atTop (x^2)] with n hn
  exact (le_abs_self x).trans (by simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hn)

private theorem profile_peak : profile (Real.sqrt 3/2) (Real.sqrt 3/2) = 2/(3*Real.sqrt 3) := by
  have hz : 0 < Real.sqrt 3 := by positivity
  have hz2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by positivity)
  unfold profile
  field_simp [ne_of_gt hz]
  ring_nf

/-- The optimal constant from affine occupancy at asymptotically optimal prime scales. -/
theorem asymptotic_bound_of_prime_scale (q : ℕ → ℕ) (hp : ∀ n, (q n).Prime)
    (hq : Tendsto (fun n : ℕ => (q n:ℝ) / Real.sqrt n) atTop (𝓝 (Real.sqrt 3/2)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ, A.card=n →
      ∃ S ⊆ A, SidonOn S (fun a b c d => a+b=c+d) ∧
        (2/(3*Real.sqrt 3)-ε)*Real.sqrt n ≤ S.card := by
  let z := Real.sqrt 3 / 2
  have hz : 0 < z := by dsimp [z]; positivity
  have hsmall : Tendsto (fun n : ℕ => 1 / Real.sqrt n) atTop (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop sqrt_nat_atTop
  have hb : Tendsto (fun n : ℕ => (((q n-1 : ℕ):ℝ)) / Real.sqrt n) atTop (𝓝 z) := by
    convert hq.sub hsmall using 1
    · funext n
      simp only [Nat.cast_sub (hp n).one_le,Nat.cast_one, sub_div]
    · simp only [sub_zero, z]
  have hg : Tendsto (fun n : ℕ => profile (q n / Real.sqrt n) ((q n-1 : ℕ) / Real.sqrt n))
      atTop (𝓝 (profile z z)) := by
    unfold profile
    exact (tendsto_const_nhds.div (tendsto_const_nhds.mul hq) (by positivity)).sub
      (tendsto_const_nhds.div ((tendsto_const_nhds.mul hb).mul (hq.pow 2)) (by positivity))
  rw [show profile z z=2/(3*Real.sqrt 3) from profile_peak] at hg
  filter_upwards [hg.eventually_const_lt (show 2/(3*Real.sqrt 3)-ε < 2/(3*Real.sqrt 3) by linarith),
    eventually_ge_atTop (1:ℕ)] with n hpbound hn A hc
  haveI : Fact (q n).Prime := ⟨hp n⟩
  obtain ⟨S,hsub,hs,hsz⟩ := profile_bound A (q n) (by omega)
  rw [hc] at hsz
  exact ⟨S,hsub,hs,(mul_le_mul_of_nonneg_right hpbound.le (Real.sqrt_nonneg _)).trans hsz⟩

#print axioms asymptotic_bound_of_prime_scale
end SidonCompression

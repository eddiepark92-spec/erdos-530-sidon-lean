import AsymptoticBound
import PNTDensity
import PrimeNumberTheoremAnd.Consequences

open Filter Topology
namespace SidonCompression

/-- Every sufficiently large n-element set of reals has a Sidon subset of size
at least (2/(3√3) − ε)√n, for every strictly positive ε. -/
theorem real_sidon_asymptotic (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ, A.card=n →
      ∃ S ⊆ A, SidonOn S (fun a b c d => a+b=c+d) ∧
        (2/(3*Real.sqrt 3)-ε)*Real.sqrt n ≤ S.card := by
  obtain ⟨q, hp, hq⟩ := prime_sequence_of_intervals
    (fun h => prime_between h) (c := Real.sqrt 3/2) (by positivity)
  exact asymptotic_bound_of_prime_scale q hp hq ε hε

#print axioms prime_between
#print axioms real_sidon_asymptotic
end SidonCompression

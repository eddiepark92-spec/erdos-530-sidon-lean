import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod

namespace SidonAffine

/-- Reducing an arbitrary finite integer set modulo any sufficiently large
natural number is injective. The modulus need not be prime. -/
theorem eventually_injOn_intCast (A : Finset ℤ) :
    ∃ N : ℕ, ∀ p ≥ N, Set.InjOn (fun a : ℤ => (a : ZMod p)) (A : Set ℤ) := by
  let D := (A.product A).sup (fun z : ℤ × ℤ => (z.1-z.2).natAbs)
  refine ⟨D+1, ?_⟩
  intro p hp a ha b hb eq
  change (a : ZMod p) = (b : ZMod p) at eq
  by_contra hne
  have bound : (a-b).natAbs ≤ D :=
    Finset.le_sup (f := fun z : ℤ × ℤ => (z.1-z.2).natAbs)
      (Finset.mem_product.mpr ⟨ha,hb⟩ : (a,b) ∈ A.product A)
  have zero : ((a-b : ℤ) : ZMod p) = 0 := by rw [Int.cast_sub, eq, sub_self]
  have dvd : (p : ℤ) ∣ a-b := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp zero
  have natdvd : p ∣ (a-b).natAbs := Int.natAbs_dvd_natAbs.mpr dvd
  have lower := Nat.le_of_dvd (Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)) natdvd
  omega

#print axioms eventually_injOn_intCast

end SidonAffine

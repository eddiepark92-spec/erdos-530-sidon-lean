import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Rat

/-! Finite integer models for additive configurations in rational vector spaces. -/

namespace SidonCompression

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- A rational linear functional can be chosen nonzero simultaneously on
any finite family of nonzero vectors. -/
private theorem separates_nonzero (D : Finset V) (hD : ∀ x ∈ D, x ≠ 0) :
    ∃ f : V →ₗ[ℚ] ℚ, ∀ x ∈ D, f x ≠ 0 := by
  classical
  induction D using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x D _ ih =>
    obtain ⟨f,hf⟩ := ih (fun a ha => hD a (Finset.mem_insert_of_mem ha))
    let b := Basis.ofVectorSpace ℚ V
    have hex : ∃ i, b.coord i x ≠ 0 := by
      by_contra! h
      exact hD x (Finset.mem_insert_self ..) (b.forall_coord_eq_zero_iff.mp h)
    obtain ⟨i,hi⟩ := hex
    let g := b.coord i
    letI : Infinite ℚ := Infinite.of_injective (fun n : ℕ => (n : ℚ)) Nat.cast_injective
    obtain ⟨t,ht⟩ := Infinite.exists_not_mem_finset
      ((insert x D).image (fun a => -f a / g a))
    refine ⟨f + t • g, ?_⟩
    intro a ha h
    change f a + t * g a = 0 at h
    by_cases hga : g a = 0
    · have hfa : f a = 0 := by simpa only [hga,mul_zero,add_zero] using h
      rcases Finset.mem_insert.mp ha with rfl | ha'
      · exact hi hga
      · exact hf a ha' hfa
    · apply ht
      apply Finset.mem_image.mpr
      refine ⟨a,ha,?_⟩
      apply (div_eq_iff hga).2
      exact (eq_neg_of_add_eq_zero_right h).symm

/-- Separating all nonzero pair differences makes the linear functional injective
on a prescribed finite set. -/
theorem rational_linear_injOn (A : Finset V) :
    ∃ f : V →ₗ[ℚ] ℚ, Set.InjOn f (A : Set V) := by
  classical
  let D := ((A ×ˢ A).image (fun z : V × V => z.1 - z.2)).erase 0
  obtain ⟨f,hf⟩ := separates_nonzero D (fun _ h => (Finset.mem_erase.mp h).1)
  refine ⟨f,?_⟩
  intro x hx y hy eq
  by_contra hxy
  apply hf (x-y)
  · exact Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hxy, Finset.mem_image.mpr
      ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,rfl⟩⟩
  · simpa only [map_sub,sub_eq_zero] using eq

omit [AddCommGroup V] [Module ℚ V] in
/-- One positive integer clears every denominator in a finite rational family. -/
private theorem clear_denominators (A : Finset V) (f : V → ℚ) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ x ∈ A, ∃ z : ℤ, (z : ℚ) = n * f x := by
  classical
  let n := ∏ x ∈ A, (f x).den
  refine ⟨n,Finset.prod_ne_zero_iff.mpr (fun x _ => (f x).den_ne_zero),?_⟩
  intro x hx
  obtain ⟨k,hk⟩ := Finset.dvd_prod_of_mem (fun y => (f y).den) hx
  refine ⟨k * (f x).num,?_⟩
  change _ = (↑(∏ y ∈ A, (f y).den) : ℚ) * f x
  rw [hk]
  push_cast
  rw [mul_right_comm, Rat.den_mul_eq_num, mul_comm]

/-- Every finite subset of a rational vector space admits a faithful integer
model for all equalities of two-term sums, including repeated summands. -/
theorem finite_integer_model (A : Finset V) :
    ∃ f : V → ℤ, Set.InjOn f (A : Set V) ∧
      ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
        (a+b=c+d ↔ f a+f b=f c+f d) := by
  classical
  let U := A ∪ (A ×ˢ A).image (fun z : V × V => z.1 + z.2)
  obtain ⟨q,hq⟩ := rational_linear_injOn U
  obtain ⟨n,hn,hz⟩ := clear_denominators A q
  let f (x : V) : ℤ := if h : x ∈ A then (hz x h).choose else 0
  have spec {x : V} (hx : x ∈ A) : (f x : ℚ) = n * q x := by
    simpa only [f,dif_pos hx] using (hz x hx).choose_spec
  have nz : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have sums {a b : V} (ha : a ∈ A) (hb : b ∈ A) : a+b ∈ U :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr ⟨ha,hb⟩,rfl⟩)
  refine ⟨f,?_,?_⟩
  · intro x hx y hy e
    apply hq (Finset.mem_union_left _ hx) (Finset.mem_union_left _ hy)
    apply mul_left_cancel₀ nz
    rw [← spec hx,← spec hy,e]
  · intro a ha b hb c hc d hd
    have castsum (x y : V) (hx : x ∈ A) (hy : y ∈ A) :
        ((f x + f y : ℤ) : ℚ) = n * q (x+y) := by
      rw [Int.cast_add,spec hx,spec hy,map_add,mul_add]
    constructor
    · intro h
      apply Int.cast_injective (α := ℚ)
      rw [castsum _ _ ha hb,castsum _ _ hc hd,h]
    · intro h
      apply hq (sums ha hb) (sums hc hd)
      apply mul_left_cancel₀ nz
      rw [← castsum _ _ ha hb,← castsum _ _ hc hd,h]

/-- The integer model specialized to the ambient group of Erdős problem 530. -/
theorem real_integer_model (A : Finset ℝ) :
    ∃ f : ℝ → ℤ, Set.InjOn f (A : Set ℝ) ∧
      ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
        (a+b=c+d ↔ f a+f b=f c+f d) := finite_integer_model A

/-- A cardinality bound for finite integer Sidon subsets transfers with exactly
the same parameters to finite real sets. -/
theorem real_sidon_bound_of_integer (P : ℕ → ℕ → Prop)
    (H : ∀ Z : Finset ℤ, ∃ B ⊆ Z, P Z.card B.card ∧
      ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, ∀ d ∈ B, a+b=c+d →
        (a=c ∧ b=d) ∨ (a=d ∧ b=c)) (A : Finset ℝ) :
    ∃ S ⊆ A, P A.card S.card ∧
      ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a+b=c+d →
        (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  classical
  obtain ⟨f,hf,hadd⟩ := real_integer_model A
  obtain ⟨B,hB,hP,hs⟩ := H (A.image f)
  let S := A.filter (fun a => f a ∈ B)
  have hSA : S ⊆ A := Finset.filter_subset ..
  have im : S.image f = B := by
    ext z
    constructor
    · rintro hz
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp ha).2
    · intro hz
      obtain ⟨a,ha,haz⟩ := Finset.mem_image.mp (hB hz)
      exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,haz ▸ hz⟩,haz⟩
  have card_eq := Finset.card_image_of_injOn (s := S) (hf.mono hSA)
  rw [im] at card_eq
  rw [Finset.card_image_of_injOn hf,card_eq] at hP
  refine ⟨S,hSA,hP,?_⟩
  intro a ha b hb c hc d hd e
  obtain ⟨ha,hfa⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb,hfb⟩ := Finset.mem_filter.mp hb
  obtain ⟨hc,hfc⟩ := Finset.mem_filter.mp hc
  obtain ⟨hd,hfd⟩ := Finset.mem_filter.mp hd
  have eq := (hadd _ ha _ hb _ hc _ hd).mp e
  rcases hs _ hfa _ hfb _ hfc _ hfd eq with ⟨g,h⟩ | ⟨g,h⟩
  · exact Or.inl ⟨hf ha hc g,hf hb hd h⟩
  · exact Or.inr ⟨hf ha hd g,hf hb hc h⟩

#print axioms real_integer_model
#print axioms real_sidon_bound_of_integer
#print axioms finite_integer_model

end SidonCompression

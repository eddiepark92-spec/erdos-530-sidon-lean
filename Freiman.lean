import Mathlib.Data.Finset.Card

/-! Exact arithmetic behind the half-bin Freiman compression. All moduli and inputs
are represented as integers; congruence of two sums is divisibility of their difference. -/

namespace SidonCompression

/-- The label of a point in the discretization of a circle into `m` bins. -/
def label (p m x : Int) : Int := (m*x)/p

/-- The retained part of a bin has fractional width strictly less than one half. -/
def retained (p m x : Int) : Prop := 2*((m*x)%p) < p

private theorem mult_small {p k : Int} (hp : 0 < p)
    (lo : -p < p*k) (hi : p*k < p) : k = 0 := by
  by_cases hk : 0 < k
  · have h := Int.mul_le_mul_of_nonneg_left (show 1 ≤ k by omega) (Int.le_of_lt hp)
    rw [Int.mul_one] at h
    omega
  · by_cases h : k < 0
    · have h' := Int.mul_le_mul_of_nonneg_left (show k ≤ -1 by omega) (Int.le_of_lt hp)
      rw [Int.mul_neg, Int.mul_one] at h'
      omega
    · omega

/-- On the retained half-bins, the label map takes equal sums modulo `p`
to equal sums modulo `m`. The affine map that precedes this lemma can include
a common additive shift. -/
theorem half_bin_freiman {p m a b c d : Int} (hp : 0 < p)
    (ha : retained p m a) (hb : retained p m b)
    (hc : retained p m c) (hd : retained p m d)
    (h : p ∣ (a+b)-(c+d)) :
    m ∣ (label p m a + label p m b) - (label p m c + label p m d) := by
  obtain ⟨t,ht⟩ := h
  have eq : m*(a+b-(c+d)) = p*(m*t) := by
    rw [ht, ← Int.mul_assoc, Int.mul_comm m p, Int.mul_assoc]
  simp only [Int.mul_sub, Int.mul_add] at eq
  let z := m*t - (((m*a)/p + (m*b)/p) - ((m*c)/p + (m*d)/p))
  have hz : p*z = (m*a)%p + (m*b)%p - ((m*c)%p+(m*d)%p) := by
    dsimp only [z]
    simp only [Int.mul_add, Int.mul_sub]
    have E (x : Int) := Int.emod_add_ediv (m*x) p
    have e1 := E a
    have e2 := E b
    have e3 := E c
    have e4 := E d
    omega
  have nn (x : Int) := Int.emod_nonneg (m*x) (Int.ne_of_gt hp)
  have n1 := nn a
  have n2 := nn b
  have n3 := nn c
  have n4 := nn d
  unfold retained at ha hb hc hd
  have zero := mult_small hp (k := z) (by omega) (by omega)
  exact ⟨t, by unfold label; dsimp [z] at zero; omega⟩

/-- Sidon property on a family represented by its map of element indices.
The relation `sameSum` accepts four source indices in two ordered pairs. -/
def SidonFor {ι : Type*} (sameSum : ι → ι → ι → ι → Prop) : Prop :=
  ∀ a b c d, sameSum a b c d → (a=c ∧ b=d) ∨ (a=d ∧ b=c)

/-- An injective Freiman map into a Sidon family certifies the source family. -/
theorem sidon_pullback {ι κ : Type*} {source : ι → ι → ι → ι → Prop}
    {target : κ → κ → κ → κ → Prop} {f : ι → κ} (hinj : Function.Injective f)
    (hmap : ∀ a b c d, source a b c d → target (f a) (f b) (f c) (f d))
    (hs : SidonFor target) : SidonFor source := by
  intro a b c d h
  rcases hs _ _ _ _ (hmap _ _ _ _ h) with ⟨e1,e2⟩|⟨e1,e2⟩
  · exact Or.inl ⟨hinj e1,hinj e2⟩
  · exact Or.inr ⟨hinj e1,hinj e2⟩

/-- In a half-length interval, congruent pair sums lift to equal integers. -/
theorem half_interval_lift {p a b c d : Int} (hp : 0 < p)
    (ha : 0 ≤ a ∧ 2*a < p) (hb : 0 ≤ b ∧ 2*b < p)
    (hc : 0 ≤ c ∧ 2*c < p) (hd : 0 ≤ d ∧ 2*d < p)
    (h : p ∣ (a+b)-(c+d)) : a+b=c+d := by
  obtain ⟨t,ht⟩ := h
  have hz := mult_small hp (k := t) (by omega) (by omega)
  simp [hz] at ht
  omega

/-- Residue of a randomly chosen affine map on integer points. -/
def point (p u v a : Int) : Int := (u*a+v)%p

/-- Equal integer source sums give congruent sums of reduced affine coordinates. -/
theorem affine_sum_dvd {a b c d : Int} (p u v : Int) (h : a+b=c+d) :
    p ∣ (point p u v a + point p u v b) - (point p u v c + point p u v d) := by
  have hh := congrArg (fun x : Int => u*x) h
  simp only [Int.mul_add] at hh
  unfold point
  refine ⟨(u*c+v)/p + (u*d+v)/p - ((u*a+v)/p + (u*b+v)/p), ?_⟩
  simp only [Int.mul_add, Int.mul_sub]
  have E (x : Int) := Int.emod_add_ediv (u*x+v) p
  have e1 := E a
  have e2 := E b
  have e3 := E c
  have e4 := E d
  omega

/-- Reducing four equal-sum integer representatives modulo a second modulus gives
a valid cyclic additive quadruple. -/
theorem residues_of_equal_sums {a b c d : Int} (m : Int) (h : a+b=c+d) :
    m ∣ (a%m+b%m)-(c%m+d%m) := by
  simpa only [point, Int.one_mul, Int.add_zero] using affine_sum_dvd m 1 0 h

/-- Equal source sums become equal cyclic sums of the labels of retained points.
The concrete experiment retains `point p u v a < m*L` where `2*m*L ≤ p`. -/
theorem contiguous_freiman {p u v m a b c d : Int} (hp : 0<p)
    (ha : 2*point p u v a < p) (hb : 2*point p u v b < p)
    (hc : 2*point p u v c < p) (hd : 2*point p u v d < p)
    (h : a+b=c+d) :
    m ∣ (point p u v a % m + point p u v b % m) -
        (point p u v c % m + point p u v d % m) := by
  have nn (x : Int) : 0 ≤ point p u v x := Int.emod_nonneg _ (Int.ne_of_gt hp)
  apply residues_of_equal_sums
  exact half_interval_lift hp ⟨nn a,ha⟩ ⟨nn b,hb⟩ ⟨nn c,hc⟩ ⟨nn d,hd⟩
    (affine_sum_dvd _ _ _ h)

/-- Pair-sum uniqueness on an explicitly specified finite set. -/
def SidonOn {α : Type*} (A : Finset α) (E : α → α → α → α → Prop) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, E a b c d →
    (a=c ∧ b=d) ∨ (a=d ∧ b=c)

/-- Select one source representative for each occupied bin in a Sidon target.
The source Sidon subset has exactly the number of such bins. -/
theorem select_sidon_representatives {α β : Type*} {A : Finset α} {B : Finset β}
    (f : α → β) {E : α → α → α → α → Prop} {F : β → β → β → β → Prop}
    (hocc : ∀ z ∈ B, ∃ a ∈ A, f a=z)
    (hmap : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, E a b c d → F (f a) (f b) (f c) (f d))
    (hs : SidonOn B F) : ∃ S ⊆ A, S.card=B.card ∧ SidonOn S E := by
  classical
  let pick (z : B) : α := Classical.choose (hocc z.val z.property)
  have hp (z : B) : pick z ∈ A ∧ f (pick z)=z.val :=
    Classical.choose_spec (hocc z.val z.property)
  have hi : Function.Injective pick := by
    intro x y h
    apply Subtype.ext
    exact (hp x).2.symm.trans ((congrArg f h).trans (hp y).2)
  let S := B.attach.image pick
  have sep : ∀ a ∈ S, ∃ z : B, pick z=a := by
    intro a ha
    obtain ⟨z,_,hz⟩ := Finset.mem_image.mp ha
    exact ⟨z,hz⟩
  have subset : S ⊆ A := by
    intro a ha
    obtain ⟨z,rfl⟩ := sep _ ha
    exact (hp z).1
  refine ⟨S,subset,?_,?_⟩
  · exact (B.attach.card_image_of_injective hi).trans Finset.card_attach
  · intro a ha b hb c hc d hd h
    obtain ⟨i,rfl⟩ := sep _ ha
    obtain ⟨j,rfl⟩ := sep _ hb
    obtain ⟨k,rfl⟩ := sep _ hc
    obtain ⟨l,rfl⟩ := sep _ hd
    have eq := hmap _ (hp i).1 _ (hp j).1 _ (hp k).1 _ (hp l).1 h
    rw [(hp i).2,(hp j).2,(hp k).2,(hp l).2] at eq
    rcases hs _ i.property _ j.property _ k.property _ l.property eq with ⟨e1,e2⟩|⟨e1,e2⟩
    · exact Or.inl ⟨congrArg pick (Subtype.ext e1),congrArg pick (Subtype.ext e2)⟩
    · exact Or.inr ⟨congrArg pick (Subtype.ext e1),congrArg pick (Subtype.ext e2)⟩

/-- An occupied cyclic Sidon template in the retained half interval lifts to a
source Sidon set with the same cardinality. -/
theorem extract_half_sidon {A B : Finset Int} {p u v m : Int} (hp : 0<p)
    (hocc : ∀ z ∈ B, ∃ a ∈ A, 2*point p u v a < p ∧ point p u v a % m = z)
    (hs : SidonOn B (fun a b c d => m ∣ (a+b)-(c+d))) :
    ∃ S ⊆ A, S.card=B.card ∧ SidonOn S (fun a b c d => a+b=c+d) := by
  let R := A.filter (fun a => 2*point p u v a < p)
  have occ : ∀ z ∈ B, ∃ a ∈ R, point p u v a % m = z := by
    intro z hz
    obtain ⟨a,ha,hr,he⟩ := hocc _ hz
    exact ⟨a,Finset.mem_filter.mpr ⟨ha,hr⟩,he⟩
  have small {a : Int} (h : a ∈ R) : 2*point p u v a < p :=
    (Finset.mem_filter.mp h).2
  obtain ⟨S,hS,hcard,hSidon⟩ := select_sidon_representatives
    (fun a => point p u v a % m) occ
    (fun _ ha _ hb _ hc _ hd h => contiguous_freiman hp (small ha) (small hb)
      (small hc) (small hd) h) hs
  exact ⟨S,hS.trans (Finset.filter_subset _ _),hcard,hSidon⟩

#print axioms extract_half_sidon
#print axioms contiguous_freiman
#print axioms select_sidon_representatives
#print axioms half_bin_freiman
#print axioms sidon_pullback
end SidonCompression

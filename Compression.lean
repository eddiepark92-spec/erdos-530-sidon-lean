import Affine
import Freiman
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic

/-! Finite occupancy estimates for a family of pairwise-uniform hashes. -/

namespace SidonCompression

open Finset
open scoped BigOperators

/-- A lower bound for a union of finite events in terms of their individual
cardinalities and a uniform upper bound on pairwise intersections. -/
theorem event_union {α Ω : Type*} [DecidableEq Ω]
    (points : Finset α) (events : α → Finset Ω) (p q : ℕ)
    (single : ∀ a ∈ points, p ≤ (events a).card)
    (pair : ∀ a ∈ points, ∀ b ∈ points, a ≠ b → (events a ∩ events b).card ≤ q) :
    points.card * p ≤ (points.biUnion events).card + points.card.choose 2 * q := by
  classical
  induction points using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have prev := ih (fun b hb => single b (mem_insert_of_mem hb))
      (fun b hb c hc hbc => pair b (mem_insert_of_mem hb) c (mem_insert_of_mem hc) hbc)
    have ha' := single a (mem_insert_self a s)
    have overlap : (events a ∩ s.biUnion events).card ≤ s.card * q := by
      rw [Finset.inter_biUnion]
      apply Finset.card_biUnion_le_card_mul
      intro b hb
      exact pair a (mem_insert_self a s) b (mem_insert_of_mem hb)
        (fun eq => ha (eq ▸ hb))
    have inc := Finset.card_union_add_card_inter (events a) (s.biUnion events)
    rw [Finset.card_insert_of_not_mem ha, Finset.biUnion_insert,
      Nat.choose_succ_succ' s.card 1, Nat.choose_one_right, Nat.add_mul, Nat.add_mul]
    simp only [Nat.reduceAdd, Nat.one_mul] at *
    omega

/-- Number of distinct bins hit by at least one point at a given sample. -/
def occupied {α β Ω : Type*} [DecidableEq Ω]
    (points : Finset α) (bins : Finset β)
    (events : β → α → Finset Ω) (w : Ω) : ℕ :=
  (bins.filter (fun b => w ∈ points.biUnion (events b))).card

/-- A hash attaining the averaged lower bound. The sample space is finite
and uniform. The hypotheses concern the exact sample counts for individual
points and for two distinct points in the same bin. -/
theorem exists_occupied {α β Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (points : Finset α) (bins : Finset β) (events : β → α → Finset Ω) (p q : ℕ)
    (single : ∀ b ∈ bins, ∀ a ∈ points, p ≤ (events b a).card)
    (pair : ∀ b ∈ bins, ∀ a ∈ points, ∀ c ∈ points,
      a ≠ c → (events b a ∩ events b c).card ≤ q) :
    ∃ w : Ω, bins.card * (points.card * p) ≤
      Fintype.card Ω * occupied points bins events w + bins.card * (points.card.choose 2 * q) := by
  classical
  have sum_bound := Finset.sum_le_sum (s := bins)
    (fun b hb => event_union points (events b) p q (single b hb) (pair b hb))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.nsmul_eq_mul] at sum_bound
  have doubleCount :
      (∑ b ∈ bins, (points.biUnion (events b)).card) =
        ∑ w : Ω, occupied points bins events w := by
    unfold occupied
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← Finset.card_filter, Finset.filter_univ_mem]
  obtain ⟨w, _, hw⟩ := Finset.exists_max_image (Finset.univ : Finset Ω)
    (occupied points bins events) Finset.univ_nonempty
  have total := Finset.sum_le_sum (s := (Finset.univ : Finset Ω))
    (fun v hv => hw v hv)
  simp only [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_univ] at total
  rw [doubleCount] at sum_bound
  exact ⟨w, sum_bound.trans (Nat.add_le_add_right total _)⟩

/-- The selected affine hashes with a prescribed image window for an input. -/
def affineEvents {K α β : Type*} [Field K] [Fintype K] [DecidableEq K]
    (embed : α → K) (windows : β → Finset K) (b : β) (a : α) : Finset (K × K) :=
  univ.filter (fun w => SidonAffine.eval w (embed a) ∈ windows b)

/-- Some affine hash reaches the stated number of prescribed, equal-sized
windows. An injection on the finite input set suffices. The windows may even
overlap. -/
theorem exists_affine_occupied {K α β : Type*} [Field K] [Fintype K] [DecidableEq K]
    (points : Finset α) (embed : α → K) (hinj : Set.InjOn embed ↑points)
    (bins : Finset β) (windows : β → Finset K) (L : ℕ)
    (hsize : ∀ b ∈ bins, (windows b).card = L) :
    ∃ w : K × K, bins.card * (points.card * (Fintype.card K * L)) ≤
      (Fintype.card K * Fintype.card K) * occupied points bins (affineEvents embed windows) w +
        bins.card * (points.card.choose 2 * (L * L)) := by
  classical
  let E := affineEvents embed windows
  have hs : ∀ b ∈ bins, ∀ a ∈ points, Fintype.card K * L ≤ (E b a).card := by
    intro b hb a _
    dsimp [E, affineEvents]
    rw [SidonAffine.card_single, hsize b hb]
  have hp : ∀ b ∈ bins, ∀ a ∈ points, ∀ c ∈ points, a ≠ c →
      (E b a ∩ E b c).card ≤ L * L := by
    intro b hb a ha c hc hac
    have he : E b a ∩ E b c = univ.filter (fun w =>
        SidonAffine.eval w (embed a) ∈ windows b ∧ SidonAffine.eval w (embed c) ∈ windows b) := by
      ext w
      simp [E, affineEvents]
    rw [he, SidonAffine.card_pair _ _ (fun h => hac (hinj ha hc h)), hsize b hb]
  simpa only [Fintype.card_prod] using
    exists_occupied points bins E (Fintype.card K * L) (L * L) hs hp

/-- Finite Sidon subset bound using a cyclic template and an affine half-interval hash.
The prime can be any prime for which the given integer inputs remain distinct. -/
theorem finite_sidon_bound (A : Finset ℤ) {p m L : ℕ} [Fact p.Prime] [NeZero m]
    (B : Finset (ZMod m)) (hi : Set.InjOn (fun a : ℤ => (a : ZMod p)) ↑A)
    (hL : 2 * (m * L) ≤ p) (hB : SidonOn B (fun a b c d => a+b=c+d)) :
    ∃ S ⊆ A, SidonOn S (fun a b c d => a+b=c+d) ∧
      B.card * (A.card * (p * L)) ≤ (p * p) * S.card + B.card * (A.card.choose 2 * (L * L)) := by
  classical
  let embed : ℤ → ZMod p := fun a => a
  let idx (b : ZMod m) : Fin m := ⟨b.val, b.val_lt⟩
  let windows (b : ZMod m) := SidonAffine.labelBin p m L (idx b)
  have hfull : m * L ≤ p := by omega
  have hsize (b : ZMod m) (_ : b ∈ B) : (windows b).card = L :=
    SidonAffine.card_labelBin hfull _
  obtain ⟨s, hcount⟩ := exists_affine_occupied A embed hi B windows L hsize
  rw [ZMod.card] at hcount
  let E := affineEvents embed windows
  let hits := B.filter (fun b => s ∈ A.biUnion (E b))
  let R := A.filter (fun a => (SidonAffine.eval s (embed a)).val < m * L)
  let f (a : ℤ) := SidonAffine.gridLabel m (SidonAffine.eval s (embed a))
  have hocc : ∀ b ∈ hits, ∃ a ∈ R, f a = b := by
    intro b hb
    obtain ⟨a, ha, hit⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hb).2
    have hw : SidonAffine.eval s (embed a) ∈ windows b := (Finset.mem_filter.mp hit).2
    have hz := SidonAffine.mem_labelBin hfull (idx b) (SidonAffine.eval s (embed a)) |>.mp hw
    refine ⟨a, Finset.mem_filter.mpr ⟨ha, hz.1⟩, ?_⟩
    exact (SidonAffine.gridLabel_of_mem_labelBin hfull _ _ hw).trans (ZMod.natCast_zmod_val b)
  have hr {a : ℤ} (ha : a ∈ R) : (SidonAffine.eval s (embed a)).val < m * L :=
    (Finset.mem_filter.mp ha).2
  have hmap : ∀ a ∈ R, ∀ b ∈ R, ∀ c ∈ R, ∀ d ∈ R, a+b=c+d → f a + f b = f c + f d := by
    intro a ha b hb c hc d hd he
    apply SidonAffine.gridLabel_eval_sum hL s _ _ _ _ (hr ha) (hr hb) (hr hc) (hr hd)
    simpa only [embed, Int.cast_add] using congrArg (fun z : ℤ => (z : ZMod p)) he
  have inc : hits ⊆ B := Finset.filter_subset _ _
  have hsid : SidonOn hits (fun a b c d => a+b=c+d) :=
    fun a ha b hb c hc d hd => hB a (inc ha) b (inc hb) c (inc hc) d (inc hd)
  obtain ⟨S, hsub, hcard, hs⟩ := select_sidon_representatives f hocc hmap hsid
  refine ⟨S, hsub.trans (Finset.filter_subset _ _), hs, ?_⟩
  change B.card * (A.card * (p * L)) ≤ (p * p) * hits.card +
    B.card * (A.card.choose 2 * (L * L)) at hcount
  rwa [hcard]

#print axioms finite_sidon_bound
#print axioms exists_affine_occupied
#print axioms exists_occupied

end SidonCompression

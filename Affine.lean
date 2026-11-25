import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! Exact finite-field sampling facts for the randomly shifted affine projection. -/
namespace SidonAffine

variable {K : Type*} [Field K]

/-- The first parameter is the slope and the second is the common shift. -/
def eval (s : K × K) (a : K) : K := s.1 * a + s.2

/-- Evaluations at two distinct inputs determine the slope and shift uniquely,
including when the slope is zero. -/
def pairEquiv (a b : K) (hab : a ≠ b) : (K × K) ≃ (K × K) where
  toFun s := (eval s a, eval s b)
  invFun z := let u := (z.1 - z.2) / (a - b); (u, z.1 - u * a)
  left_inv := by
    rintro ⟨u, v⟩
    dsimp [eval]
    have hs : (u * a + v - (u * b + v)) / (a - b) = u :=
      (div_eq_iff (sub_ne_zero.mpr hab)).2 (by ring)
    rw [hs]
    simp
  right_inv := by
    rintro ⟨x, y⟩
    dsimp [eval]
    apply Prod.ext
    · dsimp
      ring
    · dsimp
      calc
        _ = x - (x - y) / (a - b) * (a - b) := by ring
        _ = y := by rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab)]; ring

/-- Keeping the slope and recording a single affine evaluation is a bijection. -/
def singleEquiv (a : K) : (K × K) ≃ (K × K) where
  toFun s := (s.1, eval s a)
  invFun z := (z.1, z.2 - z.1 * a)
  left_inv := by rintro ⟨u,v⟩; simp [eval]
  right_inv := by rintro ⟨u,x⟩; simp [eval]

theorem card_preimage_equiv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (S : Finset β) :
    (Finset.univ.filter (fun s => e s ∈ S)).card = S.card := by
  classical
  calc
    _ = ((Finset.univ.filter (fun s => e s ∈ S)).map e.toEmbedding).card :=
      (Finset.card_map _).symm
    _ = (((Finset.univ : Finset α).map e.toEmbedding).filter (· ∈ S)).card := by
      rw [Finset.filter_map]
      rfl
    _ = S.card := by rw [Finset.map_univ_equiv, Finset.filter_univ_mem]

variable [Fintype K] [DecidableEq K]

/-- The two affine evaluations fall in given windows in exactly |S| |T| cases. -/
theorem card_pair (a b : K) (hab : a ≠ b) (S T : Finset K) :
    (Finset.univ.filter (fun s => eval s a ∈ S ∧ eval s b ∈ T)).card = S.card * T.card := by
  simpa [pairEquiv, Finset.card_product] using
    card_preimage_equiv (pairEquiv a b hab) (S.product T)

/-- Each allowed residue is reached once for every slope. -/
theorem card_single (a : K) (S : Finset K) :
    (Finset.univ.filter (fun s => eval s a ∈ S)).card = Fintype.card K * S.card := by
  simpa [singleEquiv, Finset.card_product] using
    card_preimage_equiv (singleEquiv a) ((Finset.univ : Finset K).product S)

/-- Exact same-bin count over all slope and shift pairs for disjoint equal bins.
The event is written as a union of rectangles for a computable membership test. -/
theorem card_same_bin (a b : K) (hab : a ≠ b) {m w : ℕ} (bins : Fin m → Finset K)
    (disj : ∀ i j, i ≠ j → Disjoint (bins i) (bins j)) (hw : ∀ i, (bins i).card = w) :
    (Finset.univ.filter (fun s => (eval s a, eval s b) ∈
      Finset.univ.biUnion (fun i => (bins i).product (bins i)))).card = m * (w * w) := by
  classical
  change (Finset.univ.filter (fun s => pairEquiv a b hab s ∈ _)).card = _
  rw [card_preimage_equiv, Finset.card_biUnion]
  · simp [Finset.card_product, hw]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro z hi hj
    exact Finset.disjoint_left.mp (disj i j hij) (Finset.mem_product.mp hi).1
      (Finset.mem_product.mp hj).1

/-- The representatives of label `i` among the first `m*w` residues modulo `p`. -/
def labelBin (p m w : ℕ) (i : Fin m) : Finset (ZMod p) :=
  Finset.univ.image fun j : Fin w => ((i.val + m * j.val : ℕ) : ZMod p)

private theorem slot_lt {m w : ℕ} (i : Fin m) (j : Fin w) : i.val + m * j.val < m * w := by
  calc
    _ < m + m * j.val := Nat.add_lt_add_right i.isLt _
    _ = m * (j.val + 1) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ j.isLt

theorem card_labelBin {p m w : ℕ} (hp : m * w ≤ p) (i : Fin m) :
    (labelBin p m w i).card = w := by
  unfold labelBin
  have hi : Function.Injective (fun j : Fin w => ((i.val + m * j.val : ℕ) : ZMod p)) := by
    intro j k hjk
    have eq := congrArg ZMod.val hjk
    change ((i.val + m * j.val : ℕ) : ZMod p).val = ((i.val + m * k.val : ℕ) : ZMod p).val at eq
    rw [ZMod.val_natCast_of_lt ((slot_lt i j).trans_le hp),
        ZMod.val_natCast_of_lt ((slot_lt i k).trans_le hp)] at eq
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt i.isLt) (Nat.add_left_cancel eq))
  rw [Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]

/-- Bin membership agrees with the concrete retention and labelling rules. -/
theorem mem_labelBin {p m w : ℕ} [NeZero p] (hp : m * w ≤ p) (i : Fin m) (z : ZMod p) :
    z ∈ labelBin p m w i ↔ z.val < m * w ∧ z.val % m = i.val := by
  constructor
  · intro hz
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
    rw [ZMod.val_natCast_of_lt ((slot_lt i j).trans_le hp)]
    exact ⟨slot_lt i j, by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]⟩
  · rintro ⟨hz, hi⟩
    let j : Fin w := ⟨z.val / m, (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt i.isLt)).2
      (by simpa [Nat.mul_comm] using hz)⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    dsimp [j]
    rw [← hi, Nat.mod_add_div, ZMod.natCast_zmod_val]

theorem disjoint_labelBin {p m w : ℕ} [NeZero p] (hp : m * w ≤ p) (i j : Fin m) (hne : i ≠ j) :
    Disjoint (labelBin p m w i) (labelBin p m w j) := by
  apply Finset.disjoint_left.mpr
  intro z hi hj
  exact hne (Fin.ext (((mem_labelBin hp i z).mp hi).2.symm.trans (((mem_labelBin hp j z).mp hj).2)))

/-- The output of the half-interval hash, as a cyclic group element. -/
def gridLabel {p : ℕ} (m : ℕ) (z : ZMod p) : ZMod m := z.val

theorem gridLabel_of_mem_labelBin {p m w : ℕ} [NeZero p] (hp : m * w ≤ p)
    (i : Fin m) (z : ZMod p) (hz : z ∈ labelBin p m w i) :
    gridLabel m z = (i.val : ZMod m) := by
  have hi := ((mem_labelBin hp i z).mp hz).2
  unfold gridLabel
  rw [← hi, ZMod.natCast_mod]

/-- Preservation of pair-sum equalities when all four affine projections lie
in the retained half interval. -/
theorem gridLabel_eval_sum {p m w : ℕ} [Fact p.Prime] (hp : 2 * (m * w) ≤ p)
    (s : ZMod p × ZMod p) (a b c d : ZMod p)
    (ha : (eval s a).val < m * w) (hb : (eval s b).val < m * w)
    (hc : (eval s c).val < m * w) (hd : (eval s d).val < m * w) (h : a+b = c+d) :
    gridLabel m (eval s a) + gridLabel m (eval s b) =
      gridLabel m (eval s c) + gridLabel m (eval s d) := by
  have e : eval s a + eval s b = eval s c + eval s d := by
    unfold eval
    calc
      _ = s.1 * (a+b) + (s.2+s.2) := by ring
      _ = s.1 * (c+d) + (s.2+s.2) := by rw [h]
      _ = _ := by ring
  have v := congrArg ZMod.val e
  rw [ZMod.val_add_of_lt (by omega : (eval s a).val + (eval s b).val < p),
      ZMod.val_add_of_lt (by omega : (eval s c).val + (eval s d).val < p)] at v
  simpa [gridLabel] using congrArg (fun n : ℕ => (n : ZMod m)) v

#print axioms gridLabel_eval_sum
#print axioms card_pair
#print axioms card_single
#print axioms card_same_bin
#print axioms card_labelBin
#print axioms mem_labelBin
#print axioms disjoint_labelBin

end SidonAffine

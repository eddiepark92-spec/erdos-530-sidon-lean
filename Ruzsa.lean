import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.Ring

/-! Ruzsa's classical cyclic Sidon sets, obtained from the graph of exponentiation. -/
namespace SidonCompression

private theorem pair_rigidity {K : Type*} [Field K] {a b c d : K}
    (hs : a+b=c+d) (hp : a*b=c*d) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have h : (a-c)*(a-d)=0 := calc
    (a-c)*(a-d) = a*a-a*(c+d)+c*d := by ring
    _ = 0 := by rw [← hs,← hp]; ring
  rcases mul_eq_zero.mp h with h|h
  · have h' := sub_eq_zero.mp h
    subst c
    exact Or.inl ⟨rfl,add_left_cancel hs⟩
  · have h' := sub_eq_zero.mp h
    subst d
    exact Or.inr ⟨rfl,add_left_cancel (hs.trans (add_comm _ _))⟩

private noncomputable def ruzsaExp (p : ℕ) [Fact p.Prime] :
    Multiplicative (ZMod (p-1)) ≃* (ZMod p)ˣ := by
  have hc : Nat.card (ZMod p)ˣ = p-1 := by rw [Nat.card_eq_fintype_card,ZMod.card_units]
  rw [← hc]
  exact zmodCyclicMulEquiv inferInstance

/-- p-1 distinct labels modulo p(p-1) with all unordered pair sums distinct.
The order of the factors here is convenient for the Chinese remainder map. -/
theorem ruzsa_target (p : ℕ) [hp : Fact p.Prime] :
    ∃ B : Finset (ZMod ((p-1)*p)), B.card = p-1 ∧
      ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, ∀ d ∈ B,
        a+b=c+d → (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  classical
  have h1 := hp.out.two_le
  letI : NeZero (p-1) := ⟨by omega⟩
  have co : Nat.Coprime (p-1) p :=
    (Nat.coprime_self_sub_left (show 1≤p by omega)).2 (Nat.coprime_one_left p)
  let crt := ZMod.chineseRemainder co
  let χ := ruzsaExp p
  let f (i : ZMod (p-1)) : ZMod p := (χ (Multiplicative.ofAdd i) : ZMod p)
  have fh (i j) : f (i+j)=f i*f j := by
    simp [f, ofAdd_add]
  have fi : Function.Injective f := by
    intro i j h
    exact χ.injective (Units.ext h)
  let g (i : ZMod (p-1)) : ZMod ((p-1)*p) := crt.symm (i,f i)
  have gi : Function.Injective g := by
    intro i j eq
    exact congrArg Prod.fst (crt.symm.injective eq)
  refine ⟨Finset.univ.image g, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ gi,Finset.card_univ,ZMod.card]
  · rintro a ha b hb c hc d hd h
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hd
    have e := congrArg crt h
    simp only [map_add, g, RingEquiv.apply_symm_apply] at e
    have e1 : i+j=k+l := congrArg Prod.fst e
    have e2 : f i+f j=f k+f l := congrArg Prod.snd e
    have he := congrArg f e1
    rw [fh,fh] at he
    rcases pair_rigidity e2 he with ⟨e3,e4⟩|⟨e3,e4⟩
    · exact Or.inl ⟨congrArg g (fi e3),congrArg g (fi e4)⟩
    · exact Or.inr ⟨congrArg g (fi e3),congrArg g (fi e4)⟩

#print axioms ruzsa_target
end SidonCompression

[paper/Sidon-subsets.pdf](paper/Sidon-subsets.pdf) — AI assistance disclosed in the paper
# Sidon subsets of finite real sets

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24528338.svg)](https://doi.org/10.5281/zenodo.24528338)

Dohyun Park, Department of Mechanical Engineering, Seoul National University.

For every ε > 0 there is an n₀ such that for all n ≥ n₀, every n-element set A of real numbers contains a Sidon subset S with |S| ≥ (2/(3√3) − ε)√n. A Sidon set has distinct sums for distinct unordered pairs, allowing either pair to contain an element twice. The conjecture that the optimal asymptotic coefficient is 1 remains open. [Erdős problem 530](https://www.erdosproblems.com/530)

## Reproduce the build

Install Git and [elan](https://github.com/leanprover/elan). In the repository root, with internet access for the pinned dependencies, run these commands (Linux or WSL with GNU coreutils).

```sh
sha256sum -c SHA256SUMS
elan toolchain install "$(cat lean-toolchain)"
lake env lean --version
lake exe cache get
lake build
lake env lean -DwarningAsError=true Optimal.lean
```

On macOS, use `shasum -a 256 -c SHA256SUMS` for the first command. The cache step downloads precompiled Mathlib modules. Lake can build them from source if that service is unavailable. Keep the supplied manifest. Lean is pinned to **4.19.0**, [Mathlib to c44e0c8ee63c](https://github.com/leanprover-community/mathlib4/tree/c44e0c8ee63ca166450922a373c7409c5d26b00b), and [Prime Number Theorem and More to 426b540a86d5](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/426b540a86d5b4a103cec5528e68168ea172da66).

## Main declaration and axiom report

The following is the declaration in `Optimal.lean`, in the namespace `SidonCompression`.

```lean
theorem real_sidon_asymptotic (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ, A.card=n →
      ∃ S ⊆ A, SidonOn S (fun a b c d => a+b=c+d) ∧
        (2/(3*Real.sqrt 3)-ε)*Real.sqrt n ≤ S.card := by
  obtain ⟨q, hp, hq⟩ := prime_sequence_of_intervals
    (fun h => prime_between h) (c := Real.sqrt 3/2) (by positivity)
  exact asymptotic_bound_of_prime_scale q hp hq ε hε
```

The final command runs the two `#print axioms` directives. Expected output, also in [fresh-axioms.txt](fresh-axioms.txt):

```text
'prime_between' depends on axioms: [propext, Classical.choice, Quot.sound]
'SidonCompression.real_sidon_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The independent clean build on November 25, 2026 reproduced these lists. It reported seven placeholder warnings in unrelated upstream declarations. Neither queried theorem depends on `sorryAx`. The 15 local proof modules and the three toolchain/build files in this release are byte-identical to those rebuilt. The SHA-256 digest of that earlier source archive was `cfdd6df28ea2d620a65a6445db477c4d61841c06617ec5aa3cd64cb9fbdf0d07`. The release manifest covers every distributed file except itself.

## Reading the proof

| Mathematical step | Source |
| --- | --- |
| Pairwise-uniform affine sampling and occupancy | [Affine](Affine.lean), [Compression](Compression.lean) |
| Pullback and cyclic Sidon construction | [Freiman](Freiman.lean), [Ruzsa](Ruzsa.lean) |
| Finite inequality and passage to real inputs | [IntegerBound](IntegerBound.lean), [RealModel](RealModel.lean), [RealBound](RealBound.lean) |
| Uniform finite bound and prime-indexed refinement | [StrongBertrand](StrongBertrand.lean), [Peak](Peak.lean) |
| Choice of the prime for all large sizes | [PNTDensity](PNTDensity.lean), [AsymptoticBound](AsymptoticBound.lean), [Optimal](Optimal.lean) |

The proof and formalization were produced with assistance from ChatGPT and Claude. The original repository files are distributed under the [MIT License](LICENSE). Lake fetches upstream projects separately under their respective licenses.

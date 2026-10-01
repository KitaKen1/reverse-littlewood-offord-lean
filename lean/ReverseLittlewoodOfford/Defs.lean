import Mathlib

/-!
# Definitions

Signed sums of planar unit vectors and the minimum probability $F_{2,r}(n)$ of
Hollom, Portier and Souza. Planar vectors are complex numbers, and a sign vector is
`ε : Fin n → Bool`, where `true` stands for $+1$.
-/

set_option autoImplicit false

namespace ReverseLittlewoodOfford

/-- The signed sum $\varepsilon_1 v_1 + \dots + \varepsilon_n v_n$. -/
noncomputable def signedSum {n : ℕ} (v : Fin n → ℂ) (ε : Fin n → Bool) : ℂ :=
  ∑ i, (if ε i then v i else -v i)

/-- The number of sign vectors whose signed sum lies in the closed disc of radius `r`. -/
noncomputable def goodCount {n : ℕ} (v : Fin n → ℂ) (r : ℝ) : ℕ :=
  (Finset.univ.filter fun ε : Fin n → Bool => ‖signedSum v ε‖ ≤ r).card

/-- The probability that the random signed sum lies in the closed disc of radius `r`. -/
noncomputable def signedSumProb {n : ℕ} (v : Fin n → ℂ) (r : ℝ) : ℝ :=
  (goodCount v r : ℝ) / 2 ^ n

/-- $F_{2,r}(n)$: the infimum of `signedSumProb v r` over `n` unit vectors. -/
noncomputable def minProb (r : ℝ) (n : ℕ) : ℝ :=
  ⨅ v : {v : Fin n → ℂ // ∀ i, ‖v i‖ = 1}, signedSumProb v.1 r

/-- $F_{2,1}(n)^{1/n}$ along odd $n = 2k + 1$. -/
noncomputable def rootSeq (k : ℕ) : ℝ :=
  minProb 1 (2 * k + 1) ^ (1 / (2 * k + 1 : ℝ))

theorem signedSumProb_nonneg {n : ℕ} (v : Fin n → ℂ) (r : ℝ) : 0 ≤ signedSumProb v r := by
  unfold signedSumProb
  positivity

/-- The family of unit vectors is nonempty, so `minProb` is an honest infimum. -/
instance unitFamily_nonempty (n : ℕ) : Nonempty {v : Fin n → ℂ // ∀ i, ‖v i‖ = 1} :=
  ⟨⟨fun _ => 1, by simp⟩⟩

theorem minProb_le {n : ℕ} (r : ℝ) (v : Fin n → ℂ) (hv : ∀ i, ‖v i‖ = 1) :
    minProb r n ≤ signedSumProb v r := by
  have hbdd : BddBelow (Set.range fun w : {v : Fin n → ℂ // ∀ i, ‖v i‖ = 1} =>
      signedSumProb w.1 r) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact signedSumProb_nonneg _ _
  exact ciInf_le hbdd ⟨v, hv⟩

end ReverseLittlewoodOfford

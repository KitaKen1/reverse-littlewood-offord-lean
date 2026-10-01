import ReverseLittlewoodOfford.Normalization
import ReverseLittlewoodOfford.HereditaryDeletion
import ReverseLittlewoodOfford.Concentration

/-!
# The finite lower bound (A)

Fix `0 < ρ < 1/2` and put `g = 1 - 2ρ`. Bring the family to normal form (Lemma 2), pair the
indices around a pivot (Lemmas 3 and 4) and count the good flip sets (Lemmas 5, 7 and 8). This
gives `P(‖σ_V‖ ≤ 1) ≥ 2^{-(n+1)} (1 - ρ)^{-((n-3)/2 - K)}` with `K = ⌊1152 / g²⌋`.
-/

set_option autoImplicit false

namespace ReverseLittlewoodOfford

/-- **Main lower bound (A).** -/
theorem lower_bound_A {n : ℕ} (hn : Odd n) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (v : Fin n → ℂ) (hv : ∀ i, ‖v i‖ = 1) :
    (1 / 2 : ℝ) ^ (n + 1) * (1 - ρ)⁻¹ ^ ((n - 3) / 2 - ⌊(1152 : ℝ) / (1 - 2 * ρ) ^ 2⌋₊)
      ≤ signedSumProb v 1 := by
  obtain ⟨θ, hθ, hrange, hreal, hcount⟩ := exists_normal_form hn v hv
  obtain ⟨m, b, d, hm, hb0, hb1, hre, hsum, hdisc, hinj⟩ :=
    exists_pair_data hn θ hθ hrange hreal
  have key := many_good_flips hb0 hb1 hρ0 hρ1 d hre hsum hdisc
  set K := ⌊(1152 : ℝ) / (1 - 2 * ρ) ^ 2⌋₊
  have hr1 : (1 : ℝ) ≤ (1 - ρ)⁻¹ := by
    rw [one_le_inv₀ (by linarith)]
    linarith
  have hpow : (1 - ρ)⁻¹ ^ ((n - 3) / 2 - K) ≤ (1 - ρ)⁻¹ ^ (m - K) :=
    pow_le_pow_right₀ hr1 (by omega)
  have hgood : ((Finset.univ.filter fun Q : Finset (Fin m) =>
      ‖(b : ℂ) + 2 * ∑ j ∈ Q, d j‖ ≤ 1).card : ℝ) ≤ goodCount v 1 := by
    rw [← hcount 1]
    exact_mod_cast hinj
  have hhalf : (1 / 2 : ℝ) ^ (n + 1) * 2 ^ n = 1 / 2 := by
    rw [pow_succ, mul_right_comm, ← mul_pow]
    norm_num
  unfold signedSumProb
  rw [le_div_iff₀ (by positivity)]
  calc (1 / 2 : ℝ) ^ (n + 1) * (1 - ρ)⁻¹ ^ ((n - 3) / 2 - K) * 2 ^ n
      = 1 / 2 * (1 - ρ)⁻¹ ^ ((n - 3) / 2 - K) := by
        rw [mul_right_comm, hhalf]
    _ ≤ 1 / 2 * (1 - ρ)⁻¹ ^ (m - K) := by gcongr
    _ ≤ _ := key
    _ ≤ goodCount v 1 := hgood

/-- The same bound for the infimum `minProb 1 n`. -/
theorem minProb_lower_bound_A {n : ℕ} (hn : Odd n) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) :
    (1 / 2 : ℝ) ^ (n + 1) * (1 - ρ)⁻¹ ^ ((n - 3) / 2 - ⌊(1152 : ℝ) / (1 - 2 * ρ) ^ 2⌋₊)
      ≤ minProb 1 n :=
  le_ciInf fun v => lower_bound_A hn hρ0 hρ1 v.1 v.2

end ReverseLittlewoodOfford

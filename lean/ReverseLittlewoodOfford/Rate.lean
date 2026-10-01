import ReverseLittlewoodOfford.LowerBound
import ReverseLittlewoodOfford.UpperConstruction
import ReverseLittlewoodOfford.Limit

/-!
# The exponential rate

For `1 < r < 2` put `ρ = 1 - 1/r`. The lower bound (A) gives
`F(2k + 1) ≥ C_r (r/4)^k`, and the Hollom–Sorkin construction gives `F(2k + 1) ≤ 2^{-k}`.
The squeeze lemma `tendsto_root_of_bounds` turns these into `F(n)^{1/n} → 1/√2`.
-/

set_option autoImplicit false

namespace ReverseLittlewoodOfford

open Filter Topology

/-- Lower bound in the form used by the squeeze lemma. -/
theorem minProb_ge_geometric {r : ℝ} (hr1 : 1 < r) (hr2 : r < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, C * (r / 4) ^ k ≤ minProb 1 (2 * k + 1) := by
  have hr0 : 0 < r := by linarith
  set ρ : ℝ := 1 - r⁻¹ with hρ
  have hrinv : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr1
  have hρ0 : 0 < ρ := by linarith
  have hρ1 : ρ < 1 / 2 := by
    have : (1 / 2 : ℝ) < r⁻¹ := by
      rw [lt_inv_comm₀ (by norm_num) hr0]
      linarith
    linarith
  have hinv : (1 - ρ)⁻¹ = r := by
    rw [hρ, sub_sub_cancel, inv_inv]
  set K := ⌊(1152 : ℝ) / (1 - 2 * ρ) ^ 2⌋₊
  refine ⟨1 / 4 * (r ^ (K + 1))⁻¹, by positivity, fun k => ?_⟩
  have hA := minProb_lower_bound_A (n := 2 * k + 1) (odd_two_mul_add_one k) hρ0 hρ1
  rw [hinv] at hA
  refine le_trans ?_ hA
  set e := (2 * k + 1 - 3) / 2 - K
  have he : k ≤ e + (K + 1) := by omega
  have hpow : r ^ k ≤ r ^ e * r ^ (K + 1) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hr1.le he
  have hhalf : (1 / 2 : ℝ) ^ (2 * k + 1 + 1) = 1 / 4 * (1 / 4) ^ k := by
    rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring, pow_add, pow_mul]
    norm_num
    ring
  rw [hhalf]
  have hrK : 0 < r ^ (K + 1) := by positivity
  calc 1 / 4 * (r ^ (K + 1))⁻¹ * (r / 4) ^ k
      = 1 / 4 * (1 / 4) ^ k * (r ^ k / r ^ (K + 1)) := by
        rw [div_pow]
        field_simp
        rw [← mul_pow]
        norm_num
    _ ≤ 1 / 4 * (1 / 4) ^ k * r ^ e := by
        gcongr
        rw [div_le_iff₀ hrK]
        exact hpow

/-- **Main theorem.** Along odd `n`, `F_{2,1}(n)^{1/n} → 1/√2`. -/
theorem rootSeq_tendsto : Tendsto rootSeq atTop (𝓝 (1 / Real.sqrt 2)) := by
  refine tendsto_root_of_bounds (fun k => minProb 1 (2 * k + 1)) (fun k => ?_)
    (fun r hr1 hr2 => minProb_ge_geometric hr1 hr2)
  have h := minProb_le_hollom_sorkin (n := 2 * k + 1) (odd_two_mul_add_one k)
  rwa [show (2 * k + 1) / 2 = k by omega] at h

end ReverseLittlewoodOfford

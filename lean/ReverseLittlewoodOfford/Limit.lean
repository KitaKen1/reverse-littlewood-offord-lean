import ReverseLittlewoodOfford.Defs

/-!
# From bounds to the limit

If `a k ≤ 2^{-k}` and, for every `1 < r < 2`, `a k ≥ C_r (r/4)^k` with `C_r > 0`, then
`a k ^ (1 / (2k + 1)) → 1/√2`. The upper bound gives `limsup ≤ 2^{-1/2}`, and the lower bounds
give `liminf ≥ √r / 2` for every `r < 2`.
-/

set_option autoImplicit false

namespace ReverseLittlewoodOfford

open Filter Topology

/-- The exponent `1 / (2k + 1)` tends to `0`. -/
private lemma tendsto_one_div_odd :
    Tendsto (fun k : ℕ => 1 / (2 * k + 1 : ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun k : ℕ => (2 * k + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
  exact tendsto_const_nhds.div_atTop h

/-- The product `k · (1 / (2k + 1))` tends to `1 / 2`. -/
private lemma tendsto_mul_one_div_odd :
    Tendsto (fun k : ℕ => (k : ℝ) * (1 / (2 * k + 1 : ℝ))) atTop (𝓝 (1 / 2)) := by
  have h := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub
    (tendsto_one_div_odd.const_mul (1 / 2 : ℝ))
  rw [mul_zero, sub_zero] at h
  refine h.congr fun k => ?_
  have hk : (2 * k + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- `(1/2)^(1/2) = 1/√2`. -/
private lemma half_rpow_half : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) = 1 / Real.sqrt 2 := by
  rw [Real.sqrt_eq_rpow, Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow]

/-- Squeeze lemma for the `n`-th roots along odd `n = 2k + 1`. -/
theorem tendsto_root_of_bounds (a : ℕ → ℝ)
    (hup : ∀ k : ℕ, a k ≤ (1 / 2 : ℝ) ^ k)
    (hlow : ∀ r : ℝ, 1 < r → r < 2 →
      ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, C * (r / 4) ^ k ≤ a k) :
    Tendsto (fun k : ℕ => a k ^ (1 / (2 * k + 1 : ℝ))) atTop (𝓝 (1 / Real.sqrt 2)) := by
  -- positivity of `a k`
  obtain ⟨C₀, hC₀, hC₀k⟩ := hlow (3 / 2) (by norm_num) (by norm_num)
  have hpos : ∀ k : ℕ, 0 < a k := fun k => lt_of_lt_of_le (by positivity) (hC₀k k)
  have he : ∀ k : ℕ, (0 : ℝ) ≤ 1 / (2 * k + 1 : ℝ) := fun k => by positivity
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · -- lower bound
    have hc : Tendsto (fun r : ℝ => (r / 4) ^ (1 / 2 : ℝ)) (𝓝[<] 2) (𝓝 (1 / Real.sqrt 2)) := by
      have hcont : Continuous (fun r : ℝ => (r / 4) ^ (1 / 2 : ℝ)) :=
        (continuous_id.div_const 4).rpow_const fun _ => Or.inr (by norm_num)
      have h2 : ((2 : ℝ) / 4) ^ (1 / 2 : ℝ) = 1 / Real.sqrt 2 := by
        rw [← half_rpow_half]; norm_num
      rw [← h2]
      exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ r in 𝓝[<] (2 : ℝ), (1 < r ∧ b < (r / 4) ^ (1 / 2 : ℝ)) ∧ r < 2 :=
      ((eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds (by norm_num))).and
        (hc.eventually (lt_mem_nhds hb))).and self_mem_nhdsWithin
    obtain ⟨r, ⟨hr1, hrb⟩, hr2⟩ := hev.exists
    obtain ⟨C, hC, hCk⟩ := hlow r hr1 hr2
    have hl : Tendsto (fun k : ℕ => C ^ (1 / (2 * k + 1 : ℝ)) *
        (r / 4) ^ ((k : ℝ) * (1 / (2 * k + 1 : ℝ)))) atTop
        (𝓝 (C ^ (0 : ℝ) * (r / 4) ^ (1 / 2 : ℝ))) :=
      (tendsto_const_nhds.rpow tendsto_one_div_odd (Or.inl hC.ne')).mul
        (tendsto_const_nhds.rpow tendsto_mul_one_div_odd (Or.inl (by positivity)))
    rw [Real.rpow_zero, one_mul] at hl
    refine (hl.eventually (lt_mem_nhds hrb)).mono fun k hk => hk.trans_le ?_
    calc C ^ (1 / (2 * k + 1 : ℝ)) * (r / 4) ^ ((k : ℝ) * (1 / (2 * k + 1 : ℝ)))
        = (C * (r / 4) ^ k) ^ (1 / (2 * k + 1 : ℝ)) := by
          rw [Real.mul_rpow hC.le (by positivity), Real.rpow_mul (by positivity),
            Real.rpow_natCast]
      _ ≤ a k ^ (1 / (2 * k + 1 : ℝ)) := Real.rpow_le_rpow (by positivity) (hCk k) (he k)
  · -- upper bound
    have hu : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ ((k : ℝ) * (1 / (2 * k + 1 : ℝ)))) atTop
        (𝓝 (1 / Real.sqrt 2)) := by
      rw [← half_rpow_half]
      exact tendsto_const_nhds.rpow tendsto_mul_one_div_odd (Or.inl (by norm_num))
    refine (hu.eventually (gt_mem_nhds hb)).mono fun k hk => lt_of_le_of_lt ?_ hk
    calc a k ^ (1 / (2 * k + 1 : ℝ)) ≤ ((1 / 2 : ℝ) ^ k) ^ (1 / (2 * k + 1 : ℝ)) :=
          Real.rpow_le_rpow (hpos k).le (hup k) (he k)
      _ = (1 / 2 : ℝ) ^ ((k : ℝ) * (1 / (2 * k + 1 : ℝ))) := by
          rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]

end ReverseLittlewoodOfford

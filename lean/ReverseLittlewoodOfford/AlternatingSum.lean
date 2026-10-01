import ReverseLittlewoodOfford.Defs

/-!
# Lemma 1: alternating sums in a closed half-plane

An odd family of unit vectors, sorted by angle inside a closed half-plane, has alternating
sum of norm at most one. We prove a version with a general coefficient pattern `c`: the partial
sums of `c` stay in `[0, 1]` and end at `1`. The alternating pattern `1, -1, 1, …, 1` is the
basic example, and deleting an adjacent cancelling pair keeps the property; this is what makes
the deletion in Lemma 4 hereditary.

The proof moves the cut of the half-plane so that it is centred on the line of the sum, then
applies a layer-cake bound to the coordinates along that line.
-/

set_option autoImplicit false

namespace ReverseLittlewoodOfford

open Real Finset

/-- The partial sums `∑_{l<k} c l` of a coefficient sequence. -/
def partialSum (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ l ∈ range k, c l

/-- A coefficient pattern on `0, …, s - 1` whose partial sums stay in `[0, 1]` and end at `1`. -/
def AltPattern (c : ℕ → ℝ) (s : ℕ) : Prop :=
  (∀ k ≤ s, 0 ≤ partialSum c k ∧ partialSum c k ≤ 1) ∧ partialSum c s = 1

/-- Layer-cake core of Lemma 1: if every interval sum of `c` lies in `[-1, 1]` and `y` is a
unimodal sequence in `[0, M]`, then `|∑ c l * y l| ≤ M`. -/
theorem abs_sum_mul_le_of_unimodal (s : ℕ) (c y : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hc : ∀ a b, a ≤ b → b ≤ s → |∑ l ∈ Ico a b, c l| ≤ 1)
    (hy : ∀ k < s, 0 ≤ y k ∧ y k ≤ M)
    (huni : ∀ i j k, i ≤ j → j ≤ k → k < s → min (y i) (y k) ≤ y j) :
    |∑ l ∈ range s, c l * y l| ≤ M := by
  induction s generalizing c y M with
  | zero => simpa using hM
  | succ s ih =>
    -- peel off the bottom layer `m = min (y 0) (y s)`, which lies below every `y k`
    set m := min (y 0) (y s) with hm_def
    have hm_le : ∀ k ≤ s, m ≤ y k := fun k hk =>
      huni 0 k s (Nat.zero_le _) hk (Nat.lt_succ_self _)
    have hm0 : 0 ≤ m := le_min (hy 0 (Nat.succ_pos _)).1 (hy s (Nat.lt_succ_self _)).1
    have hmM : m ≤ M := (min_le_left _ _).trans (hy 0 (Nat.succ_pos _)).2
    have hsplit : ∑ l ∈ range (s + 1), c l * y l =
        m * ∑ l ∈ range (s + 1), c l + ∑ l ∈ range (s + 1), c l * (y l - m) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hfirst : |m * ∑ l ∈ range (s + 1), c l| ≤ m := by
      rw [abs_mul, abs_of_nonneg hm0]
      have h1 := hc 0 (s + 1) (Nat.zero_le _) le_rfl
      rw [← Finset.range_eq_Ico] at h1
      calc m * |∑ l ∈ range (s + 1), c l| ≤ m * 1 := mul_le_mul_of_nonneg_left h1 hm0
        _ = m := mul_one m
    -- the rest `y - m` vanishes at an endpoint, so it is supported on `s` consecutive indices
    have hsecond : |∑ l ∈ range (s + 1), c l * (y l - m)| ≤ M - m := by
      rcases le_or_gt (y s) (y 0) with h | h
      · have hms : m = y s := min_eq_right h
        rw [Finset.sum_range_succ, ← hms, sub_self, mul_zero, add_zero]
        refine ih c (fun l => y l - m) (M - m) (by linarith) ?_ ?_ ?_
        · exact fun a b hab hb => hc a b hab (hb.trans (Nat.le_succ s))
        · intro k hk
          have h1 := hy k (by omega)
          exact ⟨by linarith [hm_le k hk.le], by linarith [h1.2]⟩
        · intro i j k hij hjk hk
          simp only [min_sub_sub_right]
          linarith [huni i j k hij hjk (by omega)]
      · have hm0' : m = y 0 := min_eq_left h.le
        rw [Finset.sum_range_succ', ← hm0', sub_self, mul_zero, add_zero]
        refine ih (fun l => c (l + 1)) (fun l => y (l + 1) - m) (M - m) (by linarith) ?_ ?_ ?_
        · intro a b hab hb
          rw [Finset.sum_Ico_add' c a b 1]
          exact hc (a + 1) (b + 1) (by omega) (by omega)
        · intro k hk
          have h1 := hy (k + 1) (by omega)
          exact ⟨by linarith [hm_le (k + 1) (by omega)], by linarith [h1.2]⟩
        · intro i j k hij hjk hk
          simp only [min_sub_sub_right]
          linarith [huni (i + 1) (j + 1) (k + 1) (by omega) (by omega) (by omega)]
    calc |∑ l ∈ range (s + 1), c l * y l|
        = |m * ∑ l ∈ range (s + 1), c l + ∑ l ∈ range (s + 1), c l * (y l - m)| := by
          rw [hsplit]
      _ ≤ |m * ∑ l ∈ range (s + 1), c l| + |∑ l ∈ range (s + 1), c l * (y l - m)| :=
          abs_add_le _ _
      _ ≤ m + (M - m) := add_le_add hfirst hsecond
      _ = M := by ring

/-- Cut index of a sorted sequence: the indices whose value lies below a threshold form an
initial segment `[0, j)`. -/
private theorem exists_cut (s : ℕ) (θ : ℕ → ℝ) (t : ℝ)
    (hθ : ∀ i j, i ≤ j → j < s → θ i ≤ θ j) :
    ∃ j ≤ s, (∀ k < j, θ k < t) ∧ (∀ k, j ≤ k → k < s → t ≤ θ k) := by
  classical
  have hex : ∃ k, k = s ∨ t ≤ θ k := ⟨s, Or.inl rfl⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (Or.inl rfl), fun k hk => ?_, fun k hjk hks => ?_⟩
  · have h := Nat.find_min hex hk
    rw [not_or, not_le] at h
    exact h.2
  · rcases Nat.find_spec hex with h | h
    · omega
    · exact h.trans (hθ _ _ hjk hks)

/-- Interval sums lie in `[-1, 1]` once all partial sums lie in a window `[L, L + 1]`. -/
private theorem abs_sum_Ico_le_one_of_window (s : ℕ) (c : ℕ → ℝ) (L : ℝ)
    (h : ∀ t ≤ s, L ≤ ∑ l ∈ range t, c l ∧ ∑ l ∈ range t, c l ≤ L + 1) :
    ∀ a b, a ≤ b → b ≤ s → |∑ l ∈ Ico a b, c l| ≤ 1 := by
  intro a b hab hb
  rw [Finset.sum_Ico_eq_sub _ hab, abs_le]
  have ha := h a (hab.trans hb)
  have hb' := h b hb
  constructor <;> linarith [ha.1, ha.2, hb'.1, hb'.2]

/-- `cos` is unimodal on `[-π/2, π/2]`. -/
private theorem min_cos_le_cos {x y z : ℝ} (hx : -(π / 2) ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hz : z ≤ π / 2) : min (cos x) (cos z) ≤ cos y := by
  rcases le_total y 0 with h | h
  · apply min_le_of_left_le
    rw [← Real.cos_neg x, ← Real.cos_neg y]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
      (by linarith)
  · apply min_le_of_right_le
    exact Real.cos_le_cos_of_nonneg_of_le_pi h (by linarith [Real.pi_pos]) hyz

/-- The real core of Lemma 1 once the cut is placed: the first `j` angles lie below the cut
line `ψ - π/2`. Moving them to the end, with angle shifted by `π` and coefficient negated,
gives a sorted family in `[-π/2, π/2]` around the direction `ψ`, to which the layer-cake
bound applies. -/
private theorem abs_sum_cos_le_one_of_cut (n j : ℕ) (θ c : ℕ → ℝ) (ψ : ℝ) (hψ0 : 0 ≤ ψ)
    (hψπ : ψ ≤ π)
    (hθ : ∀ i k, i ≤ k → k < n + j → θ i ≤ θ k)
    (hrange : ∀ k < n + j, θ k ∈ Set.Icc (-(π / 2)) (π / 2))
    (hc : AltPattern c (n + j))
    (hlow : ∀ k < j, θ k < ψ - π / 2)
    (hhigh : ∀ k, j ≤ k → k < n + j → ψ - π / 2 ≤ θ k) :
    |∑ k ∈ range (n + j), c k * cos (θ k - ψ)| ≤ 1 := by
  obtain ⟨c', hc'⟩ : ∃ c' : ℕ → ℝ, ∀ m, c' m = if m < n then c (j + m) else -c (m - n) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : ℕ → ℝ,
      ∀ m, φ m = if m < n then θ (j + m) - ψ else θ (m - n) + π - ψ :=
    ⟨_, fun _ => rfl⟩
  -- the sum is unchanged by the cyclic shift
  have hsum : ∑ k ∈ range (n + j), c k * cos (θ k - ψ) =
      ∑ m ∈ range (n + j), c' m * cos (φ m) := by
    rw [Finset.sum_range_add (fun m => c' m * cos (φ m)), add_comm n j,
      Finset.sum_range_add, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.mem_range] at hm
      rw [hc', hφ, if_pos hm, if_pos hm]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [hc', hφ, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left,
        show θ m + π - ψ = (θ m - ψ) + π by ring, Real.cos_add_pi]
      ring
  rw [hsum]
  -- the new angles are sorted and lie in `[-π/2, π/2]`
  have hφrange : ∀ m < n + j, -(π / 2) ≤ φ m ∧ φ m ≤ π / 2 := by
    intro m hm
    rw [hφ]
    split_ifs with h
    · have h1 := hrange (j + m) (by omega)
      have h2 := hhigh (j + m) (by omega) (by omega)
      constructor <;> linarith [h1.1, h1.2]
    · have h1 := hrange (m - n) (by omega)
      have h2 := hlow (m - n) (by omega)
      constructor <;> linarith [h1.1, h1.2]
  have hφmono : ∀ a b, a ≤ b → b < n + j → φ a ≤ φ b := by
    intro a b hab hb
    rw [hφ a, hφ b]
    split_ifs with ha hb' hb'
    · linarith [hθ (j + a) (j + b) (by omega) (by omega)]
    · have h1 := (hrange (j + a) (by omega)).2
      have h2 := (hrange (b - n) (by omega)).1
      linarith
    · omega
    · linarith [hθ (a - n) (b - n) (by omega) (by omega)]
  -- partial sums of the shifted coefficients stay in the window `[-P j, 1 - P j]`
  have hQ1 : ∀ t ≤ n, ∑ l ∈ range t, c' l = partialSum c (j + t) - partialSum c j := by
    intro t ht
    rw [partialSum, partialSum, Finset.sum_range_add, add_sub_cancel_left]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_range] at hl
    rw [hc', if_pos (by omega)]
  have hQ2 : ∀ u ≤ j, ∑ l ∈ range (n + u), c' l = 1 - partialSum c j - partialSum c u := by
    intro u hu
    rw [Finset.sum_range_add, hQ1 n le_rfl, add_comm j n, hc.2]
    have h : ∑ l ∈ range u, c' (n + l) = -partialSum c u := by
      rw [partialSum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hc', if_neg (by omega), Nat.add_sub_cancel_left]
    rw [h]
    ring
  have hwin : ∀ t ≤ n + j, -partialSum c j ≤ ∑ l ∈ range t, c' l ∧
      ∑ l ∈ range t, c' l ≤ -partialSum c j + 1 := by
    intro t ht
    rcases le_or_gt t n with h | h
    · rw [hQ1 t h]
      have h1 := hc.1 (j + t) (by omega)
      constructor <;> linarith [h1.1, h1.2]
    · obtain ⟨u, rfl⟩ : ∃ u, t = n + u := ⟨t - n, by omega⟩
      rw [hQ2 u (by omega)]
      have h1 := hc.1 u (by omega)
      constructor <;> linarith [h1.1, h1.2]
  -- apply the layer-cake bound
  refine abs_sum_mul_le_of_unimodal (n + j) c' (fun m => cos (φ m)) 1 zero_le_one
    (abs_sum_Ico_le_one_of_window (n + j) c' _ hwin) ?_ ?_
  · intro k hk
    exact ⟨Real.cos_nonneg_of_mem_Icc ⟨(hφrange k hk).1, (hφrange k hk).2⟩, Real.cos_le_one _⟩
  · intro i j' k hij hjk hk
    exact min_cos_le_cos (hφrange i (by omega)).1 (hφmono i j' hij (by omega))
      (hφmono j' k hjk hk) (hφrange k hk).2

/-- **Lemma 1, general pattern.** Unit vectors sorted by angle in a closed half-plane, with a
coefficient pattern whose partial sums stay in `[0, 1]` and end at `1`, have weighted sum in the
closed unit disc. -/
theorem norm_sum_le_one_of_altPattern (s : ℕ) (θ c : ℕ → ℝ)
    (hθ : ∀ i j, i ≤ j → j < s → θ i ≤ θ j)
    (hrange : ∀ k < s, θ k ∈ Set.Icc (-(π / 2)) (π / 2))
    (hc : AltPattern c s) :
    ‖∑ k ∈ range s, (c k : ℂ) * Complex.exp (θ k * Complex.I)‖ ≤ 1 := by
  set U := ∑ k ∈ range s, (c k : ℂ) * Complex.exp (θ k * Complex.I) with hU
  -- the coordinate of `U` along the direction `ψ`
  have hre : ∀ ψ : ℝ, (U * Complex.exp (-(ψ : ℂ) * Complex.I)).re =
      ∑ k ∈ range s, c k * cos (θ k - ψ) := by
    intro ψ
    rw [hU, Finset.sum_mul, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, ← Complex.exp_add,
      show (θ k : ℂ) * Complex.I + -(ψ : ℂ) * Complex.I = ((θ k - ψ : ℝ) : ℂ) * Complex.I by
        push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  -- choose the direction `ψ ∈ [0, π]` of the line through `U`
  obtain ⟨ψ, ⟨hψ0, hψπ⟩, hψ⟩ : ∃ ψ ∈ Set.Icc 0 π,
      ‖U‖ = |(U * Complex.exp (-(ψ : ℂ) * Complex.I)).re| := by
    have h1 : U * Complex.exp (-(U.arg : ℂ) * Complex.I) = (‖U‖ : ℂ) := by
      calc U * Complex.exp (-(U.arg : ℂ) * Complex.I)
          = (‖U‖ : ℂ) * Complex.exp (U.arg * Complex.I) * Complex.exp (-(U.arg : ℂ) * Complex.I)
            := by rw [Complex.norm_mul_exp_arg_mul_I U]
        _ = (‖U‖ : ℂ) := by
          rw [mul_assoc, ← Complex.exp_add,
            show (U.arg : ℂ) * Complex.I + -(U.arg : ℂ) * Complex.I = 0 by ring,
            Complex.exp_zero, mul_one]
    by_cases h : 0 ≤ U.arg
    · refine ⟨U.arg, ⟨h, Complex.arg_le_pi U⟩, ?_⟩
      rw [h1, Complex.ofReal_re, abs_of_nonneg (norm_nonneg U)]
    · refine ⟨U.arg + π, ⟨by linarith [Complex.neg_pi_lt_arg U], by linarith⟩, ?_⟩
      have h2 : U * Complex.exp (-((U.arg + π : ℝ) : ℂ) * Complex.I) = -(‖U‖ : ℂ) := by
        rw [show -((U.arg + π : ℝ) : ℂ) * Complex.I
            = -(U.arg : ℂ) * Complex.I + -((π : ℂ) * Complex.I) by push_cast; ring,
          Complex.exp_add, ← mul_assoc, h1, Complex.exp_neg, Complex.exp_pi_mul_I]
        simp
      rw [h2, Complex.neg_re, Complex.ofReal_re, abs_neg, abs_of_nonneg (norm_nonneg U)]
  rw [hψ, hre ψ]
  clear hψ hre hU U
  -- place the cut at `ψ - π/2`
  obtain ⟨j, hjs, hlow, hhigh⟩ := exists_cut s θ (ψ - π / 2) hθ
  obtain ⟨n, rfl⟩ : ∃ n, s = n + j := ⟨s - j, by omega⟩
  exact abs_sum_cos_le_one_of_cut n j θ c ψ hψ0 hψπ hθ hrange hc hlow hhigh

/-- The alternating pattern `1, -1, 1, …` of odd length. -/
theorem altPattern_neg_one_pow {s : ℕ} (hs : Odd s) :
    AltPattern (fun k => (-1 : ℝ) ^ k) s := by
  have key : ∀ k, partialSum (fun k => (-1 : ℝ) ^ k) k = if Even k then 0 else 1 := by
    intro k
    induction k with
    | zero => simp [partialSum]
    | succ k ih =>
      rw [partialSum, Finset.sum_range_succ, ← partialSum, ih]
      by_cases h : Even k
      · rw [if_pos h, if_neg (Nat.even_add_one.not.mpr (not_not.mpr h)), h.neg_one_pow]
        norm_num
      · rw [if_neg h, if_pos (Nat.even_add_one.mpr h), (Nat.not_even_iff_odd.mp h).neg_one_pow]
        norm_num
  refine ⟨fun k _ => ?_, ?_⟩
  · rw [key]
    split_ifs <;> norm_num
  · rw [key, if_neg (Nat.not_even_iff_odd.mpr hs)]

/-- Deleting an adjacent cancelling pair keeps the pattern property. -/
theorem AltPattern.delete_pair {c : ℕ → ℝ} {s a : ℕ} (hc : AltPattern c s) (ha : a + 1 < s)
    (hcancel : c a + c (a + 1) = 0) :
    AltPattern (fun k => if k = a ∨ k = a + 1 then 0 else c k) s := by
  set c' : ℕ → ℝ := fun k => if k = a ∨ k = a + 1 then 0 else c k with hc'
  -- partial sums of `c'` agree with those of `c`, except at `a + 1` where they equal `P a`
  have h1 : ∀ k ≤ a, partialSum c' k = partialSum c k := by
    intro k hk
    unfold partialSum
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_range] at hl
    simp only [hc']
    rw [if_neg (by omega)]
  have h2 : partialSum c' (a + 1) = partialSum c a := by
    rw [partialSum, Finset.sum_range_succ, ← partialSum, h1 a le_rfl]
    simp [hc']
  have h3 : ∀ k, a + 2 ≤ k → partialSum c' k = partialSum c k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      rw [partialSum, Finset.sum_range_succ, ← partialSum, h2, partialSum, partialSum,
        Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [hc', or_true, ↓reduceIte, add_zero]
      linarith
    | succ k hk ih =>
      rw [partialSum, Finset.sum_range_succ, ← partialSum, ih, partialSum, partialSum,
        Finset.sum_range_succ]
      simp only [hc']
      rw [if_neg (by omega)]
  refine ⟨fun k hk => ?_, ?_⟩
  · rcases lt_trichotomy k (a + 1) with h | h | h
    · rw [h1 k (by omega)]
      exact hc.1 k hk
    · rw [h, h2]
      exact hc.1 a (by omega)
    · rw [h3 k (by omega)]
      exact hc.1 k hk
  · rw [h3 s (by omega)]
    exact hc.2

/-- **Lemma 1.** An odd family of unit vectors sorted by angle in a closed half-plane has
alternating sum $\lVert w_1 - w_2 + w_3 - \dots + w_s \rVert \le 1$. -/
theorem alternating_sum_norm_le_one {s : ℕ} (hs : Odd s) (θ : Fin s → ℝ) (hθ : Monotone θ)
    (hrange : ∀ i, θ i ∈ Set.Icc (-(π / 2)) (π / 2)) :
    ‖∑ i : Fin s, (-1 : ℂ) ^ (i : ℕ) * Complex.exp (θ i * Complex.I)‖ ≤ 1 := by
  set θ' : ℕ → ℝ := fun k => if h : k < s then θ ⟨k, h⟩ else 0 with hθ'
  have hθ'mono : ∀ i j, i ≤ j → j < s → θ' i ≤ θ' j := by
    intro i j hij hj
    simp only [hθ', dif_pos hj, dif_pos (lt_of_le_of_lt hij hj)]
    exact hθ (Fin.mk_le_mk.mpr hij)
  have hθ'range : ∀ k < s, θ' k ∈ Set.Icc (-(π / 2)) (π / 2) := by
    intro k hk
    simp only [hθ', dif_pos hk]
    exact hrange _
  have h := norm_sum_le_one_of_altPattern s θ' (fun k => (-1 : ℝ) ^ k) hθ'mono hθ'range
    (altPattern_neg_one_pow hs)
  calc ‖∑ i : Fin s, (-1 : ℂ) ^ (i : ℕ) * Complex.exp (θ i * Complex.I)‖
      = ‖∑ k ∈ range s, (((-1 : ℝ) ^ k : ℝ) : ℂ) * Complex.exp (θ' k * Complex.I)‖ := by
        rw [← Fin.sum_univ_eq_sum_range]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hθ', dif_pos i.2, Fin.eta]
        push_cast
        rfl
    _ ≤ 1 := h

end ReverseLittlewoodOfford

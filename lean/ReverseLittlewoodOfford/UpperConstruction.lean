import ReverseLittlewoodOfford.Defs

/-!
# The upper bound of Hollom and Sorkin

For odd `n = 2k + 1`, take `k` pairs of equal unit vectors whose vertical coordinates decrease
geometrically, together with one copy of `1`. A signed sum lies in the closed unit disc only
when every pair cancels, so the probability is at most `2^{-k}` (Hollom–Sorkin,
arXiv:2510.05044, Theorem 1.3).

To avoid square roots, the `i`-th pair is the rational point
`((1 - t²) + 2t·I) / (1 + t²)` of the unit circle with `t = (1/20)^(i+1)`. If some pair does not
cancel and `i₀` is the first such pair, then the imaginary part of the signed sum is at least
`3.5 t` in absolute value, with `t = (1/20)^(i₀+1)`, while the real part is an odd integer up
to an error of at most `4.5 t²`; hence the sum has norm greater than `1`.
-/

set_option autoImplicit false

namespace ReverseLittlewoodOfford

namespace HollomSorkin

open Finset

/-- The rational point `((1 - t²) + 2t·I) / (1 + t²)` of the unit circle. -/
noncomputable def circlePt (t : ℝ) : ℂ := ⟨1 - 2 * t ^ 2 / (1 + t ^ 2), 2 * t / (1 + t ^ 2)⟩

lemma circlePt_re (t : ℝ) : (circlePt t).re = 1 - 2 * t ^ 2 / (1 + t ^ 2) := rfl

lemma circlePt_im (t : ℝ) : (circlePt t).im = 2 * t / (1 + t ^ 2) := rfl

lemma norm_circlePt (t : ℝ) : ‖circlePt t‖ = 1 := by
  have h : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have h2 : ‖circlePt t‖ ^ 2 = 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, circlePt_re, circlePt_im]
    field_simp
    ring
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp h2

/-- The parameter `t_i = (1/20)^(i+1)` of the `i`-th pair. -/
noncomputable def param (i : ℕ) : ℝ := (1 / 20 : ℝ) ^ (i + 1)

lemma param_pos (i : ℕ) : 0 < param i := by
  unfold param
  positivity

lemma param_anti {i j : ℕ} (h : i ≤ j) : param j ≤ param i :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

lemma param_le (i : ℕ) : param i ≤ 1 / 20 := by
  have := param_anti (Nat.zero_le i)
  simpa [param] using this

/-- The geometric tail after `i₀` is at most `t_{i₀} / 19`. -/
lemma sum_Ico_param_le (i₀ k : ℕ) : ∑ i ∈ Ico (i₀ + 1) k, param i ≤ param i₀ / 19 := by
  have h := geom_sum_Ico_le_of_lt_one (x := (1 / 20 : ℝ)) (m := i₀ + 1) (n := k)
    (by norm_num) (by norm_num)
  calc ∑ i ∈ Ico (i₀ + 1) k, param i
        = (1 / 20) * ∑ i ∈ Ico (i₀ + 1) k, (1 / 20 : ℝ) ^ i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        unfold param
        ring
    _ ≤ (1 / 20) * ((1 / 20 : ℝ) ^ (i₀ + 1) / (1 - 1 / 20)) := by gcongr
    _ = param i₀ / 19 := by
        unfold param
        ring

/-- A sum whose terms vanish below `i₀` splits into its term at `i₀` and the tail. -/
lemma sum_range_eq_head_add_tail (k i₀ : ℕ) (hi₀ : i₀ < k) (F : ℕ → ℝ)
    (hF : ∀ i < i₀, F i = 0) :
    ∑ i ∈ range k, F i = F i₀ + ∑ i ∈ Ico (i₀ + 1) k, F i := by
  rw [← Finset.sum_range_add_sum_Ico F hi₀.le, Finset.sum_eq_sum_Ico_succ_bot hi₀,
    Finset.sum_eq_zero (fun i hi => hF i (Finset.mem_range.mp hi)), zero_add]

lemma abs_term_le (w : ℤ) (hw : -1 ≤ w ∧ w ≤ 1) (a : ℝ) (ha : 0 ≤ a) :
    |2 * (w : ℝ) * a| ≤ 2 * a := by
  have h1 : (-1 : ℝ) ≤ w := by exact_mod_cast hw.1
  have h2 : (w : ℝ) ≤ 1 := by exact_mod_cast hw.2
  rw [abs_le]
  constructor <;> nlinarith

lemma abs_term_eq (w : ℤ) (hw : -1 ≤ w ∧ w ≤ 1) (hw0 : w ≠ 0) (a : ℝ) (ha : 0 ≤ a) :
    |2 * (w : ℝ) * a| = 2 * a := by
  rcases (show w = -1 ∨ w = 1 by omega) with rfl | rfl
  · rw [abs_of_nonpos (by push_cast; linarith)]
    push_cast
    ring
  · rw [abs_of_nonneg (by push_cast; linarith)]
    push_cast
    ring

/-- The analytic heart: if the first pair that does not cancel is the `i₀`-th one, the signed
sum lies outside the closed unit disc. Here `2 * w i ∈ {-2, 0, 2}` is the combined sign of the
`i`-th pair and `s = ±1` is the sign of the last vector `1`. -/
lemma one_lt_norm_of_first_pair (k : ℕ) (w : ℕ → ℤ) (hw : ∀ i, -1 ≤ w i ∧ w i ≤ 1) (s : ℤ)
    (hs : s = 1 ∨ s = -1) (i₀ : ℕ) (hi₀ : i₀ < k) (hw0 : w i₀ ≠ 0)
    (hlt : ∀ i < i₀, w i = 0) :
    1 < ‖(s : ℂ) + ∑ i ∈ range k, 2 * (w i : ℂ) * circlePt (param i)‖ := by
  set t := param i₀ with ht_def
  have ht0 : 0 < t := param_pos i₀
  have ht1 : t ≤ 1 / 20 := param_le i₀
  set S : ℂ := (s : ℂ) + ∑ i ∈ range k, 2 * (w i : ℂ) * circlePt (param i) with hS
  set N : ℝ := (s : ℝ) + ∑ i ∈ range k, 2 * (w i : ℝ) with hN_def
  set R : ℝ := ∑ i ∈ range k, 2 * (w i : ℝ) * (2 * param i ^ 2 / (1 + param i ^ 2))
    with hR_def
  set I : ℝ := ∑ i ∈ range k, 2 * (w i : ℝ) * (2 * param i / (1 + param i ^ 2)) with hI_def
  have hre : S.re = N - R := by
    simp only [hS, hN_def, hR_def, Complex.add_re, Complex.re_sum, Complex.mul_re,
      circlePt_re, circlePt_im, Complex.intCast_re, Complex.intCast_im]
    simp
    rw [add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have him : S.im = I := by
    simp only [hS, hI_def, Complex.add_im, Complex.im_sum, Complex.mul_im, circlePt_re,
      circlePt_im, Complex.intCast_re, Complex.intCast_im]
    simp
  -- the real part is an odd integer up to a small error
  have hN : 1 ≤ N ∨ N ≤ -1 := by
    have hcast : N = ((s + 2 * ∑ i ∈ range k, w i : ℤ) : ℝ) := by
      rw [hN_def]
      push_cast
      rw [Finset.mul_sum]
    rw [hcast]
    rcases (show (1 : ℤ) ≤ s + 2 * ∑ i ∈ range k, w i ∨ s + 2 * ∑ i ∈ range k, w i ≤ -1
      by omega) with h | h
    · left
      exact_mod_cast h
    · right
      exact_mod_cast h
  have hR : |R| ≤ 9 / 2 * t ^ 2 := by
    have hsplit := sum_range_eq_head_add_tail k i₀ hi₀
      (fun i => 2 * (w i : ℝ) * (2 * param i ^ 2 / (1 + param i ^ 2)))
      (fun i hi => by simp [hlt i hi])
    rw [hR_def, hsplit]
    have hhead : |2 * (w i₀ : ℝ) * (2 * param i₀ ^ 2 / (1 + param i₀ ^ 2))| ≤ 4 * t ^ 2 := by
      refine (abs_term_le (w i₀) (hw i₀) _ (by positivity)).trans ?_
      have : 2 * t ^ 2 / (1 + t ^ 2) ≤ 2 * t ^ 2 :=
        div_le_self (by positivity) (by nlinarith)
      linarith
    have htail : |∑ i ∈ Ico (i₀ + 1) k, 2 * (w i : ℝ) * (2 * param i ^ 2 / (1 + param i ^ 2))|
        ≤ 4 * t * (t / 19) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i ∈ Ico (i₀ + 1) k, |2 * (w i : ℝ) * (2 * param i ^ 2 / (1 + param i ^ 2))|
          ≤ ∑ i ∈ Ico (i₀ + 1) k, 4 * t * param i := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hi' : i₀ + 1 ≤ i := (Finset.mem_Ico.mp hi).1
            have hti : param i ≤ t := param_anti (by omega)
            have hti0 : 0 < param i := param_pos i
            refine (abs_term_le (w i) (hw i) _ (by positivity)).trans ?_
            have : 2 * param i ^ 2 / (1 + param i ^ 2) ≤ 2 * param i ^ 2 :=
              div_le_self (by positivity) (by nlinarith)
            nlinarith
        _ = 4 * t * ∑ i ∈ Ico (i₀ + 1) k, param i := by rw [Finset.mul_sum]
        _ ≤ 4 * t * (t / 19) := by
            gcongr
            exact sum_Ico_param_le i₀ k
    calc |2 * (w i₀ : ℝ) * (2 * param i₀ ^ 2 / (1 + param i₀ ^ 2))
          + ∑ i ∈ Ico (i₀ + 1) k, 2 * (w i : ℝ) * (2 * param i ^ 2 / (1 + param i ^ 2))|
        ≤ |2 * (w i₀ : ℝ) * (2 * param i₀ ^ 2 / (1 + param i₀ ^ 2))|
          + |∑ i ∈ Ico (i₀ + 1) k, 2 * (w i : ℝ) * (2 * param i ^ 2 / (1 + param i ^ 2))| :=
          abs_add_le _ _
      _ ≤ 4 * t ^ 2 + 4 * t * (t / 19) := add_le_add hhead htail
      _ ≤ 9 / 2 * t ^ 2 := by nlinarith
  -- the imaginary part is dominated by the first pair that does not cancel
  have hI : 7 / 2 * t ≤ |I| := by
    have hsplit := sum_range_eq_head_add_tail k i₀ hi₀
      (fun i => 2 * (w i : ℝ) * (2 * param i / (1 + param i ^ 2)))
      (fun i hi => by simp [hlt i hi])
    rw [hI_def, hsplit]
    have hhead : |2 * (w i₀ : ℝ) * (2 * param i₀ / (1 + param i₀ ^ 2))| ≥ 19 / 5 * t := by
      rw [abs_term_eq (w i₀) (hw i₀) hw0 _ (by positivity)]
      have : 19 / 10 * t ≤ 2 * t / (1 + t ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    have htail : |∑ i ∈ Ico (i₀ + 1) k, 2 * (w i : ℝ) * (2 * param i / (1 + param i ^ 2))|
        ≤ 4 * (t / 19) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i ∈ Ico (i₀ + 1) k, |2 * (w i : ℝ) * (2 * param i / (1 + param i ^ 2))|
          ≤ ∑ i ∈ Ico (i₀ + 1) k, 4 * param i := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hti0 : 0 < param i := param_pos i
            refine (abs_term_le (w i) (hw i) _ (by positivity)).trans ?_
            have : 2 * param i / (1 + param i ^ 2) ≤ 2 * param i :=
              div_le_self (by positivity) (by nlinarith)
            linarith
        _ = 4 * ∑ i ∈ Ico (i₀ + 1) k, param i := by rw [Finset.mul_sum]
        _ ≤ 4 * (t / 19) := by
            gcongr
            exact sum_Ico_param_le i₀ k
    have htri := abs_add_le
      (2 * (w i₀ : ℝ) * (2 * param i₀ / (1 + param i₀ ^ 2))
        + ∑ i ∈ Ico (i₀ + 1) k, 2 * (w i : ℝ) * (2 * param i / (1 + param i ^ 2)))
      (-∑ i ∈ Ico (i₀ + 1) k, 2 * (w i : ℝ) * (2 * param i / (1 + param i ^ 2)))
    rw [add_neg_cancel_right, abs_neg] at htri
    linarith
  -- combine: `‖S‖² ≥ (1 - 4.5 t²)² + (3.5 t)² > 1`
  have hnorm : ‖S‖ ^ 2 = (N - R) ^ 2 + I ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  have hR' := abs_le.mp hR
  have hI2 : (7 / 2 * t) ^ 2 ≤ I ^ 2 := by
    rw [← sq_abs I]
    exact pow_le_pow_left₀ (by positivity) hI 2
  have hsmall : 0 ≤ 1 - 9 / 2 * t ^ 2 := by nlinarith
  have hNR : (1 - 9 / 2 * t ^ 2) ^ 2 ≤ (N - R) ^ 2 := by
    rcases hN with hN | hN
    · exact pow_le_pow_left₀ hsmall (by linarith) 2
    · have h1 : N - R ≤ -(1 - 9 / 2 * t ^ 2) := by linarith
      nlinarith
  have hsq : 1 < ‖S‖ ^ 2 := by
    rw [hnorm]
    nlinarith [mul_pos ht0 ht0]
  by_contra hcon
  push Not at hcon
  nlinarith [norm_nonneg S]

/-- The vectors: index `j < 2k` carries `circlePt (param (j / 2))`, index `2k` carries `1`. -/
noncomputable def hsVec (k j : ℕ) : ℂ := if j < 2 * k then circlePt (param (j / 2)) else 1

lemma norm_vec (k j : ℕ) : ‖hsVec k j‖ = 1 := by
  unfold hsVec
  split_ifs
  · exact norm_circlePt _
  · exact norm_one

/-- A sign vector on `Fin m`, extended by `false` to all of `ℕ`. -/
def extSign {m : ℕ} (ε : Fin m → Bool) (j : ℕ) : Bool :=
  if h : j < m then ε ⟨j, h⟩ else false

lemma extSign_fin {m : ℕ} (ε : Fin m → Bool) (j : Fin m) : extSign ε j = ε j := by
  simp [extSign, j.isLt]

/-- The sign `±1` of a Boolean. -/
def signInt (b : Bool) : ℤ := if b then 1 else -1

/-- Half the combined sign of a pair: `0` when the pair cancels, `±1` otherwise. -/
def pairCoeff (b b' : Bool) : ℤ := (if b then 1 else 0) + (if b' then 1 else 0) - 1

lemma pairCoeff_bounds (b b' : Bool) : -1 ≤ pairCoeff b b' ∧ pairCoeff b b' ≤ 1 := by
  cases b <;> cases b' <;> decide

lemma pairCoeff_eq_zero {b b' : Bool} (h : pairCoeff b b' = 0) : b' = !b := by
  cases b <;> cases b' <;> simp_all [pairCoeff]

lemma signInt_cases (b : Bool) : signInt b = 1 ∨ signInt b = -1 := by
  cases b <;> simp [signInt]

lemma sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : ℕ) :
    ∑ j ∈ range (2 * k), f j = ∑ i ∈ range k, (f (2 * i) + f (2 * i + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

/-- The signed sum of the construction, grouped into pairs. -/
lemma signedSum_vec (k : ℕ) (ε : Fin (2 * k + 1) → Bool) :
    signedSum (fun j : Fin (2 * k + 1) => hsVec k j) ε =
      (signInt (extSign ε (2 * k)) : ℂ)
        + ∑ i ∈ range k,
          2 * (pairCoeff (extSign ε (2 * i)) (extSign ε (2 * i + 1)) : ℂ) * circlePt (param i) := by
  unfold signedSum
  have h1 : ∀ j : Fin (2 * k + 1), (if ε j then hsVec k j else -hsVec k j)
      = (fun m : ℕ => if extSign ε m then hsVec k m else -hsVec k m) j := by
    intro j
    simp only [extSign_fin]
  rw [Finset.sum_congr rfl (fun j _ => h1 j),
    Fin.sum_univ_eq_sum_range (fun m => if extSign ε m then hsVec k m else -hsVec k m) (2 * k + 1),
    sum_range_succ, sum_range_two_mul, add_comm]
  congr 1
  · have : hsVec k (2 * k) = 1 := by simp [hsVec]
    rw [this]
    cases extSign ε (2 * k) <;> simp [signInt]
  · refine sum_congr rfl fun i hi => ?_
    have hi' : i < k := mem_range.mp hi
    have e1 : hsVec k (2 * i) = circlePt (param i) := by
      simp [hsVec, show 2 * i < 2 * k by omega, show 2 * i / 2 = i by omega]
    have e2 : hsVec k (2 * i + 1) = circlePt (param i) := by
      simp [hsVec, show 2 * i + 1 < 2 * k by omega, show (2 * i + 1) / 2 = i by omega]
    rw [e1, e2]
    cases extSign ε (2 * i) <;> cases extSign ε (2 * i + 1) <;> simp [pairCoeff] <;> ring

/-- In a sign vector whose signed sum lies in the closed unit disc, every pair cancels. -/
lemma pairs_cancel (k : ℕ) (ε : Fin (2 * k + 1) → Bool)
    (hε : ‖signedSum (fun j : Fin (2 * k + 1) => hsVec k j) ε‖ ≤ 1) :
    ∀ i < k, extSign ε (2 * i + 1) = !extSign ε (2 * i) := by
  set w : ℕ → ℤ := fun i => pairCoeff (extSign ε (2 * i)) (extSign ε (2 * i + 1)) with hw_def
  suffices h : ∀ i < k, w i = 0 from fun i hi => pairCoeff_eq_zero (h i hi)
  by_contra hcon
  push Not at hcon
  have hex : ∃ i, i < k ∧ w i ≠ 0 := hcon
  classical
  have hspec := Nat.find_spec hex
  have hmin : ∀ i < Nat.find hex, w i = 0 := by
    intro i hi
    have := Nat.find_min hex hi
    push Not at this
    exact this (hi.trans hspec.1)
  have hkey := one_lt_norm_of_first_pair k w (fun i => pairCoeff_bounds _ _)
    (signInt (extSign ε (2 * k))) (signInt_cases _) (Nat.find hex) hspec.1 hspec.2 hmin
  rw [signedSum_vec] at hε
  linarith

end HollomSorkin

open HollomSorkin in
/-- **Hollom–Sorkin, Theorem 1.3** (the inequality we need). -/
theorem hollom_sorkin_construction {n : ℕ} (hn : Odd n) :
    ∃ v : Fin n → ℂ, (∀ i, ‖v i‖ = 1) ∧ signedSumProb v 1 ≤ (1 / 2 : ℝ) ^ (n / 2) := by
  obtain ⟨k, rfl⟩ := hn
  refine ⟨fun j => hsVec k j, fun j => norm_vec k j, ?_⟩
  have hk : (2 * k + 1) / 2 = k := by omega
  rw [hk]
  -- a good sign vector is determined by its signs at the even indices `0, 2, …, 2k`
  have hcount : goodCount (fun j : Fin (2 * k + 1) => hsVec k j) 1 ≤ 2 ^ (k + 1) := by
    unfold goodCount
    have hcard : (Finset.univ : Finset (Fin (k + 1) → Bool)).card = 2 ^ (k + 1) := by
      simp
    rw [← hcard]
    refine Finset.card_le_card_of_injOn (fun ε j => extSign ε (2 * (j : ℕ)))
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_
    intro ε₁ h₁ ε₂ h₂ heq
    have hp₁ := pairs_cancel k ε₁ (Finset.mem_filter.mp (Finset.mem_coe.mp h₁)).2
    have hp₂ := pairs_cancel k ε₂ (Finset.mem_filter.mp (Finset.mem_coe.mp h₂)).2
    have hev : ∀ j, j ≤ k → extSign ε₁ (2 * j) = extSign ε₂ (2 * j) := by
      intro j hj
      exact congrFun heq ⟨j, by omega⟩
    funext m
    rw [← extSign_fin ε₁ m, ← extSign_fin ε₂ m]
    have hm := m.isLt
    rcases Nat.even_or_odd' (m : ℕ) with ⟨j, hj | hj⟩
    · rw [hj]
      exact hev j (by omega)
    · rw [hj, hp₁ j (by omega), hp₂ j (by omega), hev j (by omega)]
  unfold signedSumProb
  rw [div_le_iff₀ (by positivity)]
  calc (goodCount (fun j : Fin (2 * k + 1) => hsVec k j) 1 : ℝ) ≤ 2 ^ (k + 1) := by
        exact_mod_cast hcount
    _ = (1 / 2) ^ k * 2 ^ (2 * k + 1) := by
        rw [one_div_pow]
        field_simp
        ring

theorem minProb_le_hollom_sorkin {n : ℕ} (hn : Odd n) :
    minProb 1 n ≤ (1 / 2 : ℝ) ^ (n / 2) := by
  obtain ⟨v, hv, hprob⟩ := hollom_sorkin_construction hn
  exact (minProb_le 1 v hv).trans hprob

end ReverseLittlewoodOfford

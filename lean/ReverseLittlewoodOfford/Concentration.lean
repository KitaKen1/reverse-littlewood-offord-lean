import Mathlib

/-!
# Lemmas 5, 7 and 8: normalized length, stability and concentration

Write the alternating sum as `b` with `0 ≤ b ≤ 1` and put `δ = 1 - b`. A pair difference
`d = δ p + i √δ q` is measured in the normalized coordinates `(p, q)`. In these coordinates the
closed unit disc around `b` becomes `F(X, Y) = δ X² + Y² + 2 b X ≤ 1 + b`.

* Lemma 5: hereditary deletion bounds the total normalized length `∑ (p + |q|)` by `4`.
* Lemma 7 (`disc_stability`): a point within `g / 6` of a mean with slack `g` stays in the disc.
* Lemma 8: flip each light pair independently with probability `ρ`. The second moment of the
  deviation from the mean is small, so the subsets close to the mean carry at least half of the
  weight.

Counting the subsets close to the mean gives `many_good_flips`.
-/

set_option autoImplicit false

namespace ReverseLittlewoodOfford

open Real Finset

/-- The weight of `Q ⊆ L` when each element of `L` is chosen independently with probability
`ρ`. -/
noncomputable def flipWeight {ι : Type*} [DecidableEq ι] (ρ : ℝ) (L Q : Finset ι) : ℝ :=
  ρ ^ Q.card * (1 - ρ) ^ (L \ Q).card

/-- Adding a new element `x` to `L` and leaving it out of `Q` multiplies the weight by
`1 - ρ`. -/
lemma flipWeight_insert_of_notMem {ι : Type*} [DecidableEq ι] (ρ : ℝ) {L Q : Finset ι} {x : ι}
    (hx : x ∉ L) (hQ : Q ⊆ L) :
    flipWeight ρ (insert x L) Q = (1 - ρ) * flipWeight ρ L Q := by
  unfold flipWeight
  have hxQ : x ∉ Q := fun h => hx (hQ h)
  rw [Finset.insert_sdiff_of_notMem _ hxQ,
    Finset.card_insert_of_notMem (fun h => hx (Finset.sdiff_subset h))]
  ring

/-- Adding a new element `x` to both `L` and `Q` multiplies the weight by `ρ`. -/
lemma flipWeight_insert_insert {ι : Type*} [DecidableEq ι] (ρ : ℝ) {L Q : Finset ι} {x : ι}
    (hx : x ∉ L) (hQ : Q ⊆ L) :
    flipWeight ρ (insert x L) (insert x Q) = ρ * flipWeight ρ L Q := by
  unfold flipWeight
  have hxQ : x ∉ Q := fun h => hx (hQ h)
  rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem hx,
    Finset.card_insert_of_notMem hxQ]
  ring

/-- The weights form a probability distribution on the subsets of `L`. -/
theorem sum_flipWeight {ι : Type*} [DecidableEq ι] (ρ : ℝ) (L : Finset ι) :
    ∑ Q ∈ L.powerset, flipWeight ρ L Q = 1 := by
  induction L using Finset.induction_on with
  | empty => simp [flipWeight]
  | insert x L hx ih =>
    rw [Finset.sum_powerset_insert hx,
      Finset.sum_congr rfl fun Q hQ =>
        flipWeight_insert_of_notMem ρ hx (Finset.mem_powerset.1 hQ),
      Finset.sum_congr rfl fun Q hQ =>
        flipWeight_insert_insert ρ hx (Finset.mem_powerset.1 hQ),
      ← Finset.mul_sum, ← Finset.mul_sum, ih]
    ring

/-- The mean of `∑_{j ∈ Q} a j` for a random subset `Q` of `L`. -/
lemma sum_flipWeight_mul_sum {ι : Type*} [DecidableEq ι] (ρ : ℝ) (L : Finset ι)
    (a : ι → ℝ) :
    ∑ Q ∈ L.powerset, flipWeight ρ L Q * ∑ j ∈ Q, a j = ρ * ∑ j ∈ L, a j := by
  induction L using Finset.induction_on with
  | empty => simp
  | insert x L hx ih =>
    have h1 : ∀ Q ∈ L.powerset, flipWeight ρ (insert x L) Q * ∑ j ∈ Q, a j =
        (1 - ρ) * (flipWeight ρ L Q * ∑ j ∈ Q, a j) := by
      intro Q hQ
      rw [flipWeight_insert_of_notMem ρ hx (Finset.mem_powerset.1 hQ), mul_assoc]
    have h2 : ∀ Q ∈ L.powerset, flipWeight ρ (insert x L) (insert x Q) * ∑ j ∈ insert x Q, a j =
        ρ * (flipWeight ρ L Q * ∑ j ∈ Q, a j) + ρ * a x * flipWeight ρ L Q := by
      intro Q hQ
      rw [flipWeight_insert_insert ρ hx (Finset.mem_powerset.1 hQ),
        Finset.sum_insert fun h => hx (Finset.mem_powerset.1 hQ h)]
      ring
    rw [Finset.sum_powerset_insert hx, Finset.sum_congr rfl h1, Finset.sum_congr rfl h2,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ih,
      sum_flipWeight, Finset.sum_insert hx]
    ring

/-- The variance of `∑_{j ∈ Q} a j` for a random subset `Q` of `L`. -/
theorem sum_flipWeight_mul_sq {ι : Type*} [DecidableEq ι] (ρ : ℝ) (L : Finset ι) (a : ι → ℝ) :
    ∑ Q ∈ L.powerset, flipWeight ρ L Q * (∑ j ∈ Q, a j - ρ * ∑ j ∈ L, a j) ^ 2 =
      ρ * (1 - ρ) * ∑ j ∈ L, a j ^ 2 := by
  induction L using Finset.induction_on with
  | empty => simp [flipWeight]
  | insert x L hx ih =>
    have hm : ∑ Q ∈ L.powerset, flipWeight ρ L Q * (∑ j ∈ Q, a j - ρ * ∑ j ∈ L, a j) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, sum_flipWeight_mul_sum, ← Finset.sum_mul,
        sum_flipWeight]
      ring
    have h1 : ∀ Q ∈ L.powerset,
        flipWeight ρ (insert x L) Q * (∑ j ∈ Q, a j - ρ * ∑ j ∈ insert x L, a j) ^ 2 =
          (1 - ρ) * (flipWeight ρ L Q * (∑ j ∈ Q, a j - ρ * ∑ j ∈ L, a j) ^ 2)
          - 2 * ρ * (1 - ρ) * a x * (flipWeight ρ L Q * (∑ j ∈ Q, a j - ρ * ∑ j ∈ L, a j))
          + (1 - ρ) * ρ ^ 2 * a x ^ 2 * flipWeight ρ L Q := by
      intro Q hQ
      rw [flipWeight_insert_of_notMem ρ hx (Finset.mem_powerset.1 hQ), Finset.sum_insert hx]
      ring
    have h2 : ∀ Q ∈ L.powerset,
        flipWeight ρ (insert x L) (insert x Q) *
            (∑ j ∈ insert x Q, a j - ρ * ∑ j ∈ insert x L, a j) ^ 2 =
          ρ * (flipWeight ρ L Q * (∑ j ∈ Q, a j - ρ * ∑ j ∈ L, a j) ^ 2)
          + 2 * ρ * (1 - ρ) * a x * (flipWeight ρ L Q * (∑ j ∈ Q, a j - ρ * ∑ j ∈ L, a j))
          + ρ * (1 - ρ) ^ 2 * a x ^ 2 * flipWeight ρ L Q := by
      intro Q hQ
      have hxQ : x ∉ Q := fun h => hx (Finset.mem_powerset.1 hQ h)
      rw [flipWeight_insert_insert ρ hx (Finset.mem_powerset.1 hQ), Finset.sum_insert hx,
        Finset.sum_insert hxQ]
      ring
    rw [Finset.sum_powerset_insert hx, Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [ih, hm, sum_flipWeight, Finset.sum_insert hx]
    ring

/-- For `ρ ≤ 1/2`, no subset has weight above `(1 - ρ) ^ |L|`. -/
theorem flipWeight_le {ι : Type*} [DecidableEq ι] {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1 / 2)
    {L Q : Finset ι} (hQ : Q ⊆ L) :
    flipWeight ρ L Q ≤ (1 - ρ) ^ L.card := by
  unfold flipWeight
  rw [← Finset.card_sdiff_add_card_eq_card hQ, pow_add]
  calc ρ ^ Q.card * (1 - ρ) ^ (L \ Q).card ≤ (1 - ρ) ^ Q.card * (1 - ρ) ^ (L \ Q).card :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hρ0 (by linarith) _)
          (pow_nonneg (by linarith) _)
    _ = (1 - ρ) ^ (L \ Q).card * (1 - ρ) ^ Q.card := mul_comm _ _

/-- For `0 ≤ ρ ≤ 1` the weights are nonnegative. -/
lemma flipWeight_nonneg {ι : Type*} [DecidableEq ι] {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (L Q : Finset ι) : 0 ≤ flipWeight ρ L Q :=
  mul_nonneg (pow_nonneg hρ0 _) (pow_nonneg (by linarith) _)

/-- **Markov.** If the mean of `f ≥ 0` is at most `t / 2`, the subsets with `f Q ≤ t` carry
weight at least `1 / 2`. -/
lemma half_le_sum_flipWeight_filter {ι : Type*} [DecidableEq ι] {ρ t : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) (ht : 0 < t) (L : Finset ι) (f : Finset ι → ℝ) (hf : ∀ Q, 0 ≤ f Q)
    (hvar : ∑ Q ∈ L.powerset, flipWeight ρ L Q * f Q ≤ t / 2) :
    1 / 2 ≤ ∑ Q ∈ L.powerset.filter (fun Q => f Q ≤ t), flipWeight ρ L Q := by
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not L.powerset (fun Q => f Q ≤ t) (flipWeight ρ L)
  rw [sum_flipWeight] at hsplit
  have hbad : t * ∑ Q ∈ L.powerset.filter (fun Q => ¬ f Q ≤ t), flipWeight ρ L Q ≤ t / 2 := by
    rw [Finset.mul_sum]
    calc ∑ Q ∈ L.powerset.filter (fun Q => ¬ f Q ≤ t), t * flipWeight ρ L Q
        ≤ ∑ Q ∈ L.powerset.filter (fun Q => ¬ f Q ≤ t), flipWeight ρ L Q * f Q := by
          refine Finset.sum_le_sum fun Q hQ => ?_
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (not_le.1 (Finset.mem_filter.1 hQ).2).le
            (flipWeight_nonneg hρ0 hρ1 L Q)
      _ ≤ ∑ Q ∈ L.powerset, flipWeight ρ L Q * f Q :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun Q _ _ =>
            mul_nonneg (flipWeight_nonneg hρ0 hρ1 L Q) (hf Q)
      _ ≤ t / 2 := hvar
  have h2 : ∑ Q ∈ L.powerset.filter (fun Q => ¬ f Q ≤ t), flipWeight ρ L Q ≤ 1 / 2 := by
    refine le_of_mul_le_mul_left ?_ ht
    linarith
  linarith

/-- A family of subsets of `L` of total weight at least `1 / 2` has at least
`(1 / 2) (1 - ρ)^{-|L|}` members. -/
lemma le_card_of_half_le_sum_flipWeight {ι : Type*} [DecidableEq ι] {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1 / 2) {L : Finset ι} {S : Finset (Finset ι)} (hS : S ⊆ L.powerset)
    (h : 1 / 2 ≤ ∑ Q ∈ S, flipWeight ρ L Q) :
    (1 / 2 : ℝ) * (1 - ρ)⁻¹ ^ L.card ≤ S.card := by
  have hpos : 0 < (1 - ρ) ^ L.card := pow_pos (by linarith) _
  have h2 : ∑ Q ∈ S, flipWeight ρ L Q ≤ S.card * (1 - ρ) ^ L.card := by
    calc ∑ Q ∈ S, flipWeight ρ L Q ≤ ∑ Q ∈ S, (1 - ρ) ^ L.card :=
          Finset.sum_le_sum fun Q hQ => flipWeight_le hρ0 hρ1 (Finset.mem_powerset.1 (hS hQ))
      _ = S.card * (1 - ρ) ^ L.card := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ hpos]
  linarith

/-- **Lemma 8, second moment.** If each term of `L` has `p + |q| ≤ η` and the total of `p + |q|`
on `L` is at most `4`, the mean squared deviation from the mean is at most `η`. -/
lemma sum_flipWeight_mul_dev_le {ι : Type*} [DecidableEq ι] {ρ η : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) (hη : 0 ≤ η) (L : Finset ι) (p q : ι → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hL : ∀ j ∈ L, p j + |q j| ≤ η) (hsum : ∑ j ∈ L, (p j + |q j|) ≤ 4) :
    ∑ Q ∈ L.powerset, flipWeight ρ L Q *
        ((∑ j ∈ Q, p j - ρ * ∑ j ∈ L, p j) ^ 2 + (∑ j ∈ Q, q j - ρ * ∑ j ∈ L, q j) ^ 2) ≤ η := by
  simp only [mul_add, Finset.sum_add_distrib, sum_flipWeight_mul_sq]
  have h1 : ∑ j ∈ L, p j ^ 2 + ∑ j ∈ L, q j ^ 2 ≤ η * 4 := by
    rw [← Finset.sum_add_distrib]
    calc ∑ j ∈ L, (p j ^ 2 + q j ^ 2) ≤ ∑ j ∈ L, η * (p j + |q j|) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have h3 := hL j hj
          have h4 := hp j
          have h5 := abs_nonneg (q j)
          have h6 : q j ^ 2 = |q j| ^ 2 := (sq_abs _).symm
          nlinarith
      _ = η * ∑ j ∈ L, (p j + |q j|) := by rw [Finset.mul_sum]
      _ ≤ η * 4 := mul_le_mul_of_nonneg_left hsum hη
  have h2 : ρ * (1 - ρ) ≤ 1 / 4 := by nlinarith [sq_nonneg (ρ - 1 / 2)]
  have h3 : 0 ≤ ρ * (1 - ρ) := mul_nonneg hρ0 (by linarith)
  have h4 : 0 ≤ ∑ j ∈ L, p j ^ 2 + ∑ j ∈ L, q j ^ 2 := by positivity
  nlinarith

/-- **Lemma 7 (stability).** In normalized coordinates, a point within `g / 6` of a mean with
slack `g` lies in the disc `δ X² + Y² + 2 b X ≤ 1 + b`. -/
theorem disc_stability {b δ g X Y μx μy : ℝ} (hb0 : 0 ≤ b) (hδ0 : 0 < δ) (hbδ : b + δ = 1)
    (hg0 : 0 < g) (hg1 : g ≤ 1) (hμx : 0 ≤ μx)
    (hμ : δ * μx ^ 2 + μy ^ 2 + 2 * b * μx ≤ (1 - g) * (1 + b))
    (hdev : (X - μx) ^ 2 + (Y - μy) ^ 2 ≤ (g / 6) ^ 2) :
    δ * X ^ 2 + Y ^ 2 + 2 * b * X ≤ 1 + b := by
  have hδ1 : δ ≤ 1 := by linarith
  have key : δ * X ^ 2 + Y ^ 2 + 2 * b * X = (δ * μx ^ 2 + μy ^ 2 + 2 * b * μx)
      + 2 * (δ * μx + b) * (X - μx) + 2 * μy * (Y - μy)
      + (δ * (X - μx) ^ 2 + (Y - μy) ^ 2) := by ring
  have hc0 : 0 ≤ δ * μx + b := by positivity
  have hsq : δ * μx ^ 2 + 2 * b * μx ≤ 1 + b := by nlinarith [sq_nonneg μy]
  have hc1 : (δ * μx + b) ^ 2 ≤ 1 ^ 2 := by
    have h1 : (δ * μx + b) ^ 2 = b ^ 2 + δ * (δ * μx ^ 2 + 2 * b * μx) := by ring
    have h2 : δ * (δ * μx ^ 2 + 2 * b * μx) ≤ δ * (1 + b) :=
      mul_le_mul_of_nonneg_left hsq hδ0.le
    have h3 : b ^ 2 + δ * (1 + b) = 1 := by
      have : δ = 1 - b := by linarith
      subst this; ring
    nlinarith
  have hc1' : δ * μx + b ≤ 1 := by
    have := abs_le_of_sq_le_sq hc1 zero_le_one
    rwa [abs_of_nonneg hc0] at this
  have hμy2 : μy ^ 2 ≤ (3 / 2) ^ 2 := by nlinarith [sq_nonneg μx]
  have hμy : |μy| ≤ 3 / 2 := abs_le_of_sq_le_sq hμy2 (by norm_num)
  have hex : |X - μx| ≤ g / 6 :=
    abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (Y - μy)]) (by positivity)
  have hey : |Y - μy| ≤ g / 6 :=
    abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (X - μx)]) (by positivity)
  have t1 : 2 * (δ * μx + b) * (X - μx) ≤ 2 * (g / 6) := by
    have : (δ * μx + b) * (X - μx) ≤ g / 6 := by
      calc (δ * μx + b) * (X - μx) ≤ |(δ * μx + b) * (X - μx)| := le_abs_self _
        _ = (δ * μx + b) * |X - μx| := by rw [abs_mul, abs_of_nonneg hc0]
        _ ≤ 1 * (g / 6) := mul_le_mul hc1' hex (abs_nonneg _) zero_le_one
        _ = g / 6 := one_mul _
    linarith
  have t2 : 2 * μy * (Y - μy) ≤ 2 * ((3 / 2) * (g / 6)) := by
    have : μy * (Y - μy) ≤ (3 / 2) * (g / 6) := by
      calc μy * (Y - μy) ≤ |μy * (Y - μy)| := le_abs_self _
        _ = |μy| * |Y - μy| := abs_mul _ _
        _ ≤ (3 / 2) * (g / 6) := mul_le_mul hμy hey (abs_nonneg _) (by norm_num)
    linarith
  have t3 : δ * (X - μx) ^ 2 + (Y - μy) ^ 2 ≤ (g / 6) ^ 2 := by
    nlinarith [sq_nonneg (X - μx)]
  rw [key]
  nlinarith

/-- In normalized coordinates `z = δ X + i s Y` with `s² = δ = 1 - b`, the disc
`‖b + z‖ ≤ 1` becomes `δ X² + Y² + 2 b X ≤ 1 + b`. -/
lemma norm_ofReal_add_le_one_iff {b δ s X Y : ℝ} (hδ0 : 0 < δ) (hbδ : b + δ = 1)
    (hs : s ^ 2 = δ) {z : ℂ} (hre : z.re = δ * X) (him : z.im = s * Y) :
    ‖(b : ℂ) + z‖ ≤ 1 ↔ δ * X ^ 2 + Y ^ 2 + 2 * b * X ≤ 1 + b := by
  have hn : ‖(b : ℂ) + z‖ ^ 2 = b ^ 2 + δ * (δ * X ^ 2 + Y ^ 2 + 2 * b * X) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, hre, him,
      zero_add]
    have e : s * Y * (s * Y) = s ^ 2 * Y ^ 2 := by ring
    rw [e, hs]
    ring
  have h1 : b ^ 2 + δ * (1 + b) = 1 := by
    have e : b = 1 - δ := by linarith
    rw [e]
    ring
  rw [← sq_le_one_iff₀ (norm_nonneg _), hn]
  constructor
  · intro h
    have h2 : δ * (δ * X ^ 2 + Y ^ 2 + 2 * b * X) ≤ δ * (1 + b) := by linarith
    exact le_of_mul_le_mul_left h2 hδ0
  · intro h
    have h2 : δ * (δ * X ^ 2 + Y ^ 2 + 2 * b * X) ≤ δ * (1 + b) :=
      mul_le_mul_of_nonneg_left h hδ0.le
    linarith

/-- **Lemma 5, imaginary part.** If every partial sum lies in the disc, the normalized imaginary
parts have total absolute value at most `3`. -/
lemma sum_abs_le_three {ι : Type*} [Fintype ι] {b δ : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hδ0 : 0 ≤ δ) (p q : ι → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hF : ∀ D : Finset ι,
      δ * (∑ j ∈ D, p j) ^ 2 + (∑ j ∈ D, q j) ^ 2 + 2 * b * ∑ j ∈ D, p j ≤ 1 + b) :
    ∑ j, |q j| ≤ 3 := by
  have hY : ∀ D : Finset ι, |∑ j ∈ D, q j| ≤ 3 / 2 := by
    intro D
    have hX : 0 ≤ ∑ j ∈ D, p j := Finset.sum_nonneg fun j _ => hp j
    have h := hF D
    apply abs_le_of_sq_le_sq _ (by norm_num)
    nlinarith [sq_nonneg (∑ j ∈ D, p j)]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun j => 0 ≤ q j)]
  have e1 : ∑ j ∈ univ.filter (fun j => 0 ≤ q j), |q j| =
      ∑ j ∈ univ.filter (fun j => 0 ≤ q j), q j :=
    Finset.sum_congr rfl fun j hj => abs_of_nonneg (Finset.mem_filter.1 hj).2
  have e2 : ∑ j ∈ univ.filter (fun j => ¬ 0 ≤ q j), |q j| =
      -∑ j ∈ univ.filter (fun j => ¬ 0 ≤ q j), q j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j hj => abs_of_neg (not_le.1 (Finset.mem_filter.1 hj).2)
  rw [e1, e2]
  have h1 := le_abs_self (∑ j ∈ univ.filter (fun j => 0 ≤ q j), q j)
  have h2 := neg_le_abs (∑ j ∈ univ.filter (fun j => ¬ 0 ≤ q j), q j)
  linarith [hY (univ.filter (fun j => 0 ≤ q j)), hY (univ.filter (fun j => ¬ 0 ≤ q j))]

/-- Few terms of a nonnegative family with bounded sum exceed a threshold `η`. -/
lemma card_filter_lt_le {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ j, 0 ≤ w j) {η C : ℝ}
    (hη : 0 < η) (hC : ∑ j, w j ≤ C) :
    ((univ.filter fun j => η < w j).card : ℝ) ≤ C / η := by
  rw [le_div_iff₀ hη]
  calc ((univ.filter fun j => η < w j).card : ℝ) * η
        = ∑ j ∈ univ.filter (fun j => η < w j), η := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ univ.filter (fun j => η < w j), w j :=
        Finset.sum_le_sum fun j hj => (Finset.mem_filter.1 hj).2.le
    _ ≤ ∑ j, w j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j _ _ => hw j
    _ ≤ C := hC

/-- Scaling a point of the disc by `c ∈ [0, 1]` gains the slack factor `c`. -/
lemma disc_scale {b δ c X Y : ℝ} (hδ0 : 0 ≤ δ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hF : δ * X ^ 2 + Y ^ 2 + 2 * b * X ≤ 1 + b) :
    δ * (c * X) ^ 2 + (c * Y) ^ 2 + 2 * b * (c * X) ≤ c * (1 + b) := by
  have e : δ * (c * X) ^ 2 + (c * Y) ^ 2 + 2 * b * (c * X) =
      c * (δ * X ^ 2 + Y ^ 2 + 2 * b * X) - c * (1 - c) * (δ * X ^ 2 + Y ^ 2) := by ring
  have h1 : 0 ≤ c * (1 - c) * (δ * X ^ 2 + Y ^ 2) :=
    mul_nonneg (mul_nonneg hc0 (by linarith)) (by positivity)
  have h2 : c * (δ * X ^ 2 + Y ^ 2 + 2 * b * X) ≤ c * (1 + b) := mul_le_mul_of_nonneg_left hF hc0
  rw [e]
  linarith

/-- **Counting good flips.** Let `0 ≤ b ≤ 1` and let `d j` be pair differences with
nonnegative real parts, total real part at most `1 - b`, and the hereditary property
`‖b + ∑_{j ∈ D} d j‖ ≤ 1` for every `D`. Then for `0 < ρ < 1/2` at least
`(1/2) (1 - ρ)^{-(m - K)}` sets `Q` of pairs satisfy `‖b + 2 ∑_{j ∈ Q} d j‖ ≤ 1`, where
`K = ⌊1152 / (1 - 2ρ)²⌋`. -/
theorem many_good_flips {m : ℕ} {b ρ : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1 / 2) (d : Fin m → ℂ) (hre : ∀ j, 0 ≤ (d j).re)
    (hsum : ∑ j, (d j).re ≤ 1 - b)
    (hdisc : ∀ D : Finset (Fin m), ‖(b : ℂ) + ∑ j ∈ D, d j‖ ≤ 1) :
    (1 / 2 : ℝ) * (1 - ρ)⁻¹ ^ (m - ⌊(1152 : ℝ) / (1 - 2 * ρ) ^ 2⌋₊) ≤
      ((univ.filter fun Q : Finset (Fin m) => ‖(b : ℂ) + 2 * ∑ j ∈ Q, d j‖ ≤ 1).card : ℝ) := by
  have hinv1 : 1 ≤ (1 - ρ)⁻¹ := (one_le_inv₀ (by linarith)).2 (by linarith)
  rcases eq_or_lt_of_le hb1 with hb | hb
  · -- `b = 1`: every `d j` vanishes and every `Q` is good.
    subst hb
    have hre0 : ∀ j, (d j).re = 0 := by
      have h0 : ∑ j, (d j).re = 0 :=
        le_antisymm (by linarith) (Finset.sum_nonneg fun j _ => hre j)
      intro j
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hre j)).1 h0 j (Finset.mem_univ j)
    have hd0 : ∀ j, d j = 0 := by
      intro j
      have h := hdisc {j}
      rw [Finset.sum_singleton, ← sq_le_one_iff₀ (norm_nonneg _), Complex.sq_norm,
        Complex.normSq_apply] at h
      simp [hre0 j] at h
      have him : (d j).im = 0 := by nlinarith [sq_nonneg (d j).im]
      exact Complex.ext (hre0 j) him
    have hall : (univ.filter fun Q : Finset (Fin m) =>
        ‖((1 : ℝ) : ℂ) + 2 * ∑ j ∈ Q, d j‖ ≤ 1) = univ := by
      apply Finset.filter_true_of_mem
      intro Q _
      simp [hd0]
    rw [hall, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
    have h2 : (1 - ρ)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    push_cast
    calc (1 / 2 : ℝ) * (1 - ρ)⁻¹ ^ (m - ⌊(1152 : ℝ) / (1 - 2 * ρ) ^ 2⌋₊)
        ≤ (1 - ρ)⁻¹ ^ (m - ⌊(1152 : ℝ) / (1 - 2 * ρ) ^ 2⌋₊) := by
          have := pow_nonneg (zero_le_one.trans hinv1) (m - ⌊(1152 : ℝ) / (1 - 2 * ρ) ^ 2⌋₊)
          linarith
      _ ≤ (1 - ρ)⁻¹ ^ m := pow_le_pow_right₀ hinv1 (Nat.sub_le _ _)
      _ ≤ 2 ^ m := pow_le_pow_left₀ (zero_le_one.trans hinv1) h2 m
  · -- `b < 1`: pass to normalized coordinates.
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 - b := ⟨_, rfl⟩
    have hδ0 : 0 < δ := by linarith
    have hbδ : b + δ = 1 := by linarith
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt δ := ⟨_, rfl⟩
    have hs2 : s ^ 2 = δ := hs ▸ Real.sq_sqrt hδ0.le
    obtain ⟨g, hg⟩ : ∃ g : ℝ, g = 1 - 2 * ρ := ⟨_, rfl⟩
    have hg0 : 0 < g := by linarith
    have hg1 : g ≤ 1 := by linarith
    obtain ⟨p, hp⟩ : ∃ p : Fin m → ℝ, ∀ j, p j = (d j).re / δ := ⟨_, fun _ => rfl⟩
    obtain ⟨q, hq⟩ : ∃ q : Fin m → ℝ, ∀ j, q j = (d j).im / s := ⟨_, fun _ => rfl⟩
    have hs0 : 0 < s := hs ▸ Real.sqrt_pos.2 hδ0
    have hp0 : ∀ j, 0 ≤ p j := fun j => (hp j).symm ▸ div_nonneg (hre j) hδ0.le
    have hre_sum : ∀ D : Finset (Fin m), (∑ j ∈ D, d j).re = δ * ∑ j ∈ D, p j := by
      intro D
      rw [Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hp j]
      field_simp
    have him_sum : ∀ D : Finset (Fin m), (∑ j ∈ D, d j).im = s * ∑ j ∈ D, q j := by
      intro D
      rw [Complex.im_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hq j]
      field_simp
    have hF : ∀ D : Finset (Fin m),
        δ * (∑ j ∈ D, p j) ^ 2 + (∑ j ∈ D, q j) ^ 2 + 2 * b * ∑ j ∈ D, p j ≤ 1 + b :=
      fun D => (norm_ofReal_add_le_one_iff hδ0 hbδ hs2 (hre_sum D) (him_sum D)).1 (hdisc D)
    have hgood : ∀ Q : Finset (Fin m),
        δ * (2 * ∑ j ∈ Q, p j) ^ 2 + (2 * ∑ j ∈ Q, q j) ^ 2 + 2 * b * (2 * ∑ j ∈ Q, p j) ≤
          1 + b → ‖(b : ℂ) + 2 * ∑ j ∈ Q, d j‖ ≤ 1 := by
      intro Q h
      refine (norm_ofReal_add_le_one_iff hδ0 hbδ hs2 ?_ ?_).2 h
      · rw [Complex.mul_re, hre_sum Q]
        simp
        ring
      · rw [Complex.mul_im, him_sum Q]
        simp
        ring
    -- Lemma 5: the total normalized length is at most `4`.
    have hpsum : ∑ j, p j ≤ 1 := by
      have h := hre_sum univ
      rw [Complex.re_sum] at h
      have h2 : δ * ∑ j, p j ≤ δ * 1 := by rw [← h, mul_one]; linarith
      exact le_of_mul_le_mul_left h2 hδ0
    have hqsum : ∑ j, |q j| ≤ 3 := sum_abs_le_three hb0 hb1 hδ0.le p q hp0 hF
    have hpq : ∑ j, (p j + |q j|) ≤ 4 := by rw [Finset.sum_add_distrib]; linarith
    have hpq0 : ∀ j, 0 ≤ p j + |q j| := fun j => add_nonneg (hp0 j) (abs_nonneg _)
    -- Heavy pairs: at most `K` of them.
    obtain ⟨η, hη⟩ : ∃ η : ℝ, η = g ^ 2 / 288 := ⟨_, rfl⟩
    have hη0 : 0 < η := by rw [hη]; positivity
    have hH : ((univ.filter fun j => η < p j + |q j|).card : ℝ) ≤ 1152 / g ^ 2 := by
      have h := card_filter_lt_le (fun j => p j + |q j|) hpq0 hη0 hpq
      have e : (4 : ℝ) / η = 1152 / g ^ 2 := by rw [hη]; field_simp; ring
      rw [← e]
      exact h
    have hHK : (univ.filter fun j => η < p j + |q j|).card ≤ ⌊(1152 : ℝ) / g ^ 2⌋₊ :=
      Nat.le_floor hH
    -- Light pairs: at least `m - K` of them.
    obtain ⟨L, hL⟩ : ∃ L : Finset (Fin m), L = univ.filter fun j => ¬ η < p j + |q j| :=
      ⟨_, rfl⟩
    have hLH : (univ.filter fun j => η < p j + |q j|).card + L.card = m := by
      have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin m)))
        (fun j => η < p j + |q j|)
      rw [Finset.card_univ, Fintype.card_fin] at h
      rw [hL]
      exact h
    have hLcard : m - ⌊(1152 : ℝ) / g ^ 2⌋₊ ≤ L.card := by omega
    have hLle : ∀ j ∈ L, p j + |q j| ≤ η := by
      intro j hj
      rw [hL] at hj
      exact not_lt.1 (Finset.mem_filter.1 hj).2
    have hLsum : ∑ j ∈ L, (p j + |q j|) ≤ 4 :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun j _ _ => hpq0 j) hpq
    -- Lemma 8: second moment and Markov.
    have hvar := sum_flipWeight_mul_dev_le hρ0.le (by linarith) hη0.le L p q hp0 hLle hLsum
    have ht : 0 < (g / 12) ^ 2 := by positivity
    have hmarkov := half_le_sum_flipWeight_filter hρ0.le (by linarith) ht L
      (fun Q => (∑ j ∈ Q, p j - ρ * ∑ j ∈ L, p j) ^ 2 + (∑ j ∈ Q, q j - ρ * ∑ j ∈ L, q j) ^ 2)
      (fun Q => by positivity) (by rw [show (g / 12) ^ 2 / 2 = η by rw [hη]; ring]; exact hvar)
    have hcount :=
      le_card_of_half_le_sum_flipWeight hρ0.le hρ1.le (Finset.filter_subset _ _) hmarkov
    -- The mean has slack `g`.
    have hmean : δ * (2 * ρ * ∑ j ∈ L, p j) ^ 2 + (2 * ρ * ∑ j ∈ L, q j) ^ 2 +
        2 * b * (2 * ρ * ∑ j ∈ L, p j) ≤ (1 - g) * (1 + b) := by
      have h := disc_scale hδ0.le (c := 2 * ρ) (by linarith) (by linarith) (hF L)
      rw [show 1 - g = 2 * ρ by rw [hg]; ring]
      exact h
    -- Subsets close to the mean are good (Lemma 7).
    have hsub : L.powerset.filter (fun Q => (∑ j ∈ Q, p j - ρ * ∑ j ∈ L, p j) ^ 2 +
          (∑ j ∈ Q, q j - ρ * ∑ j ∈ L, q j) ^ 2 ≤ (g / 12) ^ 2) ⊆
        univ.filter fun Q : Finset (Fin m) => ‖(b : ℂ) + 2 * ∑ j ∈ Q, d j‖ ≤ 1 := by
      intro Q hQ
      have hdev := (Finset.mem_filter.1 hQ).2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hgood Q ?_⟩
      refine disc_stability hb0 hδ0 hbδ hg0 hg1 ?_ hmean ?_
      · exact mul_nonneg (by linarith) (Finset.sum_nonneg fun j _ => hp0 j)
      · calc (2 * ∑ j ∈ Q, p j - 2 * ρ * ∑ j ∈ L, p j) ^ 2 +
              (2 * ∑ j ∈ Q, q j - 2 * ρ * ∑ j ∈ L, q j) ^ 2
            = 4 * ((∑ j ∈ Q, p j - ρ * ∑ j ∈ L, p j) ^ 2 +
              (∑ j ∈ Q, q j - ρ * ∑ j ∈ L, q j) ^ 2) := by ring
          _ ≤ 4 * (g / 12) ^ 2 := by linarith
          _ = (g / 6) ^ 2 := by ring
    rw [← hg]
    calc (1 / 2 : ℝ) * (1 - ρ)⁻¹ ^ (m - ⌊(1152 : ℝ) / g ^ 2⌋₊)
        ≤ (1 / 2) * (1 - ρ)⁻¹ ^ L.card :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hinv1 hLcard) (by norm_num)
      _ ≤ _ := hcount
      _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

end ReverseLittlewoodOfford

import ReverseLittlewoodOfford.AlternatingSum

/-!
# Lemmas 3 and 4: pairs around the pivot and hereditary deletion

In normal form, adjacent indices are paired around a pivot so that every pair difference has
horizontal coordinate of one sign. Deleting any collection of these disjoint adjacent pairs
keeps the pattern property of `AltPattern`, so Lemma 1 puts the weighted sum of the surviving
vectors in the closed unit disc. Flipping both signs of the pairs in `Q` moves the alternating
sum by `2 ∑_{j ∈ Q} d j`, and distinct `Q` give distinct sign vectors.
-/

set_option autoImplicit false

namespace ReverseLittlewoodOfford

open Real Finset

/-- A family on `Fin n` as a sequence on `ℕ` (extended by `0`). -/
noncomputable def seqOf {n : ℕ} (θ : Fin n → ℝ) (k : ℕ) : ℝ :=
  if h : k < n then θ ⟨k, h⟩ else 0

theorem seqOf_val {n : ℕ} (θ : Fin n → ℝ) (i : Fin n) : seqOf θ i = θ i := by
  simp [seqOf]

theorem seqOf_mono {n : ℕ} {θ : Fin n → ℝ} (hθ : Monotone θ) :
    ∀ i j, i ≤ j → j < n → seqOf θ i ≤ seqOf θ j := by
  intro i j hij hj
  have hi : i < n := lt_of_le_of_lt hij hj
  simp only [seqOf, dif_pos hi, dif_pos hj]
  exact hθ (Fin.mk_le_mk.2 hij)

theorem seqOf_range {n : ℕ} {θ : Fin n → ℝ} (hrange : ∀ i, θ i ∈ Set.Icc (-(π / 2)) (π / 2)) :
    ∀ k < n, seqOf θ k ∈ Set.Icc (-(π / 2)) (π / 2) := by
  intro k hk
  simp only [seqOf, dif_pos hk]
  exact hrange _

/-- Cosines of angles sorted in `[-π/2, π/2]` form a unimodal sequence. -/
theorem cos_seqOf_unimodal {n : ℕ} {θ : Fin n → ℝ} (hθ : Monotone θ)
    (hrange : ∀ i, θ i ∈ Set.Icc (-(π / 2)) (π / 2)) :
    ∀ i j k, i ≤ j → j ≤ k → k < n →
      min (Real.cos (seqOf θ i)) (Real.cos (seqOf θ k)) ≤ Real.cos (seqOf θ j) := by
  intro i j k hij hjk hk
  have hj : j < n := lt_of_le_of_lt hjk hk
  have hi : i < n := lt_of_le_of_lt hij hj
  have h1 := seqOf_mono hθ i j hij hj
  have h2 := seqOf_mono hθ j k hjk hk
  have ri := seqOf_range hrange i hi
  have rk := seqOf_range hrange k hk
  rcases le_or_gt 0 (seqOf θ j) with h0 | h0
  · exact (min_le_right _ _).trans
      (Real.cos_le_cos_of_nonneg_of_le_pi h0 (by linarith [rk.2, Real.pi_pos]) h2)
  · refine (min_le_left _ _).trans ?_
    rw [← Real.cos_neg (seqOf θ i), ← Real.cos_neg (seqOf θ j)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [ri.1, Real.pi_pos])
      (by linarith)

/-- Membership in one of the pairs `{a j, a j + 1}` with `j ∈ D`. -/
def InPairs {m : ℕ} (a : ℕ → ℕ) (D : Finset (Fin m)) (k : ℕ) : Prop :=
  ∃ j ∈ D, k = a j ∨ k = a j + 1

instance {m : ℕ} (a : ℕ → ℕ) (D : Finset (Fin m)) (k : ℕ) : Decidable (InPairs a D k) := by
  unfold InPairs
  infer_instance

/-- The alternating pattern with the pairs in `D` deleted. -/
noncomputable def deletePattern {m : ℕ} (a : ℕ → ℕ) (D : Finset (Fin m)) (k : ℕ) : ℝ :=
  if InPairs a D k then 0 else (-1) ^ k

/-- The alternating signs with both signs of every pair in `Q` changed. -/
noncomputable def flipPattern {m : ℕ} (a : ℕ → ℕ) (Q : Finset (Fin m)) (k : ℕ) : ℝ :=
  if InPairs a Q k then -(-1) ^ k else (-1) ^ k

theorem inPairs_insert {m : ℕ} (a : ℕ → ℕ) (D : Finset (Fin m)) (j : Fin m) (k : ℕ) :
    InPairs a (insert j D) k ↔ (k = a j ∨ k = a j + 1) ∨ InPairs a D k := by
  unfold InPairs
  simp only [Finset.mem_insert, exists_eq_or_imp]

theorem not_inPairs_of_not_mem {m : ℕ} {a : ℕ → ℕ}
    (hsep : ∀ j j' : Fin m, j < j' → a j + 1 < a j') {D : Finset (Fin m)} {j : Fin m}
    (hj : j ∉ D) {k : ℕ} (hk : k = a j ∨ k = a j + 1) : ¬ InPairs a D k := by
  rintro ⟨j', hj', hk'⟩
  have hne : j ≠ j' := fun h => hj (h ▸ hj')
  rcases lt_or_gt_of_ne hne with h | h
  · have := hsep j j' h
    omega
  · have := hsep j' j h
    omega

theorem mem_iff_inPairs {m : ℕ} {a : ℕ → ℕ} (hsep : ∀ j j' : Fin m, j < j' → a j + 1 < a j')
    (D : Finset (Fin m)) (j : Fin m) : j ∈ D ↔ InPairs a D (a j) := by
  constructor
  · intro hj
    exact ⟨j, hj, Or.inl rfl⟩
  · intro h
    by_contra hj
    exact not_inPairs_of_not_mem hsep hj (Or.inl rfl) h

/-- Changing the summand at `a` and `a + 1` only. -/
theorem sum_range_ite_pair (f g : ℕ → ℂ) {n a : ℕ} (ha : a + 1 < n) :
    ∑ k ∈ range n, (if k = a ∨ k = a + 1 then g k else f k) =
      ∑ k ∈ range n, f k + (g a - f a) + (g (a + 1) - f (a + 1)) := by
  have h1 : ∀ k, (if k = a ∨ k = a + 1 then g k else f k) =
      f k + (if k = a then g k - f k else 0) + (if k = a + 1 then g k - f k else 0) := by
    intro k
    by_cases h : k = a
    · subst h
      simp
    · by_cases h' : k = a + 1
      · subst h'
        simp
      · simp [h, h']
  simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
  rw [if_pos (by omega), if_pos ha]

/-- The vectors of the family as a sequence. -/
noncomputable def vec {n : ℕ} (θ : Fin n → ℝ) (k : ℕ) : ℂ :=
  Complex.exp (seqOf θ k * Complex.I)

/-- The alternating sum `∑ (-1)^k v_k`. -/
noncomputable def altSum {n : ℕ} (θ : Fin n → ℝ) : ℂ :=
  ∑ k ∈ range n, (-1 : ℂ) ^ k * vec θ k

/-- The pair difference: deleting pair `j` adds it, flipping pair `j` adds it twice. -/
noncomputable def pairDiff {n m : ℕ} (θ : Fin n → ℝ) (a : ℕ → ℕ) (j : Fin m) : ℂ :=
  (-1 : ℂ) ^ (a j) * (vec θ (a j + 1) - vec θ (a j))

section PairStructure

variable {n m : ℕ} {a : ℕ → ℕ}

theorem deletePattern_insert (D : Finset (Fin m)) (j : Fin m) (k : ℕ) :
    deletePattern a (insert j D) k =
      if k = a j ∨ k = a j + 1 then 0 else deletePattern a D k := by
  unfold deletePattern
  by_cases hk : k = a j ∨ k = a j + 1
  · rw [if_pos ((inPairs_insert a D j k).2 (Or.inl hk)), if_pos hk]
  · rw [if_neg hk]
    simp only [inPairs_insert, hk, false_or]

theorem flipPattern_insert (Q : Finset (Fin m)) (j : Fin m) (k : ℕ) :
    flipPattern a (insert j Q) k =
      if k = a j ∨ k = a j + 1 then -(-1) ^ k else flipPattern a Q k := by
  unfold flipPattern
  by_cases hk : k = a j ∨ k = a j + 1
  · rw [if_pos ((inPairs_insert a Q j k).2 (Or.inl hk)), if_pos hk]
  · rw [if_neg hk]
    simp only [inPairs_insert, hk, false_or]

variable (hsep : ∀ j j' : Fin m, j < j' → a j + 1 < a j') (hlt : ∀ j : Fin m, a j + 1 < n)
include hsep

theorem deletePattern_pair {D : Finset (Fin m)} {j : Fin m} (hj : j ∉ D) {k : ℕ}
    (hk : k = a j ∨ k = a j + 1) : deletePattern a D k = (-1) ^ k := by
  unfold deletePattern
  rw [if_neg (not_inPairs_of_not_mem hsep hj hk)]

theorem flipPattern_pair {Q : Finset (Fin m)} {j : Fin m} (hj : j ∉ Q) {k : ℕ}
    (hk : k = a j ∨ k = a j + 1) : flipPattern a Q k = (-1) ^ k := by
  unfold flipPattern
  rw [if_neg (not_inPairs_of_not_mem hsep hj hk)]

include hlt

/-- Deleting the pairs in `D` adds `∑_{j ∈ D} d j` to the alternating sum. -/
theorem sum_deletePattern (θ : Fin n → ℝ) (D : Finset (Fin m)) :
    ∑ k ∈ range n, (deletePattern a D k : ℂ) * vec θ k =
      altSum θ + ∑ j ∈ D, pairDiff θ a j := by
  classical
  induction D using Finset.induction_on with
  | empty => simp [deletePattern, InPairs, altSum]
  | insert j D hj ih =>
    rw [Finset.sum_insert hj]
    have hrw : ∀ k, (deletePattern a (insert j D) k : ℂ) * vec θ k =
        if k = a j ∨ k = a j + 1 then 0 else (deletePattern a D k : ℂ) * vec θ k := by
      intro k
      rw [deletePattern_insert]
      split_ifs <;> simp
    simp only [hrw]
    rw [sum_range_ite_pair _ _ (hlt j), ih,
      deletePattern_pair hsep hj (Or.inl rfl), deletePattern_pair hsep hj (Or.inr rfl)]
    unfold pairDiff
    push_cast
    ring

/-- Flipping the pairs in `Q` adds `2 ∑_{j ∈ Q} d j` to the alternating sum. -/
theorem sum_flipPattern (θ : Fin n → ℝ) (Q : Finset (Fin m)) :
    ∑ k ∈ range n, (flipPattern a Q k : ℂ) * vec θ k =
      altSum θ + 2 * ∑ j ∈ Q, pairDiff θ a j := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp [flipPattern, InPairs, altSum]
  | insert j Q hj ih =>
    rw [Finset.sum_insert hj]
    have hrw : ∀ k, (flipPattern a (insert j Q) k : ℂ) * vec θ k =
        if k = a j ∨ k = a j + 1 then -(-1 : ℂ) ^ k * vec θ k
        else (flipPattern a Q k : ℂ) * vec θ k := by
      intro k
      rw [flipPattern_insert]
      split_ifs <;> push_cast <;> ring
    simp only [hrw]
    rw [sum_range_ite_pair _ _ (hlt j), ih,
      flipPattern_pair hsep hj (Or.inl rfl), flipPattern_pair hsep hj (Or.inr rfl)]
    unfold pairDiff
    push_cast
    ring

/-- Deleting pairs keeps the pattern property. -/
theorem altPattern_deletePattern (hn : Odd n) (D : Finset (Fin m)) :
    AltPattern (deletePattern a D) n := by
  classical
  induction D using Finset.induction_on with
  | empty =>
    have h : deletePattern a (∅ : Finset (Fin m)) = fun k => (-1 : ℝ) ^ k := by
      funext k
      simp [deletePattern, InPairs]
    rw [h]
    exact altPattern_neg_one_pow hn
  | insert j D hj ih =>
    have hfun : deletePattern a (insert j D) =
        fun k => if k = a j ∨ k = a j + 1 then 0 else deletePattern a D k := by
      funext k
      exact deletePattern_insert D j k
    rw [hfun]
    refine ih.delete_pair (hlt j) ?_
    rw [deletePattern_pair hsep hj (Or.inl rfl), deletePattern_pair hsep hj (Or.inr rfl),
      pow_succ]
    ring

end PairStructure

/-- The sign vector of a flip set: `true` stands for `+1`. -/
def flipBool {n m : ℕ} (a : ℕ → ℕ) (Q : Finset (Fin m)) (i : Fin n) : Bool :=
  decide (Even (i : ℕ)) != decide (InPairs a Q i)

theorem signedSum_flipBool {n m : ℕ} (a : ℕ → ℕ) (Q : Finset (Fin m)) (θ : Fin n → ℝ) :
    signedSum (fun i => Complex.exp (θ i * Complex.I)) (flipBool a Q) =
      ∑ k ∈ range n, (flipPattern a Q k : ℂ) * vec θ k := by
  unfold signedSum
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [vec, seqOf_val]
  unfold flipBool flipPattern
  rcases Nat.even_or_odd (i : ℕ) with he | ho
  · by_cases hp : InPairs a Q i <;> simp [he, hp, he.neg_one_pow]
  · have hne : ¬ Even (i : ℕ) := Nat.not_even_iff_odd.2 ho
    by_cases hp : InPairs a Q i <;> simp [hne, hp, ho.neg_one_pow]

section Counting

variable {n m : ℕ} {a : ℕ → ℕ}
variable (hsep : ∀ j j' : Fin m, j < j' → a j + 1 < a j') (hlt : ∀ j : Fin m, a j + 1 < n)
include hsep hlt

theorem flipBool_injective :
    Function.Injective (fun Q : Finset (Fin m) => (flipBool a Q : Fin n → Bool)) := by
  intro Q Q' h
  ext j
  have hj := congrFun h ⟨a j, by have := hlt j; omega⟩
  simp only [flipBool] at hj
  rw [mem_iff_inPairs hsep Q j, mem_iff_inPairs hsep Q' j]
  by_cases h1 : InPairs a Q (a j) <;> by_cases h2 : InPairs a Q' (a j) <;>
    simp_all

/-- Good flip sets inject into good sign vectors. -/
theorem card_good_flips_le (θ : Fin n → ℝ) :
    (univ.filter fun Q : Finset (Fin m) =>
        ‖altSum θ + 2 * ∑ j ∈ Q, pairDiff θ a j‖ ≤ 1).card ≤
      goodCount (fun i => Complex.exp (θ i * Complex.I)) 1 := by
  unfold goodCount
  refine Finset.card_le_card_of_injOn (fun Q => flipBool a Q) ?_
    (flipBool_injective hsep hlt).injOn
  intro Q hQ
  simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hQ ⊢
  change ‖altSum θ + 2 * ∑ j ∈ Q, pairDiff θ a j‖ ≤ 1 at hQ
  change ‖signedSum (fun i => Complex.exp (θ i * Complex.I)) (flipBool a Q)‖ ≤ 1
  rw [signedSum_flipBool, sum_flipPattern hsep hlt]
  exact hQ

/-- **Lemma 4 (hereditary deletion).** -/
theorem norm_altSum_add_le_one (hn : Odd n) {θ : Fin n → ℝ} (hθ : Monotone θ)
    (hrange : ∀ i, θ i ∈ Set.Icc (-(π / 2)) (π / 2)) (D : Finset (Fin m)) :
    ‖altSum θ + ∑ j ∈ D, pairDiff θ a j‖ ≤ 1 := by
  rw [← sum_deletePattern hsep hlt]
  exact norm_sum_le_one_of_altPattern n (seqOf θ) (deletePattern a D) (seqOf_mono hθ)
    (seqOf_range hrange) (altPattern_deletePattern hsep hlt hn D)

end Counting

theorem vec_re {n : ℕ} (θ : Fin n → ℝ) (k : ℕ) : (vec θ k).re = Real.cos (seqOf θ k) := by
  rw [vec, Complex.exp_ofReal_mul_I_re]

theorem pairDiff_re {n m : ℕ} (θ : Fin n → ℝ) (a : ℕ → ℕ) (j : Fin m) :
    (pairDiff θ a j).re =
      (-1) ^ (a j) * (Real.cos (seqOf θ (a j + 1)) - Real.cos (seqOf θ (a j))) := by
  rw [pairDiff, show ((-1 : ℂ) ^ (a j)) = (((-1 : ℝ) ^ (a j) : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul, Complex.sub_re, vec_re, vec_re]

theorem altSum_eq {n : ℕ} (θ : Fin n → ℝ) :
    altSum θ = ∑ i : Fin n, (-1 : ℂ) ^ (i : ℕ) * Complex.exp (θ i * Complex.I) := by
  rw [altSum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [vec, seqOf_val]

/-- Pair starts around an even pivot `p`: `(0,1), …, (p-2,p-1), (p+1,p+2), …`. -/
def evenPivotPairs (p j : ℕ) : ℕ :=
  if j < p / 2 then 2 * j else 2 * j + 1

/-- Pair starts around an odd pivot `p`: `(1,2), …, (p-2,p-1), (p+1,p+2), …`. -/
def oddPivotPairs (p j : ℕ) : ℕ :=
  if j < p / 2 then 2 * j + 1 else 2 * j + 2

theorem evenPivotPairs_lt {n p : ℕ} (hn2 : n % 2 = 1) (hpn : p < n) (hpe : p % 2 = 0)
    (j : Fin ((n - 1) / 2)) : evenPivotPairs p j + 1 < n := by
  have := j.isLt
  unfold evenPivotPairs
  split_ifs <;> omega

theorem evenPivotPairs_sep {n p : ℕ} (j j' : Fin ((n - 1) / 2)) (h : j < j') :
    evenPivotPairs p j + 1 < evenPivotPairs p j' := by
  have : (j : ℕ) < j' := h
  unfold evenPivotPairs
  split_ifs <;> omega

theorem oddPivotPairs_lt {n p : ℕ} (hn2 : n % 2 = 1) (hpn : p < n) (hpo : p % 2 = 1)
    (j : Fin ((n - 3) / 2)) : oddPivotPairs p j + 1 < n := by
  have := j.isLt
  unfold oddPivotPairs
  split_ifs <;> omega

theorem oddPivotPairs_sep {n p : ℕ} (j j' : Fin ((n - 3) / 2)) (h : j < j') :
    oddPivotPairs p j + 1 < oddPivotPairs p j' := by
  have : (j : ℕ) < j' := h
  unfold oddPivotPairs
  split_ifs <;> omega

/-- **Lemma 3, even pivot.** With `p` maximizing the horizontal coordinate over even indices,
every pair difference has nonnegative real part. -/
theorem pairDiff_re_nonneg_even {n : ℕ} {θ : Fin n → ℝ} (hθ : Monotone θ)
    (hrange : ∀ i, θ i ∈ Set.Icc (-(π / 2)) (π / 2)) {p : ℕ} (hpn : p < n) (hpe : p % 2 = 0)
    (hpmax : ∀ k, k < n → k % 2 = 0 → Real.cos (seqOf θ k) ≤ Real.cos (seqOf θ p))
    (hn2 : n % 2 = 1) (j : Fin ((n - 1) / 2)) :
    0 ≤ (pairDiff θ (evenPivotPairs p) j).re := by
  have huni := cos_seqOf_unimodal hθ hrange
  have hj := j.isLt
  rw [pairDiff_re]
  unfold evenPivotPairs
  split_ifs with hjt
  · rw [(even_two_mul (j : ℕ)).neg_one_pow, one_mul]
    have h1 := huni (2 * j) (2 * j + 1) p (by omega) (by omega) hpn
    have h2 := hpmax (2 * j) (by omega) (by omega)
    rw [min_eq_left h2] at h1
    linarith
  · rw [(odd_two_mul_add_one (j : ℕ)).neg_one_pow]
    have h1 := huni p (2 * j + 1) (2 * j + 1 + 1) (by omega) (by omega) (by omega)
    have h2 := hpmax (2 * j + 1 + 1) (by omega) (by omega)
    rw [min_eq_right h2] at h1
    linarith

/-- **Lemma 3, odd pivot.** With `p` maximizing the horizontal coordinate over odd indices,
every pair difference has nonpositive real part. -/
theorem pairDiff_re_nonpos_odd {n : ℕ} {θ : Fin n → ℝ} (hθ : Monotone θ)
    (hrange : ∀ i, θ i ∈ Set.Icc (-(π / 2)) (π / 2)) {p : ℕ} (hpn : p < n) (hpo : p % 2 = 1)
    (hpmax : ∀ k, k < n → k % 2 = 1 → Real.cos (seqOf θ k) ≤ Real.cos (seqOf θ p))
    (hn2 : n % 2 = 1) (j : Fin ((n - 3) / 2)) :
    (pairDiff θ (oddPivotPairs p) j).re ≤ 0 := by
  have huni := cos_seqOf_unimodal hθ hrange
  have hj := j.isLt
  rw [pairDiff_re]
  unfold oddPivotPairs
  split_ifs with hjt
  · rw [(odd_two_mul_add_one (j : ℕ)).neg_one_pow]
    have h1 := huni (2 * j + 1) (2 * j + 1 + 1) p (by omega) (by omega) hpn
    have h2 := hpmax (2 * j + 1) (by omega) (by omega)
    rw [min_eq_left h2] at h1
    linarith
  · have hev : (-1 : ℝ) ^ (2 * (j : ℕ) + 2) = 1 := by
      rw [pow_add, pow_mul]
      norm_num
    rw [hev, one_mul]
    have h1 := huni p (2 * j + 2) (2 * j + 2 + 1) (by omega) (by omega) (by omega)
    have h2 := hpmax (2 * j + 2 + 1) (by omega) (by omega)
    rw [min_eq_right h2] at h1
    linarith

section Packaging

variable {n m : ℕ} (hn : Odd n) {θ : Fin n → ℝ} (hθ : Monotone θ)
  (hrange : ∀ i, θ i ∈ Set.Icc (-(π / 2)) (π / 2)) {a : ℕ → ℕ}
  (hsep : ∀ j j' : Fin m, j < j' → a j + 1 < a j') (hlt : ∀ j : Fin m, a j + 1 < n)
  {β : ℝ} (hUβ : altSum θ = β)
include hn hθ hrange hsep hlt hUβ

/-- The data for `many_good_flips` when the alternating sum is `β ≥ 0`. -/
theorem pair_data_of_nonneg (hβ : 0 ≤ β) (hre : ∀ j : Fin m, 0 ≤ (pairDiff θ a j).re) :
    0 ≤ β ∧ β ≤ 1 ∧ (∀ j : Fin m, 0 ≤ (pairDiff θ a j).re) ∧
      ∑ j : Fin m, (pairDiff θ a j).re ≤ 1 - β ∧
      (∀ D : Finset (Fin m), ‖(β : ℂ) + ∑ j ∈ D, pairDiff θ a j‖ ≤ 1) ∧
      (univ.filter fun Q : Finset (Fin m) =>
          ‖(β : ℂ) + 2 * ∑ j ∈ Q, pairDiff θ a j‖ ≤ 1).card ≤
        goodCount (fun i => Complex.exp (θ i * Complex.I)) 1 := by
  have hered := norm_altSum_add_le_one hsep hlt hn hθ hrange
  rw [hUβ] at hered
  refine ⟨hβ, ?_, hre, ?_, hered, ?_⟩
  · have h := hered ∅
    rw [Finset.sum_empty, add_zero, Complex.norm_real, Real.norm_eq_abs] at h
    exact (le_abs_self β).trans h
  · have h := (Complex.re_le_norm _).trans (hered univ)
    rw [Complex.add_re, Complex.ofReal_re, Complex.re_sum] at h
    linarith
  · have h := card_good_flips_le hsep hlt θ
    rwa [hUβ] at h

/-- The data for `many_good_flips` when the alternating sum is `β ≤ 0`: reflect by
`z ↦ -conj z`. -/
theorem pair_data_of_nonpos (hβ : β ≤ 0) (hre : ∀ j : Fin m, (pairDiff θ a j).re ≤ 0) :
    0 ≤ -β ∧ -β ≤ 1 ∧ (∀ j : Fin m, 0 ≤ (-(starRingEnd ℂ) (pairDiff θ a j)).re) ∧
      ∑ j : Fin m, (-(starRingEnd ℂ) (pairDiff θ a j)).re ≤ 1 - -β ∧
      (∀ D : Finset (Fin m),
        ‖((-β : ℝ) : ℂ) + ∑ j ∈ D, -(starRingEnd ℂ) (pairDiff θ a j)‖ ≤ 1) ∧
      (univ.filter fun Q : Finset (Fin m) =>
          ‖((-β : ℝ) : ℂ) + 2 * ∑ j ∈ Q, -(starRingEnd ℂ) (pairDiff θ a j)‖ ≤ 1).card ≤
        goodCount (fun i => Complex.exp (θ i * Complex.I)) 1 := by
  have hered := norm_altSum_add_le_one hsep hlt hn hθ hrange
  rw [hUβ] at hered
  have hconj1 : ∀ D : Finset (Fin m),
      ((-β : ℝ) : ℂ) + ∑ j ∈ D, -(starRingEnd ℂ) (pairDiff θ a j) =
        -(starRingEnd ℂ) ((β : ℂ) + ∑ j ∈ D, pairDiff θ a j) := by
    intro D
    rw [Finset.sum_neg_distrib, map_add, map_sum, Complex.conj_ofReal]
    push_cast
    ring
  have hconj2 : ∀ Q : Finset (Fin m),
      ((-β : ℝ) : ℂ) + 2 * ∑ j ∈ Q, -(starRingEnd ℂ) (pairDiff θ a j) =
        -(starRingEnd ℂ) ((β : ℂ) + 2 * ∑ j ∈ Q, pairDiff θ a j) := by
    intro Q
    rw [Finset.sum_neg_distrib, map_add, map_mul, map_sum, Complex.conj_ofReal, map_ofNat]
    push_cast
    ring
  refine ⟨by linarith, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hered ∅
    rw [Finset.sum_empty, add_zero, Complex.norm_real, Real.norm_eq_abs] at h
    exact (neg_le_abs β).trans h
  · intro j
    rw [Complex.neg_re, Complex.conj_re]
    linarith [hre j]
  · have h := (Complex.abs_re_le_norm _).trans (hered univ)
    rw [abs_le, Complex.add_re, Complex.ofReal_re, Complex.re_sum] at h
    simp only [Complex.neg_re, Complex.conj_re, Finset.sum_neg_distrib]
    linarith [h.1]
  · intro D
    rw [hconj1, norm_neg, Complex.norm_conj]
    exact hered D
  · have h := card_good_flips_le hsep hlt θ
    rw [hUβ] at h
    refine le_trans (le_of_eq ?_) h
    congr 1
    ext Q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hconj2, norm_neg, Complex.norm_conj]

end Packaging

/-- **Lemmas 3 and 4 (pairs and hereditary deletion).** A family in normal form yields the
data used by `many_good_flips`: a real `b ∈ [0, 1]`, at least `(n - 3) / 2` pair differences
with nonnegative real parts and total real part at most `1 - b`, the hereditary property, and an
injection of good flip sets into good sign vectors. -/
theorem exists_pair_data {n : ℕ} (hn : Odd n) (θ : Fin n → ℝ) (hθ : Monotone θ)
    (hrange : ∀ i, θ i ∈ Set.Icc (-(π / 2)) (π / 2))
    (hreal : (∑ i : Fin n, (-1 : ℂ) ^ (i : ℕ) * Complex.exp (θ i * Complex.I)).im = 0) :
    ∃ (m : ℕ) (b : ℝ) (d : Fin m → ℂ), (n - 3) / 2 ≤ m ∧ 0 ≤ b ∧ b ≤ 1 ∧
      (∀ j, 0 ≤ (d j).re) ∧ ∑ j, (d j).re ≤ 1 - b ∧
      (∀ D : Finset (Fin m), ‖(b : ℂ) + ∑ j ∈ D, d j‖ ≤ 1) ∧
      (Finset.univ.filter fun Q : Finset (Fin m) =>
          ‖(b : ℂ) + 2 * ∑ j ∈ Q, d j‖ ≤ 1).card ≤
        goodCount (fun i => Complex.exp (θ i * Complex.I)) 1 := by
  classical
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  rw [← altSum_eq] at hreal
  set β := (altSum θ).re with hβdef
  have hUβ : altSum θ = (β : ℂ) := Complex.ext (by simp [hβdef]) (by simp [hreal])
  by_cases hβ : 0 ≤ β
  · obtain ⟨p, hp, hpmax⟩ := Finset.exists_max_image ((range n).filter fun k => k % 2 = 0)
      (fun k => Real.cos (seqOf θ k)) ⟨0, by simp [hn.pos]⟩
    simp only [Finset.mem_filter, Finset.mem_range] at hp hpmax
    refine ⟨(n - 1) / 2, β, pairDiff θ (evenPivotPairs p), by omega, ?_⟩
    exact pair_data_of_nonneg hn hθ hrange (evenPivotPairs_sep (p := p))
      (evenPivotPairs_lt hn2 hp.1 hp.2) hUβ hβ
      (pairDiff_re_nonneg_even hθ hrange hp.1 hp.2 (fun k hk hk2 => hpmax k ⟨hk, hk2⟩) hn2)
  · rw [not_le] at hβ
    have hn3 : 3 ≤ n := by
      by_contra h3
      have hn1 : n = 1 := by omega
      subst hn1
      have : 0 ≤ β := by
        rw [hβdef, altSum, Finset.sum_range_one, pow_zero, one_mul, vec_re]
        exact Real.cos_nonneg_of_mem_Icc (seqOf_range hrange 0 (by norm_num))
      linarith
    obtain ⟨p, hp, hpmax⟩ := Finset.exists_max_image ((range n).filter fun k => k % 2 = 1)
      (fun k => Real.cos (seqOf θ k)) ⟨1, by simp; omega⟩
    simp only [Finset.mem_filter, Finset.mem_range] at hp hpmax
    exact ⟨(n - 3) / 2, -β, fun j => -(starRingEnd ℂ) (pairDiff θ (oddPivotPairs p) j), le_rfl,
      pair_data_of_nonpos hn hθ hrange (oddPivotPairs_sep (p := p))
        (oddPivotPairs_lt hn2 hp.1 hp.2) hUβ hβ.le
        (pairDiff_re_nonpos_odd hθ hrange hp.1 hp.2 (fun k hk hk2 => hpmax k ⟨hk, hk2⟩) hn2)⟩

end ReverseLittlewoodOfford

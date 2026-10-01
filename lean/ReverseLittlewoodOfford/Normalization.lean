import ReverseLittlewoodOfford.Defs

/-!
# Lemma 2: normal form

Changing the sign of single vectors, reordering them and rotating all of them do not change
the number of good sign vectors. Using these moves, every odd family of unit vectors becomes
angle-sorted in the right half-plane with a real alternating sum: replace each vector by the
one of `± v` in the right half-plane, sort by angle, and move the cut of the half-plane so
that it is centred on the line of the alternating sum.
-/

set_option autoImplicit false

namespace ReverseLittlewoodOfford

open Real

/-- Two families have the same number of good sign vectors when a bijection of the sign
vectors preserves the norm of the signed sum. -/
private theorem goodCount_eq_of_equiv {n : ℕ} (v w : Fin n → ℂ)
    (f : (Fin n → Bool) ≃ (Fin n → Bool)) (h : ∀ ε, ‖signedSum v ε‖ = ‖signedSum w (f ε)‖)
    (r : ℝ) :
    goodCount v r = goodCount w r := by
  unfold goodCount
  exact Finset.card_equiv f (fun ε => by simp [h])

/-- Reindexing the vectors amounts to reindexing the sign vector. -/
private theorem signedSum_comp_equiv {n : ℕ} (v : Fin n → ℂ) (e : Fin n ≃ Fin n)
    (ε : Fin n → Bool) :
    signedSum (fun i => v (e i)) ε = signedSum v (fun i => ε (e.symm i)) := by
  unfold signedSum
  rw [← Equiv.sum_comp e (fun i => if ε (e.symm i) then v i else -v i)]
  simp

/-- A common factor comes out of the signed sum. -/
private theorem signedSum_const_mul {n : ℕ} (v : Fin n → ℂ) (c : ℂ) (ε : Fin n → Bool) :
    signedSum (fun i => c * v i) ε = c * signedSum v ε := by
  unfold signedSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> ring

/-- Reordering the vectors does not change the number of good sign vectors. -/
theorem goodCount_comp_equiv {n : ℕ} (v : Fin n → ℂ) (e : Fin n ≃ Fin n) (r : ℝ) :
    goodCount (fun i => v (e i)) r = goodCount v r := by
  refine goodCount_eq_of_equiv _ _ (e.arrowCongr (Equiv.refl Bool)) (fun ε => ?_) r
  rw [signedSum_comp_equiv]
  rfl

/-- Changing the signs of single vectors does not change the number of good sign vectors. -/
theorem goodCount_mul_sign {n : ℕ} (v σ : Fin n → ℂ) (hσ : ∀ i, σ i = 1 ∨ σ i = -1)
    (r : ℝ) :
    goodCount (fun i => σ i * v i) r = goodCount v r := by
  classical
  let b : Fin n → Bool := fun i => decide (σ i = 1)
  let f : (Fin n → Bool) ≃ (Fin n → Bool) :=
    { toFun := fun ε i => if b i then ε i else !ε i
      invFun := fun ε i => if b i then ε i else !ε i
      left_inv := fun ε => by funext i; by_cases h : b i <;> simp [h]
      right_inv := fun ε => by funext i; by_cases h : b i <;> simp [h] }
  refine goodCount_eq_of_equiv _ _ f (fun ε => ?_) r
  congr 1
  unfold signedSum
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rcases hσ i with h | h
  · simp [f, b, h]
  · have h1 : (-1 : ℂ) ≠ 1 := by norm_num
    cases hε : ε i <;> simp [f, b, h, h1, hε]

/-- A common rotation does not change the number of good sign vectors. -/
theorem goodCount_mul_unit {n : ℕ} (v : Fin n → ℂ) {c : ℂ} (hc : ‖c‖ = 1) (r : ℝ) :
    goodCount (fun i => c * v i) r = goodCount v r := by
  refine goodCount_eq_of_equiv _ _ (Equiv.refl _) (fun ε => ?_) r
  simp [signedSum_const_mul, hc]

/-- Replacing each unit vector by the one of `± v i` in the closed right half-plane gives
angles in `[-π/2, π/2]` and keeps the number of good sign vectors. -/
private theorem exists_right_half_angles {n : ℕ} (v : Fin n → ℂ) (hv : ∀ i, ‖v i‖ = 1) :
    ∃ θ : Fin n → ℝ, (∀ i, θ i ∈ Set.Icc (-(π / 2)) (π / 2)) ∧
      ∀ r : ℝ, goodCount (fun i => Complex.exp (θ i * Complex.I)) r = goodCount v r := by
  classical
  let σ : Fin n → ℂ := fun i => if 0 ≤ (v i).re then 1 else -1
  have hσ : ∀ i, σ i = 1 ∨ σ i = -1 := fun i => by
    by_cases h : 0 ≤ (v i).re <;> simp [σ, h]
  let w : Fin n → ℂ := fun i => σ i * v i
  have hw_re : ∀ i, 0 ≤ (w i).re := fun i => by
    by_cases h : 0 ≤ (v i).re
    · simp [w, σ, h]
    · simp [w, σ, h]
      linarith
  have hw_norm : ∀ i, ‖w i‖ = 1 := fun i => by
    rcases hσ i with h | h <;> simp [w, h, hv i]
  refine ⟨fun i => Complex.arg (w i), fun i => ?_, fun r => ?_⟩
  · exact abs_le.mp (Complex.abs_arg_le_pi_div_two_iff.mpr (hw_re i))
  · have hexp : (fun i => Complex.exp (Complex.arg (w i) * Complex.I)) = w := by
      funext i
      have := Complex.norm_mul_exp_arg_mul_I (w i)
      rw [hw_norm i] at this
      simpa using this
    rw [hexp]
    exact goodCount_mul_sign v σ hσ r

/-- Sorting the angles does not change the number of good sign vectors. -/
private theorem exists_sorted_angles {n : ℕ} (θ₀ : Fin n → ℝ)
    (hθ₀ : ∀ i, θ₀ i ∈ Set.Icc (-(π / 2)) (π / 2)) :
    ∃ θ : Fin n → ℝ, Monotone θ ∧ (∀ i, θ i ∈ Set.Icc (-(π / 2)) (π / 2)) ∧
      ∀ r : ℝ, goodCount (fun i => Complex.exp (θ i * Complex.I)) r =
        goodCount (fun i => Complex.exp (θ₀ i * Complex.I)) r := by
  refine ⟨θ₀ ∘ Tuple.sort θ₀, Tuple.monotone_sort θ₀, fun i => hθ₀ _, fun r => ?_⟩
  exact goodCount_comp_equiv (fun i => Complex.exp (θ₀ i * Complex.I)) (Tuple.sort θ₀) r

/-- Polar form with the angle in `[0, π]` and a real (possibly negative) radius. -/
private theorem exists_polar_Icc (U : ℂ) :
    ∃ ψ ∈ Set.Icc (0 : ℝ) π, ∃ R : ℝ, U = R * Complex.exp (ψ * Complex.I) := by
  by_cases h : 0 ≤ Complex.arg U
  · exact ⟨Complex.arg U, ⟨h, Complex.arg_le_pi U⟩, ‖U‖,
      (Complex.norm_mul_exp_arg_mul_I U).symm⟩
  · rw [not_le] at h
    refine ⟨Complex.arg U + π, ⟨by linarith [Complex.neg_pi_lt_arg U], by linarith⟩, -‖U‖, ?_⟩
    have := Complex.norm_mul_exp_arg_mul_I U
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
    linear_combination -this

/-- A monotone family crosses a level once: below the cut index it is at most the level, from
the cut index on it is at least the level. -/
private theorem exists_monotone_cut {n : ℕ} (θ : Fin n → ℝ) (hθ : Monotone θ) (c : ℝ) :
    ∃ j ≤ n, (∀ i : Fin n, (i : ℕ) < j → θ i ≤ c) ∧ (∀ i : Fin n, j ≤ (i : ℕ) → c ≤ θ i) := by
  classical
  let P : ℕ → Prop := fun k => ∀ i : Fin n, k ≤ (i : ℕ) → c ≤ θ i
  have hPn : P n := fun i hi => absurd i.isLt (by omega)
  have hP : ∃ k, P k := ⟨n, hPn⟩
  refine ⟨Nat.find hP, Nat.find_min' hP hPn, ?_, Nat.find_spec hP⟩
  intro i hi
  have := Nat.find_min hP hi
  simp only [P, not_forall, not_le] at this
  obtain ⟨i', hii', hlt⟩ := this
  exact (hθ (Fin.le_iff_val_le_val.mpr hii')).trans hlt.le

/-- The cyclic shift `m ↦ m + j` modulo `n`, for `j ≤ n`. -/
private theorem exists_shift_equiv {n j : ℕ} (hjn : j ≤ n) :
    ∃ e : Fin n ≃ Fin n, ∀ m : Fin n,
      ((m : ℕ) < n - j → ((e m : Fin n) : ℕ) = m + j) ∧
      (n - j ≤ (m : ℕ) → ((e m : Fin n) : ℕ) + n = m + j) := by
  refine ⟨{ toFun := fun m => ⟨if (m : ℕ) + j < n then m + j else m + j - n, by
              have := m.isLt; split_ifs <;> omega⟩
            invFun := fun k => ⟨if j ≤ (k : ℕ) then k - j else k + n - j, by
              have := k.isLt; split_ifs <;> omega⟩
            left_inv := fun m => ?_, right_inv := fun k => ?_ }, fun m => ?_⟩
  · have hm := m.isLt
    apply Fin.ext
    dsimp only
    split_ifs <;> omega
  · have hk := k.isLt
    apply Fin.ext
    dsimp only
    split_ifs <;> omega
  · have hm := m.isLt
    dsimp only [Equiv.coe_fn_mk]
    split_ifs <;> constructor <;> intro <;> omega

/-- Powers of `-1` with exponents of the same parity agree. -/
private theorem neg_one_pow_eq_of_even_add {a b : ℕ} (h : Even (a + b)) :
    (-1 : ℂ) ^ a = (-1) ^ b := by
  rw [neg_one_pow_eq_pow_mod_two a, neg_one_pow_eq_pow_mod_two b]
  have := Nat.even_iff.mp h
  congr 1
  omega

/-- **Lemma 2 (normal form).** -/
theorem exists_normal_form {n : ℕ} (hn : Odd n) (v : Fin n → ℂ) (hv : ∀ i, ‖v i‖ = 1) :
    ∃ θ : Fin n → ℝ, Monotone θ ∧ (∀ i, θ i ∈ Set.Icc (-(π / 2)) (π / 2)) ∧
      (∑ i : Fin n, (-1 : ℂ) ^ (i : ℕ) * Complex.exp (θ i * Complex.I)).im = 0 ∧
      ∀ r : ℝ, goodCount (fun i => Complex.exp (θ i * Complex.I)) r = goodCount v r := by
  classical
  obtain ⟨θ₀, hθ₀, hcount₀⟩ := exists_right_half_angles v hv
  obtain ⟨θ, hmono, hθ, hcount₁⟩ := exists_sorted_angles θ₀ hθ₀
  obtain ⟨ψ, ⟨hψ0, hψπ⟩, R, hUR⟩ :=
    exists_polar_Icc (∑ i : Fin n, (-1 : ℂ) ^ (i : ℕ) * Complex.exp (θ i * Complex.I))
  obtain ⟨j, hjn, hlow, hhigh⟩ := exists_monotone_cut θ hmono (ψ - π / 2)
  obtain ⟨e, he⟩ := exists_shift_equiv hjn
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  let τ : Fin n → ℂ := fun m => if (m : ℕ) < n - j then 1 else -1
  let φ : Fin n → ℝ := fun m => if (m : ℕ) < n - j then θ (e m) - ψ else θ (e m) + π - ψ
  have hexp : ∀ m, Complex.exp (φ m * Complex.I) =
      Complex.exp ((-ψ : ℝ) * Complex.I) * (τ m * Complex.exp (θ (e m) * Complex.I)) := by
    intro m
    by_cases hm : (m : ℕ) < n - j
    · simp only [φ, τ, if_pos hm, one_mul]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    · simp only [φ, τ, if_neg hm]
      rw [← Complex.exp_pi_mul_I, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
  have hθle : ∀ a b : Fin n, (a : ℕ) ≤ b → θ a ≤ θ b := fun a b h =>
    hmono (Fin.le_iff_val_le_val.mpr h)
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · -- `φ` is monotone
    intro a b hab
    have hab' : (a : ℕ) ≤ b := Fin.le_iff_val_le_val.mp hab
    have ha := he a
    have hb := he b
    have hθa := hθ (e a)
    have hθb := hθ (e b)
    simp only [Set.mem_Icc] at hθa hθb
    simp only [φ]
    by_cases ha' : (a : ℕ) < n - j <;> by_cases hb' : (b : ℕ) < n - j
    · rw [if_pos ha', if_pos hb']
      have := hθle (e a) (e b) (by rw [ha.1 ha', hb.1 hb']; omega)
      linarith
    · rw [if_pos ha', if_neg hb']
      linarith [pi_pos]
    · omega
    · rw [if_neg ha', if_neg hb']
      have := hθle (e a) (e b) (by have := ha.2 (by omega); have := hb.2 (by omega); omega)
      linarith
  · -- `φ` takes values in `[-π/2, π/2]`
    intro m
    have hm := he m
    have hθm := hθ (e m)
    simp only [Set.mem_Icc] at hθm ⊢
    simp only [φ]
    by_cases hm' : (m : ℕ) < n - j
    · rw [if_pos hm']
      have := hhigh (e m) (by rw [hm.1 hm']; omega)
      constructor <;> linarith
    · rw [if_neg hm']
      have := hlow (e m) (by have := hm.2 (by omega); have := m.isLt; omega)
      constructor <;> linarith
  · -- the alternating sum is real
    have hsign : ∀ m : Fin n,
        (-1 : ℂ) ^ (m : ℕ) * τ m = (-1) ^ j * (-1) ^ ((e m : Fin n) : ℕ) := by
      intro m
      by_cases hm : (m : ℕ) < n - j
      · simp only [τ, if_pos hm, mul_one]
        rw [← pow_add]
        apply neg_one_pow_eq_of_even_add
        rw [(he m).1 hm, Nat.even_iff]
        omega
      · simp only [τ, if_neg hm]
        rw [← pow_succ, ← pow_add]
        apply neg_one_pow_eq_of_even_add
        have := (he m).2 (by omega)
        rw [Nat.even_iff]
        omega
    have hsum : ∑ m : Fin n, (-1 : ℂ) ^ (m : ℕ) * Complex.exp (φ m * Complex.I) =
        Complex.exp ((-ψ : ℝ) * Complex.I) * ((-1) ^ j *
          ∑ i : Fin n, (-1 : ℂ) ^ (i : ℕ) * Complex.exp (θ i * Complex.I)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Fintype.sum_equiv e _ _ (fun m => ?_)
      rw [hexp m]
      calc (-1 : ℂ) ^ (m : ℕ) * (Complex.exp ((-ψ : ℝ) * Complex.I) *
            (τ m * Complex.exp (θ (e m) * Complex.I)))
          = Complex.exp ((-ψ : ℝ) * Complex.I) * (((-1 : ℂ) ^ (m : ℕ) * τ m) *
            Complex.exp (θ (e m) * Complex.I)) := by ring
        _ = _ := by rw [hsign m]; ring
    have h1 : Complex.exp ((-ψ : ℝ) * Complex.I) * Complex.exp (ψ * Complex.I) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_zero]
      congr 1
      push_cast
      ring
    have h2 : Complex.exp ((-ψ : ℝ) * Complex.I) * ((-1) ^ j * (R * Complex.exp (ψ * Complex.I)))
        = (((-1 : ℝ) ^ j * R : ℝ) : ℂ) := by
      push_cast at h1 ⊢
      linear_combination ((-1 : ℂ) ^ j * R) * h1
    rw [hsum, hUR, h2, Complex.ofReal_im]
  · -- the number of good sign vectors is unchanged
    intro r
    have hc : ‖Complex.exp ((-ψ : ℝ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have hτ : ∀ m, τ m = 1 ∨ τ m = -1 := fun m => by
      by_cases hm : (m : ℕ) < n - j
      · left
        simp only [τ, if_pos hm]
      · right
        simp only [τ, if_neg hm]
    rw [show (fun i => Complex.exp (φ i * Complex.I)) = fun i =>
        Complex.exp ((-ψ : ℝ) * Complex.I) * (τ i * Complex.exp (θ (e i) * Complex.I)) from
        funext hexp]
    rw [goodCount_mul_unit _ hc, goodCount_mul_sign _ τ hτ,
      goodCount_comp_equiv (fun i => Complex.exp (θ i * Complex.I)) e, hcount₁, hcount₀]

end ReverseLittlewoodOfford

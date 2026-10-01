import ReverseLittlewoodOfford.Rate

/-!
Component axiom audit. The final theorem is in `ReverseLittlewoodOffordFC.lean`.
Every component should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

-- Lemma 1
#print axioms ReverseLittlewoodOfford.abs_sum_mul_le_of_unimodal
#print axioms ReverseLittlewoodOfford.norm_sum_le_one_of_altPattern
#print axioms ReverseLittlewoodOfford.AltPattern.delete_pair
#print axioms ReverseLittlewoodOfford.alternating_sum_norm_le_one
-- Lemma 2
#print axioms ReverseLittlewoodOfford.goodCount_comp_equiv
#print axioms ReverseLittlewoodOfford.goodCount_mul_sign
#print axioms ReverseLittlewoodOfford.goodCount_mul_unit
#print axioms ReverseLittlewoodOfford.exists_normal_form
-- Lemmas 3 and 4
#print axioms ReverseLittlewoodOfford.norm_altSum_add_le_one
#print axioms ReverseLittlewoodOfford.card_good_flips_le
#print axioms ReverseLittlewoodOfford.exists_pair_data
-- Lemmas 5, 7 and 8
#print axioms ReverseLittlewoodOfford.sum_flipWeight
#print axioms ReverseLittlewoodOfford.sum_flipWeight_mul_sq
#print axioms ReverseLittlewoodOfford.flipWeight_le
#print axioms ReverseLittlewoodOfford.disc_stability
#print axioms ReverseLittlewoodOfford.many_good_flips
-- Lower bound (A)
#print axioms ReverseLittlewoodOfford.lower_bound_A
#print axioms ReverseLittlewoodOfford.minProb_lower_bound_A
-- Upper bound
#print axioms ReverseLittlewoodOfford.hollom_sorkin_construction
#print axioms ReverseLittlewoodOfford.minProb_le_hollom_sorkin
-- The limit
#print axioms ReverseLittlewoodOfford.tendsto_root_of_bounds
#print axioms ReverseLittlewoodOfford.minProb_ge_geometric
#print axioms ReverseLittlewoodOfford.rootSeq_tendsto

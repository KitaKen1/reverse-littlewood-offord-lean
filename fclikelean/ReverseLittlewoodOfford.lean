/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# The reverse Littlewood–Offord problem at radius one: the odd-$n$ exponential rate

For unit vectors $v_1, \dots, v_n \in \mathbb{R}^2$ and independent uniform signs
$\varepsilon_i \in \{-1, 1\}$, let $F_{2,1}(n)$ be the infimum of
$\mathbb{P}(\lVert \varepsilon_1 v_1 + \dots + \varepsilon_n v_n \rVert_2 \le 1)$.
Does $\lim_{n \to \infty,\ n \text{ odd}} F_{2,1}(n)^{1/n}$ exist, and if so, what is it?

*Reference:* [arxiv/2503.24202](https://arxiv.org/abs/2503.24202)
**Double-jump phase transition for the reverse Littlewood–Offord problem**
by *Lawrence Hollom, Julien Portier, Victor Souza*
-/

@[expose] public section

open Filter Topology

namespace Arxiv.«2503.24202»

/-- The problem stated after Question 7.1 of the source: what is
$\lim_{n \to \infty,\ n \text{ odd}} F_{2,1}(n)^{1/n}$? Planar vectors are complex numbers,
a sign vector is `ε : Fin n → Bool` with `true` for $+1$, and $n = 2k + 1$. -/
@[category research open, AMS 5 60]
theorem reverse_littlewood_offord_rate :
    Tendsto
      (fun k : ℕ =>
        (⨅ v : {v : Fin (2 * k + 1) → ℂ // ∀ i, ‖v i‖ = 1},
          ((Finset.univ.filter fun ε : Fin (2 * k + 1) → Bool =>
              ‖∑ i, (if ε i then v.1 i else -v.1 i)‖ ≤ 1).card : ℝ) / 2 ^ (2 * k + 1))
          ^ (1 / (2 * k + 1 : ℝ)))
      atTop (𝓝 (answer(sorry) : ℝ)) := by
  sorry

end Arxiv.«2503.24202»

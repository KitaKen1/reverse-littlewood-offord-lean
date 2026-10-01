# The reverse Littlewood–Offord problem at radius one in Lean

The problem is the following question of Hollom, Portier and Souza.

> **Question.** For odd $n$, let $F_{2,1}(n)$ be the infimum, over unit vectors
> $v_1,\dots,v_n\in\mathbb{R}^2$, of
> $\mathbb{P}(\lVert\varepsilon_1v_1+\dots+\varepsilon_nv_n\rVert_2\le1)$, where the signs
> $\varepsilon_i\in\lbrace -1,1\rbrace$ are independent and uniform. Does
> $\lim_{n\to\infty,\ n\text{ odd}}F_{2,1}(n)^{1/n}$ exist, and if so, what is its value?

It is stated after Question 7.1 of
[*Double-jump phase transition for the reverse Littlewood–Offord problem*](https://arxiv.org/abs/2503.24202).
The construction of [Hollom and Sorkin](https://arxiv.org/abs/2510.05044) gives
$F_{2,1}(n)\le2^{-\lfloor n/2\rfloor}$. This repository proves, for every $0<\rho<1/2$, the
lower bound $F_{2,1}(n)\ge2^{-(n+1)}(1-\rho)^{-((n-3)/2-K_\rho)}$ with
$K_\rho=\lfloor1152/(1-2\rho)^2\rfloor$. Since $\tfrac12(1-\rho)^{-1/2}\to1/\sqrt2$ as
$\rho\to1/2$, the limit exists and equals $1/\sqrt2$.

The repository has three parts:

1. **[Formal Conjectures-style statement](fclikelean/ReverseLittlewoodOfford.lean).**
   A proposed statement with the whole definition written in the theorem. It is an
   unofficial, unsubmitted draft; its `answer(sorry)` and `by sorry` are intentional.
2. **[Modular proof on the Formal Conjectures toolchain](lean/ReverseLittlewoodOffordFC.lean).**
   The development pinned to Lean 4.33.1 and a Formal Conjectures revision.
3. **[Standalone Lean4Web file](lean4web/ReverseLittlewoodOffordLean4Web.lean).**
   A single mathlib-only file generated from the modular development by
   [`tools/export_lean4web.py`](tools/export_lean4web.py).

**Try it in Lean4Web** (after the repository is published):
[open the standalone file](https://live.lean-lang.org/#project=mathlib-stable&url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Freverse-littlewood-offord-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FReverseLittlewoodOffordLean4Web.lean)

## Formal Conjectures target

The declaration in [`lean/ReverseLittlewoodOffordFC.lean`](lean/ReverseLittlewoodOffordFC.lean)
is:

```lean
theorem reverse_littlewood_offord_rate :
    Tendsto
      (fun k : ℕ =>
        (⨅ v : {v : Fin (2 * k + 1) → ℂ // ∀ i, ‖v i‖ = 1},
          ((Finset.univ.filter fun ε : Fin (2 * k + 1) → Bool =>
              ‖∑ i, (if ε i then v.1 i else -v.1 i)‖ ≤ 1).card : ℝ) / 2 ^ (2 * k + 1))
          ^ (1 / (2 * k + 1 : ℝ)))
      atTop (𝓝 (answer(1 / Real.sqrt 2) : ℝ)) :=
  inline_statement_iff_helper.mpr rootSeq_tendsto
```

| Lean expression | Meaning |
|---|---|
| `v : Fin (2 * k + 1) → ℂ`, `‖v i‖ = 1` | $n=2k+1$ unit vectors in the plane, written as complex numbers |
| `ε : Fin (2 * k + 1) → Bool` | A sign vector; `true` stands for $+1$ |
| `‖∑ i, (if ε i then v.1 i else -v.1 i)‖ ≤ 1` | The signed sum lies in the closed unit disc |
| `(… .card : ℝ) / 2 ^ (2 * k + 1)` | The probability for uniform independent signs |
| `⨅ v : …` | The infimum $F_{2,1}(n)$ over all configurations |
| `^ (1 / (2 * k + 1 : ℝ))` | The $n$-th root |
| `Tendsto … atTop (𝓝 (answer(1 / Real.sqrt 2) : ℝ))` | The $n$-th roots converge to $1/\sqrt2$ |

`inline_statement_iff_helper` shows that this inlined statement is definitionally the helper
statement `Tendsto rootSeq atTop (𝓝 (1 / Real.sqrt 2))`. Its proof is `Iff.rfl` and already
uses only the standard axioms.

## Proof sketch (AI generated)

Throughout, $n$ is odd and vectors in $\mathbb{R}^2$ are identified with complex numbers. For
unit vectors $v_1,\dots,v_n$ and signs $\varepsilon\in\lbrace -1,1\rbrace^n$ put
$\sigma_\varepsilon=\sum_i\varepsilon_iv_i$. Call $\varepsilon$ *good* if
$\lvert\sigma_\varepsilon\rvert\le1$, and let $N(v)$ be the number of good sign vectors, so that
$F_{2,1}(n)=\inf_vN(v)/2^n$.

**Theorem.** For every odd $n$ and every $0<\rho<1/2$,

$$F_{2,1}(n)\ \ge\ 2^{-(n+1)}(1-\rho)^{-r},\qquad r=\max\Bigl(0,\ \frac{n-3}{2}-K_\rho\Bigr),\qquad K_\rho=\Bigl\lfloor\frac{1152}{(1-2\rho)^2}\Bigr\rfloor .$$

Together with the Hollom–Sorkin bound $F_{2,1}(n)\le2^{-(n-1)/2}$ this gives
$F_{2,1}(n)^{1/n}\to1/\sqrt2$.

### Step 1. Alternating sums in a half-plane

**Lemma 1.** Let $-\pi/2\le\theta_1\le\dots\le\theta_s\le\pi/2$, and let $c_1,\dots,c_s$ be real
numbers whose partial sums $P_k=c_1+\dots+c_k$ all lie in $[0,1]$, with $P_s=1$. Then
$\bigl\lvert\sum_kc_ke^{i\theta_k}\bigr\rvert\le1$.

The basic example is $c=(1,-1,1,\dots,-1,1)$ with $s$ odd: an odd family of unit vectors sorted by
angle in a closed half-plane satisfies $\lvert w_1-w_2+w_3-\dots+w_s\rvert\le1$.

*Proof.* Let $U=\sum_kc_ke^{i\theta_k}$ and choose $\psi\in[0,\pi]$ with $Ue^{-i\psi}$ real. The
indices with $\theta_k<\psi-\pi/2$ form an initial segment $k\le j$. Move them to the end of the
list and replace each such pair $(c_k,e^{i\theta_k})$ by $(-c_k,-e^{i\theta_k})$; this does not
change $U$. The new angles $\varphi_1\le\dots\le\varphi_s$ lie in $[\psi-\pi/2,\psi+\pi/2]$, and the
partial sums of the new coefficients $c'$ lie in the interval $[-P_j,1-P_j]$ of length $1$, so every
sum of consecutive $c'_m$ lies in $[-1,1]$. Hence $\lvert U\rvert=\bigl\lvert\sum_mc'_my_m\bigr\rvert$
with $y_m=\cos(\varphi_m-\psi)\in[0,1]$, and $(y_m)$ is unimodal. Write
$y_m=\int_0^1\mathbf 1[y_m>t]\ dt$. Each level set $\lbrace m:y_m>t\rbrace$ is a block of
consecutive indices, so $\bigl\lvert\sum_mc'_m\mathbf 1[y_m>t]\bigr\rvert\le1$ for every $t$, and
therefore $\lvert U\rvert\le1$. $\square$

In Lean the integral is replaced by an induction on $s$: subtract $\min(y_1,y_s)$ and drop an
endpoint.

### Step 2. Normal form

$N(v)$ does not change if some $v_i$ are replaced by $-v_i$, if the $v_i$ are permuted, or if all
$v_i$ are multiplied by the same unit complex number. With these moves and the cut move from Step
1 (with $\psi$ the direction of the alternating sum) we may assume

$$v_k=e^{i\theta_k},\qquad-\frac\pi2\le\theta_1\le\dots\le\theta_n\le\frac\pi2,\qquad\beta:=v_1-v_2+v_3-\dots+v_n\in\mathbb{R}.$$

Lemma 1 gives $\lvert\beta\rvert\le1$, and the horizontal coordinates $x_k=\cos\theta_k\in[0,1]$
form a unimodal sequence.

### Step 3. Pairs around a pivot

If $\beta\ge0$, let $p$ be an odd index at which $x_p$ is largest among the odd indices, and pair
$(1,2),\dots,(p-2,p-1),(p+1,p+2),\dots,(n-1,n)$. If $\beta<0$, let $p$ be an even index at which
$x_p$ is largest among the even indices, and pair $(2,3),\dots,(p-2,p-1),(p+1,p+2),\dots,(n-2,n-1)$;
the indices $1,p,n$ stay unpaired. Either way there are $m\ge(n-3)/2$ disjoint pairs of adjacent
indices.

For a pair $j$ let $d_j=v_{\mathrm{even}}-v_{\mathrm{odd}}$ be the difference of its even-indexed
and odd-indexed vectors. Removing the pair from the alternating sum adds $d_j$ to it. Because
$(x_k)$ is unimodal and $x_p$ is the largest value of its parity, $\operatorname{Re}d_j\ge0$ for all
$j$ when $\beta\ge0$, and $\operatorname{Re}d_j\le0$ for all $j$ when $\beta<0$. In the second case
apply the reflection $z\mapsto-\overline z$, which preserves all norms. From now on the alternating
sum is $b:=\lvert\beta\rvert\in[0,1]$ and $\operatorname{Re}d_j\ge0$ for all $j$.

### Step 4. Hereditary deletion and flips

Removing the pairs in a set $R$ turns the coefficients $(1,-1,1,\dots,1)$ into a sequence with zeros
at the removed positions. Each removed pair has coefficients $(1,-1)$ or $(-1,1)$, so the partial
sums change only between its two entries, where they take the value just before the pair. They
still lie in $[0,1]$ and end at $1$, and Lemma 1 gives

$$\Bigl\lvert b+\sum_{j\in R}d_j\Bigr\rvert\le1\qquad\text{for every set }R\text{ of pairs.}$$

Taking $R$ to be all pairs gives $\sum_j\operatorname{Re}d_j\le1-b$.

Changing both signs of every pair in a set $Q$ turns the alternating sign vector
$(+,-,+,\dots,+)$ into a sign vector whose signed sum is $b+2\sum_{j\in Q}d_j$ (up to the
reflection), and different sets $Q$ give different sign vectors. Hence $N(v)$ is at least the number
of sets $Q$ with $\bigl\lvert b+2\sum_{j\in Q}d_j\bigr\rvert\le1$.

### Step 5. Normalized coordinates

If $b=1$, then every $d_j$ is $0$ and every $Q$ is good. Otherwise put $\delta=1-b>0$ and write
$d_j=\delta p_j+i\sqrt\delta q_j$ with real $p_j,q_j$. A direct computation gives

$$\bigl\lvert b+\delta X+i\sqrt\delta Y\bigr\rvert^2=b^2+\delta\Phi(X,Y),\qquad\Phi(X,Y)=\delta X^2+Y^2+2bX,$$

so the closed unit disc becomes the region $\Phi\le1+b$. We have $p_j\ge0$ and $\sum_jp_j\le1$.
Applying Step 4 to $R=\lbrace j:q_j>0\rbrace$ and to $R=\lbrace j:q_j<0\rbrace$ gives
$\bigl(\sum_{j\in R}q_j\bigr)^2\le1+b\le2$, so $\sum_j\lvert q_j\rvert\le3$ and

$$\sum_j\bigl(p_j+\lvert q_j\rvert\bigr)\le4,$$

uniformly in $\delta$. This is what makes the argument work even when $b$ is close to $1$.

### Step 6. Random flips

Fix $0<\rho<1/2$ and put $g=1-2\rho$ and $\eta=g^2/288$. Call a pair *light* if
$p_j+\lvert q_j\rvert\le\eta$. By Step 5 at most $4/\eta=1152/g^2$ pairs are heavy, so the set $L$
of light pairs has $\lvert L\rvert\ge m-K_\rho$. Choose $Q\subseteq L$ by putting each light pair
in $Q$ independently with probability $\rho$. Write $A=\sum_{j\in L}(p_j,q_j)$ and
$Z=2\sum_{j\in Q}(p_j,q_j)$, so that $\mathbb{E}Z=2\rho A$.

* *The mean has slack $g$.* Step 4 with $R=L$ gives $\Phi(A)\le1+b$. For $0\le t\le1$,

  $$\Phi(tA)=t\Phi(A)-t(1-t)\bigl(\delta A_x^2+A_y^2\bigr)\le t(1+b),$$

  so $t=2\rho$ gives $\Phi(\mathbb{E}Z)\le(1-g)(1+b)$.
* *Points near the mean are good.* Let $\mu=\mathbb{E}Z$, and for a point $z$ let $e=z-\mu$. From
  $\Phi(\mu)\le(1-g)(1+b)$ and $\mu_x\ge0$ one gets $0\le b+\delta\mu_x\le1$ and
  $\lvert\mu_y\rvert\le3/2$, hence

  $$\Phi(z)-\Phi(\mu)=2(b+\delta\mu_x)e_x+2\mu_ye_y+\delta e_x^2+e_y^2\le5\lvert e\rvert+\lvert e\rvert^2.$$

  If $\lvert e\rvert\le g/6$ this is at most $g\le g(1+b)$, so $\Phi(z)\le1+b$.
* *Most flip sets are near the mean.* For independent flips,

  $$\mathbb{E}\lvert Z-\mathbb{E}Z\rvert^2=4\rho(1-\rho)\sum_{j\in L}\bigl(p_j^2+q_j^2\bigr)\le\eta\sum_{j\in L}\bigl(p_j+\lvert q_j\rvert\bigr)\le4\eta=\frac12\Bigl(\frac g6\Bigr)^2 .$$

  By Markov's inequality, $\lvert Z-\mathbb{E}Z\rvert\le g/6$ with probability at least $1/2$.

So the good sets $Q\subseteq L$ have total probability at least $1/2$.

### Step 7. Counting

Every $Q\subseteq L$ has probability $\rho^{\lvert Q\rvert}(1-\rho)^{\lvert L\rvert-\lvert Q\rvert}\le(1-\rho)^{\lvert L\rvert}$.
So at least $\frac12(1-\rho)^{-\lvert L\rvert}$ sets $Q$ are good, and by Step 4

$$\mathbb{P}\bigl(\lvert\sigma\rvert\le1\bigr)=\frac{N(v)}{2^n}\ \ge\ 2^{-(n+1)}(1-\rho)^{-\lvert L\rvert},\qquad\lvert L\rvert\ge\frac{n-3}{2}-K_\rho .$$

This proves the theorem.

### Step 8. The limit

*Upper bound.* Write $n=2k+1$. Hollom and Sorkin take $k$ pairs of equal unit vectors
$a_1,a_1,\dots,a_k,a_k$ together with one copy of $1$, where the vertical coordinates of the $a_i$
decrease geometrically. In Lean, $a_i=\bigl(1-t_i^2+2it_i\bigr)/\bigl(1+t_i^2\bigr)$ with
$t_i=20^{-i}$, which avoids square roots. Suppose some pair does not cancel, and let $t$ be the
parameter of the first such pair. Then the vertical coordinate of the signed sum has absolute
value at least $3.5t$, and the horizontal coordinate is an odd integer up to an error of at most
$4.5t^2$. So the squared norm is at least $(1-4.5t^2)^2+12.25t^2>1$. Every good sign vector
therefore cancels every pair. There are only $2^{k+1}$ such sign vectors, so
$F_{2,1}(n)\le2^{k+1}/2^n=2^{-k}$.

*Lower bound.* Put $\lambda=(1-\rho)^{-1}\in(1,2)$. The theorem gives
$F_{2,1}(2k+1)\ge C_\rho(\lambda/4)^k$ with $C_\rho>0$, so
$\liminf F_{2,1}(n)^{1/n}\ge\sqrt\lambda/2=\frac1{2\sqrt{1-\rho}}$. As $\rho\to1/2$ this tends to
$1/\sqrt2$, which matches $\limsup F_{2,1}(n)^{1/n}\le2^{-1/2}$. $\blacksquare$

### Where each step is formalized

| Step | Lean file | Main declarations |
|---|---|---|
| 1 | [`AlternatingSum.lean`](lean/ReverseLittlewoodOfford/AlternatingSum.lean) | `abs_sum_mul_le_of_unimodal`, `norm_sum_le_one_of_altPattern` |
| 2 | [`Normalization.lean`](lean/ReverseLittlewoodOfford/Normalization.lean) | `goodCount_mul_sign`, `goodCount_comp_equiv`, `goodCount_mul_unit`, `exists_normal_form` |
| 3–4 | [`HereditaryDeletion.lean`](lean/ReverseLittlewoodOfford/HereditaryDeletion.lean) | `pairDiff_re_nonneg_even`, `norm_altSum_add_le_one`, `card_good_flips_le`, `exists_pair_data` |
| 5–7 | [`Concentration.lean`](lean/ReverseLittlewoodOfford/Concentration.lean), [`LowerBound.lean`](lean/ReverseLittlewoodOfford/LowerBound.lean) | `sum_flipWeight_mul_sq`, `disc_stability`, `many_good_flips`, `lower_bound_A` |
| 8 | [`UpperConstruction.lean`](lean/ReverseLittlewoodOfford/UpperConstruction.lean), [`Limit.lean`](lean/ReverseLittlewoodOfford/Limit.lean), [`Rate.lean`](lean/ReverseLittlewoodOfford/Rate.lean) | `hollom_sorkin_construction`, `tendsto_root_of_bounds`, `rootSeq_tendsto` |

## Formalization status

| Component | File | Status |
|---|---|---|
| Definitions, `minProb_le` | [`Defs.lean`](lean/ReverseLittlewoodOfford/Defs.lean) | proved |
| Lemma 1 and its layer-cake core | [`AlternatingSum.lean`](lean/ReverseLittlewoodOfford/AlternatingSum.lean) | proved |
| Lemma 2 (normal form) | [`Normalization.lean`](lean/ReverseLittlewoodOfford/Normalization.lean) | proved |
| Lemmas 3–4 (pairs, hereditary deletion) | [`HereditaryDeletion.lean`](lean/ReverseLittlewoodOfford/HereditaryDeletion.lean) | proved |
| Lemmas 5, 7, 8 and the count of good flips | [`Concentration.lean`](lean/ReverseLittlewoodOfford/Concentration.lean) | proved |
| Lower bound (A) | [`LowerBound.lean`](lean/ReverseLittlewoodOfford/LowerBound.lean) | proved |
| Hollom–Sorkin upper bound | [`UpperConstruction.lean`](lean/ReverseLittlewoodOfford/UpperConstruction.lean) | proved |
| Squeeze lemma for the roots | [`Limit.lean`](lean/ReverseLittlewoodOfford/Limit.lean) | proved |
| The limit `rootSeq_tendsto` | [`Rate.lean`](lean/ReverseLittlewoodOfford/Rate.lean) | proved |
| Inlined target | [`ReverseLittlewoodOffordFC.lean`](lean/ReverseLittlewoodOffordFC.lean) | derived from `rootSeq_tendsto` |

## Files

| Directory | Environment | Contents |
|---|---|---|
| [`fclikelean/`](fclikelean/README.md) | Formal Conjectures-style draft | Inlined statement; intentional placeholders |
| [`lean/`](lean/README.md) | Lean 4.33.1; pinned Formal Conjectures dependency | Modular development |
| [`lean4web/`](lean4web/README.md) | Lean 4.33.0; pinned mathlib dependency | Standalone file and build configuration |
| [`tools/`](tools/export_lean4web.py) | Python 3 | Generates the standalone file from `lean/` |

## Verification

From the repository root, build the modular development:

```bash
cd lean
lake exe cache get
lake --wfail build
```

Or check the standalone file:

```bash
cd lean4web
lake update
lake exe cache get
lake env lean ReverseLittlewoodOffordLean4Web.lean
```

The final report is:

```text
'ReverseLittlewoodOfford.reverse_littlewood_offord_rate' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

[`lean/ReverseLittlewoodOffordVerified.lean`](lean/ReverseLittlewoodOffordVerified.lean) prints
the same report for every component.

## Sources

- J. E. Littlewood and A. C. Offord, *On the number of real roots of a random algebraic
  equation*, J. London Math. Soc. 13 (1938), 288–295.
- P. Erdős, *On a lemma of Littlewood and Offord*, Bull. Amer. Math. Soc. 51 (1945), 898–902.
- D. J. Kleitman, *On a lemma of Littlewood and Offord on the distribution of certain sums*,
  Math. Z. (1965), 251–259; *On a lemma of Littlewood and Offord on the distributions of linear
  combinations of vectors*, Adv. Math. 5 (1970), 155–157.
- J. Beck, *On a geometric problem of Erdős, Sárközy, and Szemerédi concerning vector sums*,
  European J. Combin. 4 (1983), 1–10.
- W. Carnielli and P. K. Carolino, *Adjusting a conjecture of Erdős*, Contrib. Discrete Math. 6
  (2011), 154–159.
- Xiaoyu He, Tomas Juškevičius, Bhargav Narayanan and Sam Spiro,
  [*The reverse Littlewood–Offord problem of Erdős*](https://arxiv.org/abs/2408.11034),
  arXiv:2408.11034 (2024).
- Lawrence Hollom, Julien Portier and Victor Souza,
  [*Double-jump phase transition for the reverse Littlewood–Offord problem*](https://arxiv.org/abs/2503.24202),
  arXiv:2503.24202; *J. London Math. Soc.* (2026).
- Lawrence Hollom and Gregory B. Sorkin,
  [*Reverse Littlewood–Offord problems with parity conditions*](https://arxiv.org/abs/2510.05044),
  arXiv:2510.05044 (2025).
- T. F. Bloom, Erdős Problems, [#395](https://www.erdosproblems.com/395) and
  [#498](https://www.erdosproblems.com/498); Formal Conjectures,
  [`ErdosProblems/395.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/395.lean)
  and
  [`ErdosProblems/498.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/498.lean).
- The three-directory layout follows
  [`KitaKen1/littlewood-cylinders-lean`](https://github.com/KitaKen1/littlewood-cylinders-lean).

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced
by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra, and Claude Code
using Claude Opus 5.5.

## Appendix: history of the problem

**In short.** The *Littlewood–Offord problem* asks for an **upper** bound: a random signed sum of
large numbers rarely lands in a small disc. Its sharp planar form is
[Erdős Problem #498](https://www.erdosproblems.com/498), solved by Kleitman. The *reverse*
problem asks for a **lower** bound: a random signed sum of unit vectors lands near the origin
reasonably often. Erdős's question of this kind is
[Erdős Problem #395](https://www.erdosproblems.com/395). It is false at radius $1$ for even $n$
and true at radius $\sqrt2$ (Beck; He, Juškevičius, Narayanan and Spiro). The case of odd $n$ at
radius $1$ is not covered by either problem. It is where this repository's result lives.

### The Littlewood–Offord problem: an upper bound

In their work on the number of real roots of random polynomials, Littlewood and Offord (1938)
needed the following estimate. If $z_1,\dots,z_n$ are complex numbers with $\lvert z_i\rvert\ge1$
and the signs $\varepsilon_i=\pm1$ are independent and uniform, then
$\varepsilon_1z_1+\dots+\varepsilon_nz_n$ lands in any given open disc of radius $1$ with
probability $O(n^{-1/2}\log n)$. A sum of many large terms with random signs cannot concentrate on
a small region. Estimates of this kind are what "Littlewood–Offord problem" means today.

Erdős (1945) found the sharp form for real numbers. At most $\binom{n}{\lfloor n/2\rfloor}$ of the
$2^n$ signed sums lie in any open interval of length $2$, so the probability is at most
$\binom{n}{\lfloor n/2\rfloor}2^{-n}\approx\sqrt{2/(\pi n)}$. The proof is a short application of
Sperner's theorem, and $z_1=\dots=z_n=1$ shows that the bound is sharp. For complex numbers Erdős
proved only a bound of order $2^n/\sqrt n$ and asked whether the sharp count
$\binom{n}{\lfloor n/2\rfloor}$ still holds for every open disc of radius $1$. This is
**Erdős Problem #498**. Kleitman proved it in 1965 and extended it to vectors in any Hilbert space
in 1970.

### The reverse problem: a lower bound

In the same 1945 paper Erdős asked the opposite question. If $\lvert z_i\rvert=1$ for all $i$, does
the random signed sum lie in the closed unit disc with probability $\gg1/n$? Instead of saying that
the sum rarely lands in a small region, this asks that it always comes back near the origin
reasonably often, whatever the unit vectors are. Questions of this kind are called reverse
Littlewood–Offord problems. Erdős's question is **Erdős Problem #395**.

* **Radius $1$ fails for even $n$.** Carnielli and Carolino (2011) took $z_1=1$ and
  $z_2=\dots=z_n=i$ with $n$ even. The real part of every signed sum is $\pm1$, and the imaginary
  part is a sum of an odd number of terms $\pm1$, so every signed sum has norm at least $\sqrt2$.
  They proposed radius $\sqrt2$ instead, and this is how #395 is stated today.
* **Radius $\sqrt2$ is true.** Beck (1983) had already proved that for unit vectors in
  $\mathbb{R}^d$ the signed sum has norm at most $\sqrt d$ with probability at least $c_dn^{-d/2}$.
  His paper does not cite Erdős's 1945 paper; the case $d=2$ is #395. He, Juškevičius, Narayanan
  and Spiro (2024) found an independent, elementary proof by pairing vectors before they learned of
  Beck's paper, and erdosproblems.com lists #395 as solved. The order $1/n$ cannot be improved:
  take half of the $z_k$ equal to $1$ and the other half equal to $i$.

### Odd $n$ at radius one: the question answered here

The counterexample at radius $1$ needs $n$ to be even. He, Juškevičius, Narayanan and Spiro
conjectured (2024, Conjecture 4.1) that for odd $n$ Erdős's original radius $1$ works, that is,
$F_{2,1}(n)\ge c/n$.

* **Hollom, Portier and Souza (2025)** disproved this conjecture: some configurations have
  $\mathbb{P}(\lvert\sigma\rvert\le1)=O(n^{-3/2})$. They also proved that every radius $1+\delta$
  gives probability $\Omega_\delta(1/n)$, and that at radius $1$ the probability is at least
  exponentially small, $\Omega((1/2+\mu)^n)$ for an explicit $\mu>0$ (about $0.525^n$). So for odd
  $n$ the worst-case probability is $0$ below radius $1$ (take all $v_i$ equal), of order $1/n$
  above radius $1$, and much smaller exactly at radius $1$. This is the "double jump" in their
  title. They asked whether $F_{2,1}(n)$ decays polynomially or exponentially (Question 7.1), and,
  right after it, whether $\lim F_{2,1}(n)^{1/n}$ exists and what its value is.
* **Hollom and Sorkin (2025)** answered Question 7.1. Their construction gives
  $F_{2,1}(n)\le2^{-\lfloor n/2\rfloor}$, so the decay is exponential. After this, the limit, if it
  exists, was known to lie between about $0.525$ and $1/\sqrt2\approx0.707$.
* **This repository** proves that the limit exists and equals $1/\sqrt2$. In other words, the
  Hollom–Sorkin construction is optimal at the exponential scale. The proof is checked in Lean.

### Relation to Formal Conjectures

* `ErdosProblems/498.lean` states #498 (the Littlewood–Offord problem in the plane) and marks it
  solved, with a link to a Lean proof.
* `ErdosProblems/395.lean` states #395 at radius $\sqrt2$ (solved, with a link to a Lean proof),
  the radius-$1$ variant for all $n$ (false, because of even $n$), and the sharpness of $1/n$.
* Neither file treats odd $n$ at radius $1$. The statement proved here would be a new entry on
  the arXiv shelf, `FormalConjectures/Arxiv/2503.24202`; see [`fclikelean/`](fclikelean/README.md).

### Timeline

| Year | Who | What |
|---|---|---|
| 1938 | Littlewood, Offord | Small discs catch a random signed sum with probability $O(n^{-1/2}\log n)$ |
| 1945 | Erdős | Sharp bound $\binom{n}{\lfloor n/2\rfloor}2^{-n}$ for real numbers; asked #498 (complex numbers) and #395 (lower bound at radius $1$) |
| 1965, 1970 | Kleitman | Solved #498 in the plane, then in every Hilbert space |
| 1983 | Beck | Radius $\sqrt d$ in $\mathbb{R}^d$ gives probability at least $c_dn^{-d/2}$; for $d=2$ this is #395 at radius $\sqrt2$ |
| 2011 | Carnielli, Carolino | Radius $1$ fails for even $n$; proposed radius $\sqrt2$ |
| 2024 | He, Juškevičius, Narayanan, Spiro | New proof of #395 at radius $\sqrt2$; conjectured probability $\gg1/n$ at radius $1$ for odd $n$ |
| 2025 | Hollom, Portier, Souza | Disproved the odd-$n$ conjecture; double jump at radius $1$; asked for the exponential rate |
| 2025 | Hollom, Sorkin | $F_{2,1}(n)\le2^{-\lfloor n/2\rfloor}$, so the decay is exponential |
| 2026 | this repository | $F_{2,1}(n)^{1/n}\to1/\sqrt2$, checked in Lean |

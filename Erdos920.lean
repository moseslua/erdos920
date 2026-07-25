import Mathlib

/-!
# Erdős Problem 920

This file is a **self-contained** formalization: its only import is `Mathlib`.

## The question (erdosproblems.com #920, [Er69b])

> Let `f_k(n)` be the maximum possible chromatic number of a graph with `n`
> vertices which contains no `K_k`.  Is it true that, for `k ≥ 4`,
> `f_k(n) ≫ n^(1 - 1/(k-1)) / (log n)^(c_k)` for some constant `c_k > 0`?

## The answer proved here

**Yes**, conditional on the off-diagonal Ramsey lower bound
`r(k,t) ≫_k t^(k-1) / (log t)^(2k-4)` (Bradač 2026), with the explicit value

```
c_k = 2(k-2)/(k-1).
```

The top-level statement is `erdos_problem_920`; `erdos_problem_920_explicit`
exhibits `c_k` and `erdos_problem_920_isBigO` states it in the `≫` (Landau)
form used on the problem page.

At `k = 4` this reads `f_4(n) ≫ n^(2/3) / (log n)^(4/3)` (`erdos920_k4`), which
is exactly the consequence of Mattheus–Verstraete recorded on the problem page.
The new content is `k ≥ 5`: the page notes that the route through [986] gives
only the weaker exponent `1 - 1/(k-2)`, whereas the bound below achieves the
requested `1 - 1/(k-1)`.

## Structure

* §1 — `extremalChromaticNumber`, the formalization of `f_k(n)`, together with
  `exists_extremal_graph` certifying that it really is a maximum (attained).
* §2 — `finite_transfer` (Lemma 2.1): the finite Ramsey-to-chromatic transfer
  `r(k,t) > n ⟹ f_k(n) ≥ n/(t-1)`.
* §3 — `general_transfer` (Theorem 2.2): asymptotic inversion.  From
  `r(k,t) ≥ a t^d/(log t)^A` for `t ≥ t₀` with `a > 0`, `d > 1`, `A ≥ 0`, one
  gets `C > 0` with `f_k(n) ≥ C n^(1-1/d)/(log n)^(A/d)` for all large `n`.
* §4 — `erdos_problem_920` (Theorem 3.2): instantiation at `d = k-1`, `A = 2k-4`.

## Trust boundary

Bradač's Ramsey bound is a **hypothesis** (`BradacInput` / `ExistsBradacInput`),
never an axiom, and it is the only unproved input.  Everything else — the finite
counting argument, the choice of parameter, the ceiling and logarithm
bookkeeping, and the asymptotic inversion — is proved here from `Mathlib`.  The
`#print axioms` block at the end of the file certifies that the proofs use only
`propext`, `Classical.choice` and `Quot.sound`.  There is no `sorry`.
-/

namespace Erdos920

open SimpleGraph Filter Asymptotics

/-! ## §1. The extremal function `f_k(n)` -/

/-- A graph on exactly `n` vertices avoiding both a `k`-clique and an
independent set of order `t`.

The existence of such a graph is precisely the statement `r(k,t) > n` for the
off-diagonal Ramsey number.  Phrasing the Ramsey input this way avoids
introducing a Ramsey-number API, which mathlib does not currently provide for
graphs. -/
def RamseyWitness (k t n : ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ G.indepNum < t

/-- The natural-number-valued chromatic number of a finite graph. -/
noncomputable def chromaticNumberNat {V : Type*} (G : SimpleGraph V) : ℕ :=
  ENat.toNat G.chromaticNumber

/-- **`f_k(n)`**: the maximum chromatic number of a `K_k`-free graph on exactly
`n` vertices.  (That the supremum is attained is `exists_extremal_graph`.) -/
noncomputable def extremalChromaticNumber (k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    G.CliqueFree k ∧ m = chromaticNumberNat G}

lemma chromaticNumberNat_le_card {V : Type*} [Fintype V] (G : SimpleGraph V) :
    chromaticNumberNat G ≤ Fintype.card V :=
  ENat.toNat_le_of_le_coe G.colorable_of_fintype.chromaticNumber_le

private lemma extremalChromaticNumbers_bddAbove (k n : ℕ) :
    BddAbove {m : ℕ | ∃ G : SimpleGraph (Fin n),
      G.CliqueFree k ∧ m = chromaticNumberNat G} := by
  refine ⟨n, ?_⟩
  rintro m ⟨G, _, rfl⟩
  simpa using chromaticNumberNat_le_card G

/-- `f_k(n)` dominates the chromatic number of every `K_k`-free graph on `n`
vertices. -/
lemma chromaticNumberNat_le_extremal {k n : ℕ}
    (G : SimpleGraph (Fin n)) (hK : G.CliqueFree k) :
    chromaticNumberNat G ≤ extremalChromaticNumber k n := by
  apply le_csSup (extremalChromaticNumbers_bddAbove k n)
  exact ⟨G, hK, rfl⟩

/-- The supremum defining `f_k(n)` is **attained**: for `k ≥ 2` there is a
`K_k`-free graph on `n` vertices whose chromatic number is exactly
`extremalChromaticNumber k n`.  Together with `chromaticNumberNat_le_extremal`
this certifies that the definition really formalizes "the maximum possible
chromatic number of a graph with `n` vertices which contains no `K_k`". -/
theorem exists_extremal_graph {k n : ℕ} (hk : 2 ≤ k) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧
      chromaticNumberNat G = extremalChromaticNumber k n := by
  have hne : {m : ℕ | ∃ G : SimpleGraph (Fin n),
      G.CliqueFree k ∧ m = chromaticNumberNat G}.Nonempty :=
    ⟨chromaticNumberNat (⊥ : SimpleGraph (Fin n)),
      ⊥, SimpleGraph.cliqueFree_bot hk, rfl⟩
  obtain ⟨G, hK, hG⟩ :=
    Nat.sSup_mem hne (extremalChromaticNumbers_bddAbove k n)
  exact ⟨G, hK, hG.symm⟩

/-! ## §2. Lemma 2.1: the finite Ramsey-to-chromatic transfer -/

/-- Every colour class of a proper colouring is an independent set, hence has
order at most the independence number. -/
lemma card_colorClass_le_indepNum
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {α : Type*} [Fintype α] [DecidableEq α]
    (C : G.Coloring α) (c : α) :
    (Finset.univ.filter fun v : V => C v = c).card ≤ G.indepNum := by
  classical
  let s : Finset V := (C.colorClass c).toFinset
  have hs : G.IsIndepSet (↑s : Set V) := by
    simpa [s] using C.isIndepSet_colorClass c
  have hcard : s.card ≤ G.indepNum := hs.card_le_indepNum
  simpa [s, SimpleGraph.Coloring.colorClass] using hcard

/-- The counting inequality `|V| ≤ q · α(G)` for every `q`-colourable finite
graph: `q` colour classes, each of order at most `α(G)`, cover `V`. -/
theorem card_le_colors_mul_indepNum
    {V : Type*} [Fintype V] (G : SimpleGraph V) {q : ℕ}
    (hcol : G.Colorable q) :
    Fintype.card V ≤ q * G.indepNum := by
  by_contra hnot
  have hlt : q * G.indepNum < Fintype.card V := Nat.lt_of_not_ge hnot
  rcases hcol with ⟨C⟩
  obtain ⟨c, hc⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card
      (fun v : V => C v) (by simpa using hlt)
  exact (not_lt_of_ge (card_colorClass_le_indepNum C c)) hc

/-- **Lemma 2.1** (Finite Ramsey-to-chromatic transfer).

If `n < r(k,t)`, witnessed by a `K_k`-free graph on `n` vertices with
independence number `< t`, then `f_k(n) ≥ n / (t - 1)`. -/
theorem finite_transfer {k t n : ℕ} (hR : RamseyWitness k t n) (ht : 2 ≤ t) :
    (n : ℝ) / ((t - 1 : ℕ) : ℝ) ≤ (extremalChromaticNumber k n : ℝ) := by
  rcases hR with ⟨G, hK, hα⟩
  have hcount :=
    card_le_colors_mul_indepNum G G.colorable_chromaticNumber_of_fintype
  have hα' : G.indepNum ≤ t - 1 := by omega
  have hprod : n ≤ chromaticNumberNat G * (t - 1) := by
    simpa [chromaticNumberNat] using
      hcount.trans (Nat.mul_le_mul_left (chromaticNumberNat G) hα')
  have hprodR : (n : ℝ) ≤ (chromaticNumberNat G : ℝ) * ((t - 1 : ℕ) : ℝ) := by
    exact_mod_cast hprod
  have htpos : (0 : ℝ) < ((t - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < t - 1 by omega)
  have hG : (n : ℝ) / ((t - 1 : ℕ) : ℝ) ≤ (chromaticNumberNat G : ℝ) :=
    (div_le_iff₀ htpos).2 (by simpa [mul_comm] using hprodR)
  exact hG.trans (by exact_mod_cast chromaticNumberNat_le_extremal G hK)

/-! ## §3. Theorem 2.2: the general transfer theorem

Witness form of a Ramsey lower bound, the inversion parameter
`x_n = B n^(1/d) (log n)^(A/d)`, and the asymptotic inversion itself. -/

/-- Witness form of the Ramsey lower bound `r(k,t) ≥ a t^d / (log t)^A` for
`t ≥ t₀`: whenever `n` is below that threshold there is a `K_k`-free graph on
`n` vertices with independence number `< t`. -/
def RamseyLowerBound (k : ℕ) (a d A : ℝ) (t₀ : ℕ) : Prop :=
  ∀ ⦃t n : ℕ⦄, t₀ ≤ t →
    (n : ℝ) < a * (t : ℝ) ^ d / Real.log (t : ℝ) ^ A → RamseyWitness k t n

/-- The real parameter `x_n = B n^(1/d) (log n)^(A/d)` of Theorem 2.2. -/
noncomputable def transferValue (B d A : ℝ) (n : ℕ) : ℝ :=
  B * (n : ℝ) ^ d⁻¹ * Real.log (n : ℝ) ^ (A / d)

/-- The integer Ramsey parameter `t_n = ⌈x_n⌉`. -/
noncomputable def transferParam (B d A : ℝ) (n : ℕ) : ℕ := ⌈transferValue B d A n⌉₊

/-- The comparison function `n^(1 - 1/d) / (log n)^(A/d)` in the conclusion. -/
noncomputable def transferGrowth (d A : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (1 - d⁻¹) / Real.log (n : ℝ) ^ (A / d)

lemma transferGrowth_pos {d A : ℝ} {n : ℕ} (hn : 2 ≤ n) : 0 < transferGrowth d A n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos; exact_mod_cast (show 1 < n by omega)
  exact div_pos (Real.rpow_pos_of_pos hnpos _) (Real.rpow_pos_of_pos hlogpos _)

lemma transferValue_pos {B d A : ℝ} {n : ℕ} (hB : 0 < B) (hn : 2 ≤ n) :
    0 < transferValue B d A n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos; exact_mod_cast (show 1 < n by omega)
  exact mul_pos (mul_pos hB (Real.rpow_pos_of_pos hnpos _))
    (Real.rpow_pos_of_pos hlogpos _)

/-- The defining identity `x_n^d = B^d · n · (log n)^A`. -/
lemma transferValue_rpow {B d A : ℝ} {n : ℕ} (hB : 0 ≤ B) (hd : 0 < d) (hn : 2 ≤ n) :
    transferValue B d A n ^ d = B ^ d * (n : ℝ) * Real.log (n : ℝ) ^ A := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos; exact_mod_cast (show 1 < n by omega)
  rw [transferValue,
    Real.mul_rpow (by positivity) (Real.rpow_nonneg hlogpos.le _),
    Real.mul_rpow hB (Real.rpow_nonneg hnpos.le _),
    ← Real.rpow_mul hnpos.le, ← Real.rpow_mul hlogpos.le,
    inv_mul_cancel₀ hd.ne', Real.rpow_one, div_mul_cancel₀ _ hd.ne']

/-- `n / x_n = B⁻¹ · n^(1 - 1/d) / (log n)^(A/d)`. -/
lemma div_transferValue_eq {B d A : ℝ} {n : ℕ} (hB : 0 < B) (hn : 2 ≤ n) :
    (n : ℝ) / transferValue B d A n = B⁻¹ * transferGrowth d A n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos; exact_mod_cast (show 1 < n by omega)
  have hroot : 0 < (n : ℝ) ^ d⁻¹ := Real.rpow_pos_of_pos hnpos _
  have hlogpow : 0 < Real.log (n : ℝ) ^ (A / d) := Real.rpow_pos_of_pos hlogpos _
  rw [transferValue, transferGrowth, Real.rpow_sub hnpos, Real.rpow_one]
  field_simp

/-- `x_n = o(n)`: the Ramsey parameter is eventually much smaller than the
vertex count, so `t_n ≤ n` for large `n`. -/
lemma transferValue_isLittleO (B : ℝ) {d A : ℝ} (hd : 1 < d) :
    (fun n : ℕ => transferValue B d A n) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  have hs : 0 < 1 - d⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hd)
  have hlog :=
    (isLittleO_log_rpow_rpow_atTop (A / d) hs).comp_tendsto tendsto_natCast_atTop_atTop
  have hroot : (fun n : ℕ => (n : ℝ) ^ d⁻¹) =O[atTop] (fun n : ℕ => (n : ℝ) ^ d⁻¹) :=
    Asymptotics.isBigO_refl _ _
  have hmul := hroot.mul_isLittleO hlog
  have hprod :
      (fun n : ℕ => (n : ℝ) ^ d⁻¹ * (n : ℝ) ^ (1 - d⁻¹)) =ᶠ[atTop] (fun n : ℕ => (n : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [← Real.rpow_add (by exact_mod_cast hn)]
    norm_num
  have hmul' := hmul.congr' Filter.EventuallyEq.rfl hprod
  simpa [transferValue, mul_assoc] using hmul'.const_mul_left B

/-- `x_n → ∞`, so the parameter eventually exceeds any fixed threshold `c`
(applied below with `c = t₀`). -/
lemma eventually_lt_transferValue {B d A : ℝ} (hB : 0 < B) (hd : 1 < d) (hA : 0 ≤ A)
    (c : ℝ) : ∀ᶠ n : ℕ in atTop, c < transferValue B d A n := by
  have hdpos : (0 : ℝ) < d := lt_trans zero_lt_one hd
  have hinv : 0 < d⁻¹ := inv_pos.mpr hdpos
  have hrootTop :
      Filter.Tendsto (fun n : ℕ => B * (n : ℝ) ^ d⁻¹) atTop atTop :=
    ((tendsto_rpow_atTop hinv).comp tendsto_natCast_atTop_atTop).const_mul_atTop hB
  have hrootLarge : ∀ᶠ n : ℕ in atTop, max c 0 < B * (n : ℝ) ^ d⁻¹ :=
    hrootTop.eventually (Filter.eventually_gt_atTop (max c 0))
  have hlogTop : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) ^ (A / d) :=
    (hlogTop.eventually (Filter.eventually_ge_atTop 1)).mono fun _ hn =>
      Real.one_le_rpow hn (div_nonneg hA hdpos.le)
  filter_upwards [hrootLarge, hlogOne] with n hroot hlog
  have hc : c ≤ max c 0 := le_max_left _ _
  have hnn : (0 : ℝ) ≤ max c 0 := le_max_right _ _
  rw [transferValue]
  nlinarith

/-- The heart of **Theorem 2.2**, with the constant `B` supplied explicitly.

Given `B ≥ 1` with `a B^d > 1`, the parameter `t_n = ⌈B n^(1/d) (log n)^(A/d)⌉`
eventually satisfies `t₀ ≤ t_n ≤ n` and `a t_n^d / (log t_n)^A > n`, so Lemma 2.1
applies and yields `f_k(n) > B⁻¹ n^(1-1/d) / (log n)^(A/d)`. -/
theorem general_transfer_of_pow_lt
    {k t₀ : ℕ} {a d A B : ℝ}
    (ha : 0 < a) (hd : 1 < d) (hA : 0 ≤ A) (ht₀ : 2 ≤ t₀)
    (hB1 : 1 ≤ B) (haB : 1 < a * B ^ d)
    (hR : RamseyLowerBound k a d A t₀) :
    ∀ᶠ n : ℕ in atTop,
      B⁻¹ * transferGrowth d A n < (extremalChromaticNumber k n : ℝ) := by
  have hdpos : (0 : ℝ) < d := lt_trans zero_lt_one hd
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
  -- eventually `t₀ < x n`
  have hbig := eventually_lt_transferValue (A := A) hBpos hd hA (t₀ : ℝ)
  -- eventually `x n ≤ n / 2`, from `x n = o(n)`
  have hsmall := (transferValue_isLittleO (A := A) B hd).def (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [hbig, hsmall, Filter.eventually_ge_atTop 2] with n hbig hsmall hn2
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlogn : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos; exact_mod_cast (show 1 < n by omega)
  set x : ℝ := transferValue B d A n with hxdef
  set t : ℕ := transferParam B d A n with htdef
  have hxpos : 0 < x := transferValue_pos hBpos hn2
  have hxt : x ≤ (t : ℝ) := by
    simpa [htdef, transferParam, ← hxdef] using Nat.le_ceil x
  have hceil : (t : ℝ) < x + 1 := by
    simpa [htdef, transferParam, ← hxdef] using Nat.ceil_lt_add_one hxpos.le
  -- `t₀ ≤ t`
  have ht₀t : t₀ ≤ t := by
    have : ((t₀ : ℕ) : ℝ) ≤ (t : ℝ) := le_of_lt (lt_of_lt_of_le hbig hxt)
    exact_mod_cast this
  have ht2 : 2 ≤ t := le_trans ht₀ ht₀t
  -- `t ≤ n`
  have hhalf : x ≤ (n : ℝ) / 2 := by
    have := hsmall
    rw [Real.norm_of_nonneg hxpos.le, Real.norm_of_nonneg hnpos.le] at this
    linarith
  have htn : t ≤ n := by
    have hR2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have : (t : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast this
  have hlogt : 0 < Real.log (t : ℝ) := by
    apply Real.log_pos; exact_mod_cast (show 1 < t by omega)
  have hlogle : Real.log (t : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < t by omega)) (by exact_mod_cast htn)
  -- the Ramsey range inequality `n < a t^d / (log t)^A`
  have hlogtA : 0 < Real.log (t : ℝ) ^ A := Real.rpow_pos_of_pos hlogt _
  have hlognA : 0 < Real.log (n : ℝ) ^ A := Real.rpow_pos_of_pos hlogn _
  have hxd : x ^ d = B ^ d * (n : ℝ) * Real.log (n : ℝ) ^ A :=
    transferValue_rpow hBpos.le hdpos hn2
  have hpow : x ^ d ≤ (t : ℝ) ^ d := Real.rpow_le_rpow hxpos.le hxt hdpos.le
  have hlogpow : Real.log (t : ℝ) ^ A ≤ Real.log (n : ℝ) ^ A :=
    Real.rpow_le_rpow hlogt.le hlogle hA
  have hrange : (n : ℝ) < a * (t : ℝ) ^ d / Real.log (t : ℝ) ^ A := by
    have step1 : (n : ℝ) < a * B ^ d * (n : ℝ) := by nlinarith
    have step2 : a * B ^ d * (n : ℝ) = a * x ^ d / Real.log (n : ℝ) ^ A := by
      rw [hxd]; field_simp
    have step3 : a * x ^ d / Real.log (n : ℝ) ^ A
        ≤ a * (t : ℝ) ^ d / Real.log (n : ℝ) ^ A := by
      gcongr
    have step4 : a * (t : ℝ) ^ d / Real.log (n : ℝ) ^ A
        ≤ a * (t : ℝ) ^ d / Real.log (t : ℝ) ^ A := by
      apply div_le_div_of_nonneg_left _ hlogtA hlogpow
      positivity
    linarith [step1, step2 ▸ step1, step3, step4]
  -- Lemma 2.1
  have hW : RamseyWitness k t n := hR ht₀t hrange
  have hlower := finite_transfer hW ht2
  -- `t - 1 < x`, hence `n / x < n / (t - 1) ≤ f_k(n)`
  have htm1 : ((t - 1 : ℕ) : ℝ) < x := by
    rw [Nat.cast_sub (show 1 ≤ t by omega)]
    push_cast
    linarith
  have hdiv : (n : ℝ) / x < (n : ℝ) / ((t - 1 : ℕ) : ℝ) :=
    div_lt_div_of_pos_left hnpos
      (by exact_mod_cast (show 0 < t - 1 by omega)) htm1
  rw [← div_transferValue_eq (A := A) hBpos hn2]
  exact lt_of_lt_of_le hdiv hlower

/-- **Theorem 2.2** (General transfer theorem).

Fix `k`.  If there are constants `a > 0`, `d > 1`, `A ≥ 0` and `t₀ ≥ 2` with

```
r(k, t) ≥ a t^d / (log t)^A     for all t ≥ t₀,
```

then there is a constant `C > 0` such that

```
f_k(n) ≥ C n^(1 - 1/d) / (log n)^(A/d)
```

for every sufficiently large `n` — for *every* large integer `n`, not merely
along a sparse sequence of orders. -/
theorem general_transfer {k t₀ : ℕ} {a d A : ℝ}
    (ha : 0 < a) (hd : 1 < d) (hA : 0 ≤ A) (ht₀ : 2 ≤ t₀)
    (hR : RamseyLowerBound k a d A t₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C * transferGrowth d A n < (extremalChromaticNumber k n : ℝ) := by
  have hdpos : (0 : ℝ) < d := lt_trans zero_lt_one hd
  -- choose `B ≥ 1` with `a B^d > 1`
  set B : ℝ := max 1 ((2 / a) ^ d⁻¹) with hBdef
  have hB1 : 1 ≤ B := le_max_left _ _
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
  have hkey : 2 / a ≤ B ^ d := by
    have h0 : (0 : ℝ) ≤ (2 / a) ^ d⁻¹ := Real.rpow_nonneg (by positivity) _
    have hle : ((2 / a) ^ d⁻¹) ^ d ≤ B ^ d :=
      Real.rpow_le_rpow h0 (le_max_right _ _) hdpos.le
    rwa [← Real.rpow_mul (by positivity), inv_mul_cancel₀ hdpos.ne', Real.rpow_one] at hle
  have haB : 1 < a * B ^ d := by
    have : a * (2 / a) ≤ a * B ^ d := by nlinarith
    rw [mul_div_cancel₀ _ ha.ne'] at this
    linarith
  exact ⟨B⁻¹, inv_pos.mpr hBpos,
    general_transfer_of_pow_lt ha hd hA ht₀ hB1 haB hR⟩

/-- Landau form of Theorem 2.2: `f_k(n) ≫ n^(1-1/d) / (log n)^(A/d)`. -/
theorem general_transfer_isBigO {k t₀ : ℕ} {a d A : ℝ}
    (ha : 0 < a) (hd : 1 < d) (hA : 0 ≤ A) (ht₀ : 2 ≤ t₀)
    (hR : RamseyLowerBound k a d A t₀) :
    (fun n : ℕ => transferGrowth d A n) =O[atTop]
      (fun n : ℕ => (extremalChromaticNumber k n : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := general_transfer ha hd hA ht₀ hR
  rw [Asymptotics.isBigO_iff'']
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, Filter.eventually_ge_atTop 2] with n hn hn2
  have hgrowth : 0 ≤ transferGrowth d A n := (transferGrowth_pos hn2).le
  have hextremal : 0 ≤ (extremalChromaticNumber k n : ℝ) := by positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg hgrowth, abs_of_nonneg hextremal] using hn.le

/-- Non-vacuity: the function bounded below in Theorem 2.2 itself tends to
infinity, so the theorem genuinely forces `f_k(n) → ∞` at a polynomial rate
rather than bounding it below by something bounded.  Indeed
`(log n)^(A/d) = o(n^((1-1/d)/2))`, hence
`n^(1-1/d) / (log n)^(A/d) ≥ n^((1-1/d)/2) → ∞`. -/
lemma tendsto_transferGrowth_atTop {d A : ℝ} (hd : 1 < d) :
    Filter.Tendsto (fun n : ℕ => transferGrowth d A n) atTop atTop := by
  have hrpos : (0 : ℝ) < 1 - d⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hd)
  have hhalf : (0 : ℝ) < (1 - d⁻¹) / 2 := by linarith
  have hlog : ∀ᶠ n : ℕ in atTop,
      ‖Real.log (n : ℝ) ^ (A / d)‖ ≤ 1 * ‖(n : ℝ) ^ ((1 - d⁻¹) / 2)‖ :=
    tendsto_natCast_atTop_atTop.eventually
      ((isLittleO_log_rpow_rpow_atTop (A / d) hhalf).def (by norm_num))
  have hbase : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 - d⁻¹) / 2)) atTop atTop :=
    (tendsto_rpow_atTop hhalf).comp tendsto_natCast_atTop_atTop
  refine tendsto_atTop_mono' _ ?_ hbase
  filter_upwards [hlog, Filter.eventually_ge_atTop 2] with n hn hn2
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos; exact_mod_cast (show 1 < n by omega)
  have hL : 0 < Real.log (n : ℝ) ^ (A / d) := Real.rpow_pos_of_pos hlogpos _
  have hQ : 0 < (n : ℝ) ^ ((1 - d⁻¹) / 2) := Real.rpow_pos_of_pos hnpos _
  have hLQ : Real.log (n : ℝ) ^ (A / d) ≤ (n : ℝ) ^ ((1 - d⁻¹) / 2) := by
    simpa [Real.norm_of_nonneg hL.le, Real.norm_of_nonneg hQ.le] using hn
  rw [transferGrowth, le_div_iff₀ hL]
  calc (n : ℝ) ^ ((1 - d⁻¹) / 2) * Real.log (n : ℝ) ^ (A / d)
      ≤ (n : ℝ) ^ ((1 - d⁻¹) / 2) * (n : ℝ) ^ ((1 - d⁻¹) / 2) := by gcongr
    _ = (n : ℝ) ^ (1 - d⁻¹) := by rw [← Real.rpow_add hnpos]; ring_nf

/-! ## §4. Theorem 3.2: the answer to Problem 920

The Ramsey input, and its instantiation `d = k - 1`, `A = 2k - 4`. -/

/-- **The Ramsey input.** For fixed `k` and a constant `γ > 0`: whenever

```
n < γ t^(k-1) / (log t)^(2k-4),
```

there is an `n`-vertex graph with neither a `K_k` nor an independent `t`-set —
i.e. `r(k,t) ≥ γ t^(k-1) / (log t)^(2k-4)`.

This is Bradač's off-diagonal Ramsey theorem (2026), and it is the **only**
unproved input to the results below.  It is a hypothesis, never an axiom. -/
def BradacInput (k : ℕ) (γ : ℝ) : Prop :=
  0 < γ ∧
    ∀ ⦃t n : ℕ⦄, 2 ≤ t →
      (n : ℝ) < γ * (t : ℝ) ^ (k - 1) / Real.log (t : ℝ) ^ (2 * k - 4) →
      RamseyWitness k t n

/-- Bundled form: the Ramsey theorem supplies *some* positive constant `γ_k`. -/
def ExistsBradacInput (k : ℕ) : Prop := ∃ γ : ℝ, BradacInput k γ

/-- The logarithmic exponent `c_k = 2(k-2)/(k-1)` produced below. -/
noncomputable def erdosExponent (k : ℕ) : ℝ := 2 * ((k : ℝ) - 2) / ((k : ℝ) - 1)

lemma erdosExponent_pos {k : ℕ} (hk : 3 ≤ k) : 0 < erdosExponent k := by
  have h3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  apply div_pos <;> linarith

/-- The Ramsey input in the general `RamseyLowerBound` shape: `d = k - 1`,
`A = 2k - 4`, `t₀ = 2`.  (This converts the natural-number exponents of
`BradacInput` into the real exponents of `RamseyLowerBound`.) -/
theorem ramseyLowerBound_of_bradacInput {k : ℕ} {γ : ℝ} (hk : 3 ≤ k)
    (hBr : BradacInput k γ) :
    RamseyLowerBound k γ ((k : ℝ) - 1) (2 * (k : ℝ) - 4) 2 := by
  intro t n ht hlt
  refine hBr.2 ht ?_
  have hd : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hA : ((2 * k - 4 : ℕ) : ℝ) = 2 * (k : ℝ) - 4 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rwa [← Real.rpow_natCast (t : ℝ) (k - 1), ← Real.rpow_natCast (Real.log (t : ℝ)) (2 * k - 4),
    hd, hA]

/-- **Theorem 3.2**, with the exponent named.  For every `k ≥ 3` there is
`C_k > 0` with

```
f_k(n) ≥ C_k · n^(1 - 1/(k-1)) / (log n)^(2(k-2)/(k-1))
```

for all sufficiently large `n`. -/
theorem erdos920_of_bradacInput {k : ℕ} {γ : ℝ} (hk : 3 ≤ k) (hBr : BradacInput k γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C * ((n : ℝ) ^ (1 - ((k : ℝ) - 1)⁻¹) / Real.log (n : ℝ) ^ erdosExponent k)
        < (extremalChromaticNumber k n : ℝ) := by
  have h3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hd : (1 : ℝ) < (k : ℝ) - 1 := by linarith
  have hA : (0 : ℝ) ≤ 2 * (k : ℝ) - 4 := by linarith
  obtain ⟨C, hC, hbound⟩ :=
    general_transfer hBr.1 hd hA (le_refl 2) (ramseyLowerBound_of_bradacInput hk hBr)
  refine ⟨C, hC, ?_⟩
  have hexp : (2 * (k : ℝ) - 4) / ((k : ℝ) - 1) = erdosExponent k := by
    rw [erdosExponent]; ring_nf
  filter_upwards [hbound] with n hn
  rwa [transferGrowth, hexp] at hn

/-- Non-vacuity of Theorem 3.2: the function being bounded below does tend to
infinity, so the bound genuinely forces `f_k(n) → ∞` at the stated rate. -/
lemma tendsto_erdos920Growth_atTop {k : ℕ} (hk : 3 ≤ k) :
    Filter.Tendsto
      (fun n : ℕ => (n : ℝ) ^ (1 - ((k : ℝ) - 1)⁻¹) / Real.log (n : ℝ) ^ erdosExponent k)
      atTop atTop := by
  have h3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hd : (1 : ℝ) < (k : ℝ) - 1 := by linarith
  have hexp : (2 * (k : ℝ) - 4) / ((k : ℝ) - 1) = erdosExponent k := by
    rw [erdosExponent]; ring_nf
  have := tendsto_transferGrowth_atTop (A := 2 * (k : ℝ) - 4) hd
  simpa [transferGrowth, hexp] using this

/-! ### The statement of Problem 920 -/

/-- **Erdős Problem 920 — affirmative answer, with the constant exhibited.**

> Let `f_k(n)` be the maximum possible chromatic number of a graph with `n`
> vertices which contains no `K_k`.  Is it true that, for `k ≥ 4`,
> `f_k(n) ≫ n^(1 - 1/(k-1)) / (log n)^(c_k)` for some constant `c_k > 0`?

Yes, with `c_k = 2(k-2)/(k-1)`, given the Ramsey input `ExistsBradacInput k`.

The three conjuncts are, in order: `c_k > 0`; the lower bound
`f_k(n) ≥ C_k n^(1-1/(k-1)) / (log n)^(c_k)` for all large `n`; and non-vacuity,
namely that the right-hand side itself tends to infinity. -/
theorem erdos_problem_920_explicit {k : ℕ} (hk : 4 ≤ k) (hR : ExistsBradacInput k) :
    0 < erdosExponent k ∧
    (∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C * ((n : ℝ) ^ (1 - ((k : ℝ) - 1)⁻¹) / Real.log (n : ℝ) ^ erdosExponent k)
        < (extremalChromaticNumber k n : ℝ)) ∧
    Filter.Tendsto
      (fun n : ℕ => (n : ℝ) ^ (1 - ((k : ℝ) - 1)⁻¹) / Real.log (n : ℝ) ^ erdosExponent k)
      atTop atTop := by
  obtain ⟨γ, hγ⟩ := hR
  have hk3 : 3 ≤ k := by omega
  exact ⟨erdosExponent_pos hk3, erdos920_of_bradacInput hk3 hγ,
    tendsto_erdos920Growth_atTop hk3⟩

/-- **Erdős Problem 920 — affirmative answer, as asked.**

For every `k ≥ 4` there exist a constant `c_k > 0` and a constant `C_k > 0`
with `f_k(n) ≥ C_k · n^(1 - 1/(k-1)) / (log n)^(c_k)` for all sufficiently
large `n`, where `f_k(n) = extremalChromaticNumber k n` is the maximum
chromatic number of a `K_k`-free graph on `n` vertices. -/
theorem erdos_problem_920 {k : ℕ} (hk : 4 ≤ k) (hR : ExistsBradacInput k) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C * ((n : ℝ) ^ (1 - ((k : ℝ) - 1)⁻¹) / Real.log (n : ℝ) ^ c)
        < (extremalChromaticNumber k n : ℝ) := by
  obtain ⟨hc, hbound, -⟩ := erdos_problem_920_explicit hk hR
  exact ⟨erdosExponent k, hc, hbound⟩

/-- **Erdős Problem 920 in Landau notation**, matching the `≫` of the problem
statement: `n^(1 - 1/(k-1)) / (log n)^(c_k) = O(f_k(n))`. -/
theorem erdos_problem_920_isBigO {k : ℕ} (hk : 4 ≤ k) (hR : ExistsBradacInput k) :
    ∃ c : ℝ, 0 < c ∧
      (fun n : ℕ => (n : ℝ) ^ (1 - ((k : ℝ) - 1)⁻¹) / Real.log (n : ℝ) ^ c)
        =O[atTop] (fun n : ℕ => (extremalChromaticNumber k n : ℝ)) := by
  obtain ⟨γ, hγ⟩ := hR
  have hk3 : 3 ≤ k := by omega
  have h3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
  have hd : (1 : ℝ) < (k : ℝ) - 1 := by linarith
  have hA : (0 : ℝ) ≤ 2 * (k : ℝ) - 4 := by linarith
  have hexp : (2 * (k : ℝ) - 4) / ((k : ℝ) - 1) = erdosExponent k := by
    rw [erdosExponent]; ring_nf
  refine ⟨erdosExponent k, erdosExponent_pos hk3, ?_⟩
  have := general_transfer_isBigO hγ.1 hd hA (le_refl 2)
    (ramseyLowerBound_of_bradacInput hk3 hγ)
  simpa [transferGrowth, hexp] using this

/-! ### Consistency check at `k = 4`

The problem page records that Mattheus–Verstraete's `r(4,m) ≫ m^3/(log m)^4`
gives `f_4(n) ≫ n^(2/3)/(log n)^(4/3)`.  Specializing the theorem above to
`k = 4` reproduces exactly that: `1 - 1/(k-1) = 2/3` and `c_4 = 4/3`.  For
`k ≥ 5` the theorem is new at this exponent — the page notes that the route
through problem [986] yields only the weaker exponent `1 - 1/(k-2)`. -/

lemma erdosExponent_four : erdosExponent 4 = 4 / 3 := by
  rw [erdosExponent]; norm_num

theorem erdos920_k4 (hR : ExistsBradacInput 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C * ((n : ℝ) ^ ((2 : ℝ) / 3) / Real.log (n : ℝ) ^ ((4 : ℝ) / 3))
        < (extremalChromaticNumber 4 n : ℝ) := by
  obtain ⟨γ, hγ⟩ := hR
  obtain ⟨C, hC, hb⟩ := erdos920_of_bradacInput (k := 4) (by norm_num) hγ
  refine ⟨C, hC, ?_⟩
  have h1 : (1 : ℝ) - (((4 : ℕ) : ℝ) - 1)⁻¹ = 2 / 3 := by norm_num
  rw [h1, erdosExponent_four] at hb
  exact hb

end Erdos920

/-! ## Axiom audit

These commands are checked at compile time.  Each reports
`[propext, Classical.choice, Quot.sound]` — the three standard axioms of
mathlib — and nothing else.  In particular the Ramsey input appears as a
hypothesis of the theorems, not as an axiom, and there is no `sorry`. -/

#print axioms Erdos920.exists_extremal_graph
#print axioms Erdos920.finite_transfer
#print axioms Erdos920.general_transfer
#print axioms Erdos920.general_transfer_isBigO
#print axioms Erdos920.tendsto_transferGrowth_atTop
#print axioms Erdos920.ramseyLowerBound_of_bradacInput
#print axioms Erdos920.erdos920_of_bradacInput
#print axioms Erdos920.erdos_problem_920
#print axioms Erdos920.erdos_problem_920_explicit
#print axioms Erdos920.erdos_problem_920_isBigO
#print axioms Erdos920.erdos920_k4

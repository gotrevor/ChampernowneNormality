/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Champernowne.Main

/-!
# The Champernowne constant as a real number

`champernowne_normal` is a statement about the digit *sequence*
`champDigit b`.  This file upgrades it to the real number
`champReal b = 0.12345678910111213…₍b₎`: the digit map
`i ↦ ⌊b^(i+1)·x⌋ % b` applied to `champReal b` recovers `champDigit b`
exactly, so the real number itself is normal (`IsNormalReal`).

The bridge (`digitOf_tsum_digits`) is generic: any digit sequence with all
digits `< b` that is not eventually `b − 1` is recovered by the digit map
of the real number it sums to.  The Champernowne-specific input is
`champDigit_not_eventually_max`: past every position there is a digit
`≠ b − 1` (we exhibit a `0` inside the digit block of a large power of
`b`).
-/

/-- The `i`-th digit (0-indexed) of the standard base-`b` expansion of
`x ∈ [0,1)`: `⌊b^(i+1)·x⌋ mod b`.  (Total; junk values outside `[0,1)` —
normality of a real is always read through `Int.fract`.) -/
noncomputable def digitOf (b : ℕ) (x : ℝ) (i : ℕ) : ℕ :=
  (⌊x * (b : ℝ) ^ (i + 1)⌋).toNat % b

/-- A real number is **normal in base `b`** iff the digit sequence of its
fractional part is a normal sequence. -/
def IsNormalReal (b : ℕ) (x : ℝ) : Prop :=
  IsNormalSequence b (digitOf b (Int.fract x))

/-- The base-`b` Champernowne constant `0.12345678910111213…₍b₎`. -/
noncomputable def champReal (b : ℕ) : ℝ :=
  ∑' i, (champDigit b i : ℝ) / (b : ℝ) ^ (i + 1)

/-! ### The generic sequence → real bridge

Ported from `gotrevor/normal-numbers` (`NormalNumbers/Bridge.lean`,
Apache 2.0): the classical positional-expansion computation.  Writing
`F i = s i / b^(i+1)`, the series `∑ F` splits at every index into a
finite head (a natural number after scaling by `b^(i+1)`) plus a tail in
`[0, 1/b^(i+1))` — the *strict* upper bound is where properness enters,
via a termwise-strict comparison with `∑ (b−1)/b^(n+k+1) = 1/b^n`. -/

private theorem summable_digitTerm (b : ℕ) (hb : 2 ≤ b) (s : ℕ → ℕ)
    (hs : ∀ i, s i < b) :
    Summable (fun i : ℕ => (s i : ℝ) / (b : ℝ) ^ (i + 1)) := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := lt_trans zero_lt_one hb1
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    (summable_geometric_of_lt_one (r := (b : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hb1))
  rw [inv_pow, div_le_iff₀ (pow_pos hb0 (i + 1)), pow_succ,
    inv_mul_cancel_left₀ (pow_pos hb0 i).ne']
  exact_mod_cast (hs i).le

private theorem tail_term_eq (b : ℕ) (n k : ℕ) :
    ((b : ℝ) - 1) / (b : ℝ) ^ (k + n + 1)
      = (((b : ℝ) - 1) / (b : ℝ) ^ (n + 1)) * ((b : ℝ)⁻¹) ^ k := by
  rw [(by omega : k + n + 1 = n + 1 + k), pow_add, ← div_div, div_eq_mul_inv,
    inv_pow]

private theorem tsum_tail_geom (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    ∑' k : ℕ, ((b : ℝ) - 1) / (b : ℝ) ^ (k + n + 1) = 1 / (b : ℝ) ^ n := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := lt_trans zero_lt_one hb1
  have hbne : (b : ℝ) ≠ 0 := hb0.ne'
  have hbsubne : (b : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hb1.ne'
  have h1 : (1 : ℝ) - (b : ℝ)⁻¹ = ((b : ℝ) - 1) / (b : ℝ) := by
    rw [sub_div, div_self hbne, one_div]
  rw [tsum_congr (tail_term_eq b n), tsum_mul_left,
    tsum_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hb1),
    h1, inv_div, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hbne) hbsubne)
      (pow_ne_zero n hbne)]
  ring

private theorem tsum_tail_lt (b : ℕ) (hb : 2 ≤ b) (s : ℕ → ℕ)
    (hs : ∀ i, s i < b) (hp : ∀ N, ∃ i, N ≤ i ∧ s i ≠ b - 1) (n : ℕ) :
    ∑' k : ℕ, (s (k + n) : ℝ) / (b : ℝ) ^ (k + n + 1) < 1 / (b : ℝ) ^ n := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := lt_trans zero_lt_one hb1
  have hb1n : 1 ≤ b := by omega
  have hbsub : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
    rw [Nat.cast_sub hb1n, Nat.cast_one]
  obtain ⟨j, hjn, hj⟩ := hp n
  have hgsum : Summable (fun k : ℕ => ((b : ℝ) - 1) / (b : ℝ) ^ (k + n + 1)) := by
    refine Summable.congr ((summable_geometric_of_lt_one (r := (b : ℝ)⁻¹)
      (by positivity) (inv_lt_one_of_one_lt₀ hb1)).mul_left
        (((b : ℝ) - 1) / (b : ℝ) ^ (n + 1))) fun k => ?_
    exact (tail_term_eq b n k).symm
  have hle : ∀ k : ℕ, (s (k + n) : ℝ) / (b : ℝ) ^ (k + n + 1)
      ≤ ((b : ℝ) - 1) / (b : ℝ) ^ (k + n + 1) := by
    intro k
    have h1 : s (k + n) ≤ b - 1 := by have := hs (k + n); omega
    have h2 : (s (k + n) : ℝ) ≤ (b : ℝ) - 1 := by
      rw [← hbsub]; exact_mod_cast h1
    exact div_le_div_of_nonneg_right h2 (pow_pos hb0 _).le
  have hstrict : (s ((j - n) + n) : ℝ) / (b : ℝ) ^ ((j - n) + n + 1)
      < ((b : ℝ) - 1) / (b : ℝ) ^ ((j - n) + n + 1) := by
    have hjeq : (j - n) + n = j := by omega
    have h1 : s j < b - 1 := by have := hs j; omega
    have h2 : (s ((j - n) + n) : ℝ) < (b : ℝ) - 1 := by
      rw [hjeq, ← hbsub]; exact_mod_cast h1
    exact div_lt_div_of_pos_right h2 (pow_pos hb0 _)
  calc ∑' k : ℕ, (s (k + n) : ℝ) / (b : ℝ) ^ (k + n + 1)
      < ∑' k : ℕ, ((b : ℝ) - 1) / (b : ℝ) ^ (k + n + 1) :=
        Summable.tsum_lt_tsum_of_nonneg (fun k => by positivity) hle hstrict hgsum
    _ = 1 / (b : ℝ) ^ n := tsum_tail_geom b hb n

/-- The reals summed from a digit sequence lie in `[0, 1)` (properness
rules out the value `1`). -/
theorem tsum_digits_mem_Ico (b : ℕ) (hb : 2 ≤ b) (s : ℕ → ℕ)
    (hs : ∀ i, s i < b) (hp : ∀ N, ∃ i, N ≤ i ∧ s i ≠ b - 1) :
    (∑' i, (s i : ℝ) / (b : ℝ) ^ (i + 1)) ∈ Set.Ico (0 : ℝ) 1 := by
  rw [Set.mem_Ico]
  constructor
  · exact tsum_nonneg fun i => by positivity
  · have h := tsum_tail_lt b hb s hs hp 0
    simp only [Nat.add_zero, pow_zero, div_one] at h
    exact h

private theorem head_mul_pow (b : ℕ) (hb : 2 ≤ b) (s : ℕ → ℕ) (i : ℕ) :
    (∑ k ∈ Finset.range (i + 1), (s k : ℝ) / (b : ℝ) ^ (k + 1)) * (b : ℝ) ^ (i + 1)
      = ((∑ k ∈ Finset.range (i + 1), s k * b ^ (i - k) : ℕ) : ℝ) := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := lt_trans zero_lt_one hb1
  rw [Finset.sum_mul]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [div_mul_eq_mul_div, div_eq_iff (pow_pos hb0 (k + 1)).ne', mul_assoc,
    ← pow_add, (by omega : i - k + (k + 1) = i + 1)]

private theorem floor_tsum_digits_mul_pow (b : ℕ) (hb : 2 ≤ b) (s : ℕ → ℕ)
    (hs : ∀ i, s i < b) (hp : ∀ N, ∃ i, N ≤ i ∧ s i ≠ b - 1) (i : ℕ) :
    ⌊(∑' i, (s i : ℝ) / (b : ℝ) ^ (i + 1)) * (b : ℝ) ^ (i + 1)⌋
      = (∑ k ∈ Finset.range (i + 1), s k * b ^ (i - k) : ℕ) := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := lt_trans zero_lt_one hb1
  have hpowpos : (0 : ℝ) < (b : ℝ) ^ (i + 1) := pow_pos hb0 (i + 1)
  have hsum := summable_digitTerm b hb s hs
  have hx : (∑' i, (s i : ℝ) / (b : ℝ) ^ (i + 1))
      = (∑ k ∈ Finset.range (i + 1), (s k : ℝ) / (b : ℝ) ^ (k + 1))
        + ∑' k, (s (k + (i + 1)) : ℝ) / (b : ℝ) ^ (k + (i + 1) + 1) :=
    (hsum.sum_add_tsum_nat_add (i + 1)).symm
  have htail0 : (0 : ℝ) ≤ ∑' k, (s (k + (i + 1)) : ℝ) / (b : ℝ) ^ (k + (i + 1) + 1) :=
    tsum_nonneg fun k => by positivity
  have htail1 : ∑' k, (s (k + (i + 1)) : ℝ) / (b : ℝ) ^ (k + (i + 1) + 1)
      < 1 / (b : ℝ) ^ (i + 1) := tsum_tail_lt b hb s hs hp (i + 1)
  have key : (∑' i, (s i : ℝ) / (b : ℝ) ^ (i + 1)) * (b : ℝ) ^ (i + 1)
      = ((∑ k ∈ Finset.range (i + 1), s k * b ^ (i - k) : ℕ) : ℝ)
        + (∑' k, (s (k + (i + 1)) : ℝ) / (b : ℝ) ^ (k + (i + 1) + 1))
            * (b : ℝ) ^ (i + 1) := by
    rw [hx, add_mul, head_mul_pow b hb s i]
  have htail1' : (∑' k, (s (k + (i + 1)) : ℝ) / (b : ℝ) ^ (k + (i + 1) + 1))
      * (b : ℝ) ^ (i + 1) < 1 := by
    have := mul_lt_mul_of_pos_right htail1 hpowpos
    rwa [one_div, inv_mul_cancel₀ hpowpos.ne'] at this
  have htail0' : (0 : ℝ) ≤ (∑' k, (s (k + (i + 1)) : ℝ) / (b : ℝ) ^ (k + (i + 1) + 1))
      * (b : ℝ) ^ (i + 1) := mul_nonneg htail0 hpowpos.le
  rw [Int.floor_eq_iff]
  constructor
  · rw [key]; push_cast; linarith
  · rw [key]; push_cast; linarith

/-- **The bridge**: the digit map inverts digit summation on sequences
that are not eventually `b − 1`. -/
theorem digitOf_tsum_digits (b : ℕ) (hb : 2 ≤ b) (s : ℕ → ℕ)
    (hs : ∀ i, s i < b) (hp : ∀ N, ∃ i, N ≤ i ∧ s i ≠ b - 1) :
    digitOf b (∑' i, (s i : ℝ) / (b : ℝ) ^ (i + 1)) = s := by
  funext i
  show (⌊(∑' i, (s i : ℝ) / (b : ℝ) ^ (i + 1)) * (b : ℝ) ^ (i + 1)⌋).toNat % b = s i
  rw [floor_tsum_digits_mul_pow b hb s hs hp i, Int.toNat_natCast,
    Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
  have hdvd : b ∣ ∑ k ∈ Finset.range i, s k * b ^ (i - k) := by
    refine Finset.dvd_sum fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [(by omega : i - k = (i - k - 1) + 1), pow_succ, ← mul_assoc]
    exact dvd_mul_left b _
  obtain ⟨m, hm⟩ := hdvd
  rw [hm, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (hs i)

/-! ### Champernowne-specific facts -/

/-- Every digit of the Champernowne sequence is a base-`b` digit. -/
theorem champDigit_lt {b : ℕ} (hb : 1 < b) (i : ℕ) : champDigit b i < b := by
  have hmem : champDigit b i ∈ champBlocks b (i + 1) := by
    unfold champDigit
    exact List.getElem_mem _
  rw [champBlocks] at hmem
  obtain ⟨l, hl, hd⟩ := List.mem_flatten.mp hmem
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp hl
  rw [bigDigits, List.mem_reverse] at hd
  exact Nat.digits_lt_base hb hd

/-- The digit at offset `j` inside the block of the number `n + 1`. -/
theorem champDigit_block (b n j : ℕ) (hj : j < (bigDigits b (n + 1)).length) :
    champDigit b ((champBlocks b n).length + j) = (bigDigits b (n + 1))[j] := by
  have hlen : (champBlocks b n).length + j < (champBlocks b (n + 1)).length := by
    rw [champBlocks_succ, List.length_append]
    omega
  rw [← champBlocks_getElem b (n + 1) _ hlen]
  simp only [champBlocks_succ]
  rw [List.getElem_append_right (by omega)]
  congr 1
  omega

/-- Big-endian digits of `b ^ k`: a leading `1` then `k` zeros. -/
theorem bigDigits_base_pow {b : ℕ} (hb : 1 < b) (k : ℕ) :
    bigDigits b (b ^ k) = 1 :: List.replicate k 0 := by
  have h1 : Nat.digits b 1 = [1] := by
    rw [Nat.digits_def' hb Nat.one_pos]
    simp [Nat.mod_eq_of_lt hb, Nat.div_eq_of_lt hb]
  have h : Nat.digits b (b ^ k) = List.replicate k 0 ++ [1] := by
    have := Nat.digits_base_pow_mul (b := b) (k := k) (m := 1) hb Nat.one_pos
    simpa [h1] using this
  rw [bigDigits, h]
  simp [List.reverse_replicate]

/-- **Properness**: past every position, the Champernowne sequence has a
digit `≠ b − 1` (a `0` inside the digit block of a large power of `b`). -/
theorem champDigit_not_eventually_max {b : ℕ} (hb : 1 < b) (N : ℕ) :
    ∃ i, N ≤ i ∧ champDigit b i ≠ b - 1 := by
  set k := N + 1 with hk
  have hpow : N + 1 < b ^ k := by
    calc N + 1 < 2 ^ (N + 1) := Nat.lt_two_pow_self
    _ ≤ b ^ k := Nat.pow_le_pow_left hb (by omega)
  set n := b ^ k - 1 with hn
  have hn1 : n + 1 = b ^ k := Nat.succ_pred_eq_of_pos (pow_pos (by omega) k)
  have hjlen : 1 < (bigDigits b (n + 1)).length := by
    rw [hn1, bigDigits_base_pow hb]
    simp only [List.length_cons, List.length_replicate]
    omega
  refine ⟨(champBlocks b n).length + 1, ?_, ?_⟩
  · have hlb := le_length_champBlocks b n
    omega
  · have hblock := champDigit_block b n 1 hjlen
    have hval : (bigDigits b (n + 1))[1]'hjlen = 0 := by
      have hlist : bigDigits b (n + 1) = 1 :: List.replicate k 0 := by
        rw [hn1, bigDigits_base_pow hb]
      simp only [hlist, List.getElem_cons_succ, List.getElem_replicate]
    rw [hblock, hval]
    omega

/-! ### Main results -/

/-- The digit map recovers the Champernowne sequence from the
Champernowne constant. -/
theorem digitOf_champReal (b : ℕ) (hb : 2 ≤ b) :
    digitOf b (champReal b) = champDigit b :=
  digitOf_tsum_digits b hb (champDigit b) (champDigit_lt (by omega))
    (champDigit_not_eventually_max (by omega))

theorem champReal_mem_Ico (b : ℕ) (hb : 2 ≤ b) :
    champReal b ∈ Set.Ico (0 : ℝ) 1 :=
  tsum_digits_mem_Ico b hb (champDigit b) (champDigit_lt (by omega))
    (champDigit_not_eventually_max (by omega))

/-- **Champernowne's theorem, for the real number**: the base-`b`
Champernowne constant is normal in base `b`. -/
theorem champernowne_real_normal (b : ℕ) (hb : 2 ≤ b) :
    IsNormalReal b (champReal b) := by
  have hx := champReal_mem_Ico b hb
  rw [IsNormalReal, Int.fract_eq_self.mpr ⟨hx.1, hx.2⟩, digitOf_champReal b hb]
  exact champernowne_normal b hb

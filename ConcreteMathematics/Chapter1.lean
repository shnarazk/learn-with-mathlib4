module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic
public import Basic.Finset

/-!
# 1章 再帰問題
-/

/-!
## 1.1 The Tower of Hanoi
-/
section Section1

/-- 最初に再帰により枚数`n`に対する手数を与える。 -/
@[grind =]
def t (n : ℕ) : ℕ :=
  match n with
  | 0    => 0
  | n'+1 => 2 * t n' + 1

#guard t 4 = 15
#guard t 6 = 63

/-- `t`を再帰を使わずに _closed form_ として表現 -/
@[simp]
theorem Equation1_2 : ∀ n : ℕ, t n = 2 ^ n - 1 := by
  intro n
  induction n with
  | zero       => rfl
  | succ n' ih => grind

/-! 新たな関数を導入してより簡潔に表現する -/

@[simp]
def U (n : ℕ) : ℕ := t n + 1

/-- `Equation1_2`の別表現 -/
theorem Equation1_2' : ∀ n : ℕ, U n = 2 ^ n := by
  intro n
  simp
  grind

end Section1

/-!
## 1.2 Lines in the plane
平面上に引かれた直線群による空間の分割数に関する問題
-/
section Section2

/--
`L`を直線数`n`に対する分割数を返す関数とする。上限は以下で与えられる。
$∀ n >0, L (n + 1) ≤ L n + n$
これを基に定義する。
-/
@[grind =, simp]
def l (n : ℕ) : ℕ :=
  match n with
  | 0    => 1
  | n'+1 => l n' + n

/-! Lの closed formを求めるために補助関数を前もって定義する。 -/
@[grind =, simp]
def sum (n : ℕ) : ℕ := ∑ i ≤ n, i

#guard sum 0 = 0
#guard sum 1 = 1
#guard sum 9 = 45

/-! `sum`を使った`L`のclosed form -/
@[grind =, simp]
theorem ClosedFormOfL': ∀ n : ℕ, l n = 1 + sum n := by
  intro n
  induction n with
  | zero       => simp [sum]
  | succ n' ih => simp [ih] ; grind

/-! 1.6 最終的な`L`のclosed form -/
theorem ClosedFormOfL: ∀ n : ℕ, l n = n * (n + 1) / 2 + 1 := by
  intro n
  have n_pow2_ge_self : n * n ≥ n := Nat.le_mul_self n
  rw [ClosedFormOfL']
  rewrite (occs := .pos [2]) [add_comm]
  refine Nat.add_left_cancel_iff.mpr ?_
  rw [sum]
  have : ∑ i ≤ n, i = ∑ i < n + 1, i := by
    exact Finset.sum_sdiff_eq_sum_sdiff_iff.mp rfl
  simp [this]
  rw [← sum_of_range_eq_sum_of_lt (·)]
  rw [Finset.sum_range_id]
  replace : n = (2 * n) / 2 := by
    refine Nat.eq_div_of_mul_eq_right ?_ rfl
    · exact Ne.symm (Nat.zero_ne_add_one 1)
  rw (occs := .pos [3]) [this]
  refine Nat.eq_div_of_mul_eq_right ?_ ?_
  · exact Ne.symm (Nat.zero_ne_add_one 1)
  · rw [mul_add]
    replace : 2 * ((n * (n - 1)) / 2) = n * (n - 1) := by
      exact Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
    rw [this]
    replace : 2 * ((2 * n) / 2) = 2 * n := by
      exact Nat.two_mul_div_two_of_even (even_two_mul n)
    rw [this]
    replace : n * (n - 1) = n * n - n := by
      exact Nat.mul_sub_one n n
    rw [this]
    replace : n * n - n + 2 * n = n * n + n := by
      rw (occs := .pos [1]) [two_mul]
      refine Eq.symm ((fun {b a c} h ↦ (Nat.sub_eq_iff_eq_add h).mp) ?_ ?_)
      · exact Nat.add_le_add_iff_right.mpr n_pow2_ge_self
      · exact Nat.add_sub_add_right (n * n) n n
    rw [this]
    exact Eq.symm (Nat.mul_succ n n)

/-!
次に1回折れた"直線"を考える。
-/

/-- 1.7 -/
@[grind =, simp]
def z (n : ℕ) := l (2 * n) - 2 * n

/-- 1.7 後半 -/
theorem equation_1_7 : ∀ n : ℕ, z n = 2 * n ^ 2 - n + 1 := by
  intro n
  induction n with
  | zero      => rfl
  | succ n ih => rw [z, ClosedFormOfL] ; grind

end Section2

/-!
## 1.3 The Josephus Problem
-/
section Section3

/-!
- `j` 参加人数`n`に対する生存者番号
- 定義域は `n ≥ 1`  なので `j 0 = 0`と置くことにした。
-/
@[grind =, simp]
def j (n : ℕ) : ℕ :=
  match h : n with
  | 0    => 0
  | 1    => 1
  | n'+2 =>
    if Even n then 2 * j (n / 2) - 1 else 2 * j (n / 2) + 1
decreasing_by
  · expose_names
    rw [←h]
    exact Nat.div_lt_self (Nat.lt_of_sub_eq_sub_one h) (by grind)
  · expose_names
    rw [←h]
    exact Nat.div_lt_self (Nat.lt_of_sub_eq_sub_one h) (by grind)

#guard j 1 = 1
#guard j 2 = 1
#guard j 3 = 3
#guard j 14 = 13

/-- `j`のclosed formを与える -/
theorem equation_1_9 :
    ∀ m : ℕ, ∀ l < 2 ^ m, j (2 ^ m + l) = 2 * l + 1 := by
  intro m l pl
  induction m using Nat.strongRecOn generalizing l with
  | ind m ih' =>
    match m, ih' with
    | 0   , _  => simp at pl ; simp [pl]
    | m'+1, ih =>
      clear ih'
      rw [j.eq_def]
      split
      · grind
      · grind
      · expose_names
        split <;> {
          have : (2 ^ (m'+1) + l) / 2 = 2 ^ m' + l / 2 := by
            grind
          replace ih := ih m' (by grind) (l / 2) (by grind)
          grind }

/-- jが不動点を持つことを言うための準備 -/
lemma lemma_1 : ∀ n : ℕ, j n ≤ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind m ih' =>
    rw [j.eq_def]
    split
    · exact Nat.zero_le 0
    · exact NeZero.one_le
    · expose_names
      simp at *
      by_cases h : Even (n' + 1 + 1) <;> {
        simp [h]
        have : (n' + 1 + 1) / 2 ≤ n' + 1 := by
          refine Nat.div_two_le_of_sub_le_div_two ?_
          · simp ; grind
        grind }

/-- jは不動点を持つ -/
lemma j_has_a_fixpoint: ∀ n : ℕ, ∃ n' ≤ n, j n' = n' := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have from_lemma_1 : j n ≤ n := by exact lemma_1 n
    replace from_lemma_1 : j n < n ∨ j n = n := by
      exact Or.symm (Nat.eq_or_lt_of_le from_lemma_1)
    rcases from_lemma_1 with a|b
    · grind
    · use n

end Section3

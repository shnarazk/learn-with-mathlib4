module

public import Init.Control.State
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Bits
public import Mathlib.Tactic
public import Basic.Finset
public import Basic.Bits

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

/-!
## Relations in binary representation
-/

/-
実はjは一種のbit列のシフト関数になっている。ここでLuby関数が頭をよぎる。
- n = 2 ^ m + l → nの最上位bitをクリアしたものがl
-/

#guard (j (2 ^ 4 + 6)).bits = true :: (6 : ℕ).bits
#guard (j (2 ^ 4 + 1)).bits = true :: (1 : ℕ).bits
#guard (j (2 ^ 5 + 3)).bits = true :: (3 : ℕ).bits

open Nat
@[grind =, simp]
theorem even_bits : ∀ n > 1, (2 * (n / 2)).bits = false :: (n / 2).bits := by
  intro n n_gt_1
  exact Nat.bit0_bits (n / 2) (by grind)

@[grind =, simp]
theorem odd_bits : ∀ n > 1, (2 * (n / 2) + 1).bits = true :: (n / 2).bits := by
  intro n n_gt_1
  exact Nat.bit1_bits (n / 2)

/-- 補助定理
- n - 1 = 1 は`[true, false]` になれないので、 n = 2 は範囲外。 -/
theorem b10_sub_1_eq_b10 : ∀ n ≥ 4, ∀ l : List Bool,
  n.bits = false :: true :: l → (n - 1).bits = true :: false :: l := by
  intro n n_ge_4 l p
  have n_is_even : Even n := by
    exact (bit0_eq_false_iff_even (by grind)).mp (by grind)
  have base4 : (2 * (n / 4)).bits = false :: (n / 4).bits := by
    exact bit0_bits (n / 4) (by grind)
  have base : (2 * (2 * (n / 4)) + 1).bits = true :: (false :: (n / 4).bits) := by
    rw [← base4]
    exact bit1_bits (2 * (n / 4))
  have dec : (2 * (2 * (n / 4))).bits = false :: (false :: (n / 4).bits) := by
    rw [← base4]
    exact bit0_bits (2 * (n / 4)) (by grind)
  have : 4 * (n / 4) + 2 = n := by grind
  replace this : 2 * (2 * (n / 4)) + 1 = n - 1 := by grind
  have l_def : (n / 4).bits = l := by
    have n_def : 2 * (2 * (n / 4)) + 2 = n := by grind
    rw [← n_def] at p
    have calc1 : 2 * (2 * (n / 4)) + 2 = 2 * (2 * (n / 4) + 1) := by grind
    simp [calc1] at p
    grind
  rw [← this]
  grind

/-- これはちょっと無理。Nat.Bitsの表現は上位のfalseを保持できないので等価判定の拡大が必要。 -/
example : ∀ m : ℕ, ∀ l < 2 ^ m,
    (j (2 ^ m + l)).bits = true :: l.bits := by
  intro m l lm
  induction m using Nat.strongRecOn generalizing l with
  | ind m ih' =>
    rw [j.eq_def]
    split <;> expose_names
    · grind
    · have p1 : 2 ^ m ≥ 1 := by grind
      have p2 : l = 0 := by grind
      simp [p2]
    · simp at *
      by_cases even : Even (2 ^ m + l)
      · simp [even]
        have : (2 ^ m + l) / 2 = 2 ^ (m - 1) + l / 2 := by
          refine Eq.symm (Nat.eq_div_of_mul_eq_right ?_ ?_)
          · grind
          · rw [mul_add]
            have : 2 * 2 ^ (m - 1) = 2 ^ m := by
              exact mul_pow_sub_one (by grind) 2
            simp [this]
            refine Nat.mul_div_cancel' ?_
            · replace this : Even l := by grind
              exact Even.two_dvd this
        rw [this]
        have m_gt_0 : m > 0 := by grind
        have even_l : Even l := by grind
        replace ih' := ih' (m - 1) (by grind) (l / 2) (by grind)
        by_cases l_eq_0 : l = 0
        · simp [l_eq_0] at *
          have bit1 : (1 : Nat).bits = [true] := by simp
          rw [← bit1] at ih'
          replace ih' : j (2 ^ (m - 1)) = 1 := by sorry
          simp [ih']
        have x : (2 * (l / 2)).bits = false :: (l / 2).bits := by
          exact Nat.bit0_bits (l / 2) (by grind)
        replace ih' : (2 * j (2 ^ (m - 1) + l / 2)).bits = false :: true :: (l / 2).bits := by
          have : (2 * j (2 ^ (m - 1) + l / 2)).bits = false :: (j (2 ^ (m - 1) + l / 2)).bits := by
            refine Nat.bit0_bits ?_ ?_
            · have s1 : ¬(j (2 ^ (m - 1) + l / 2)).bits = [] := by simp [ih']
              exact Ne.symm (ne_of_apply_ne Nat.bits fun a ↦ s1 (id (Eq.symm a)))
          grind
        have : (2 * j (2 ^ (m - 1) + l / 2) - 1).bits = true :: false :: (l / 2).bits := by
          refine b10_sub_1_eq_b10 (2 * j (2 ^ (m - 1) + l / 2)) ?_ (l / 2).bits ih'
          · sorry
        grind
      · sorry

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

/-!
It’s not hard to verify that 2 ^ m − 2 is a multiple of 3 when m is odd, but not when m is even.
-/
#guard 3 ∣ (2 ^ 3 - 2)
#guard 3 ∣ (2 ^ 5 - 2)

theorem three_dvd_two_pow_odd_sub_two : ∀ m : ℕ, Odd m → 3 ∣ (2 ^ m - 2) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m =>
    by_cases m_range : m = 0
    · simp [m_range] at *
    · replace m_range : m ≥ 1 := by grind
      replace m_range : m = 1 ∨ m > 1 := by grind
      rcases m_range with ⟨m_eq_1, m_gt_1⟩ <;> expose_names
      · intro odd
        grind
      · intro odd
        have : m = m - 2 + 2 := by grind
        rw [this]
        replace this : 2 ^ (m - 2 + 2) =  2 ^ (m - 2) * 2 ^ 2 := by
          grind
        rw [this]
        change 3 ∣ (2 ^ (m - 2) * 3 + 2 ^ (m - 2) - 2)
        have sub:
          2 ^ (m - 2) * 3 + 2 ^ (m - 2) - 2
            = 2 ^ (m - 2) * 3 + (2 ^ (m - 2) - 2) := by
          refine Nat.add_sub_assoc ?_ (2 ^ (m - 2) * 3)
          · have m_ge_2 : m ≥ 2 := by grind
            replace m_ge_2 : m = 2 ∨ m > 2 := by grind
            rcases m_ge_2 with ⟨eq, gt⟩
            · contradiction
            · grind
        rw [sub]
        have mul3 : 3 ∣ (2 ^ (m - 2) * 3) := by grind
        have rule (x a : ℕ) : 3 ∣ a → 3 ∣ (x * 3 + a) := by
          grind
        apply rule
        replace h := h (m - 2) (by grind) (by grind)
        exact h
/-!
# 一般化

このような関数を一般化した場合に対するclosed formの求め方を考える。
-/

/-- jを一般化するため変数α, β, γを使って対象の関数をfとして定義する。 -/
@[grind =, simp]
def f (n : Nat) (α β γ : Int) : Int :=
  if h : n ≤ 1
  then α
  else 2 * f (n / 2) α β γ + if Even n then β else γ

/-! α = 1, β = γ = 0 を例にとる。 -/
#guard f 1 1 0 0= 1
#guard f 4 1 0 0 = 2 * f 2 1 0 0

/-!
- f n = α * A n + β * B n + γ * C n
として、関数A, B, Cを求めればよい。
-/

/--
仮に f _ ... = 1 ならこれらの制約が抽出される。-/
lemma f1_eq_1_leads_to {α β γ : ℤ} :
    (∀ n, f n α β γ = 1) → α = 1 ∧ β = -1 ∧ γ = -1 := by
  intro fn
  have alpha : α =  1 := by replace fn := fn 1 ; grind
  have beta  : β = -1 := by replace fn := fn 2 ; grind
  have gamma : γ = -1 := by replace fn := fn 3 ; grind
  grind

/--
次に f n ... = n ならこれらの制約が抽出される。-/
lemma fn_eq_n_leads_to {α β γ : ℤ} :
    (∀ n, f n α β γ = n) → α = 1 ∧ β = 0 ∧ γ = 1 := by
  intro fn
  have alpha : α = 1 := by replace fn := fn 1 ; grind
  have beta  : β = 0 := by replace fn := fn 2 ; grind
  have gamma : γ = 1 := by replace fn := fn 3 ; grind
  grind

/-!
従って、
- f₁ = 1 = A - B - C
- fₙ = n = A + C
- A n = 2 ^ m -- これがどこからきたのか？
以上からfが求まる。
-/

/-!
## 3進数での例：計算のみ
-/

def g (n : ℕ) : ℤ :=
  if n ≤ 1 then 3
  else if n = 2 then 5
  else if 3 ∣ n       then 10 * g (n / 3) + 76
  else if 3 ∣ (n - 1) then 10 * g (n / 3) - 2
  else                     10 * g (n / 3) + 8

#guard g 19 = 1258

example : g 19 = g (2 * 3 ^ 2 + 0 * 3 ^ 1 + 1 * 3 ^ 0) := by
  simp

/-!
(2 0 1)₃ => (5 76 -2)₁₀
-/
example : g 19 = 5 * 10 ^ 2 + 76 * 10 ^ 1 + (-2) * 10 ^ 0 := by
  simp [g]

/-!
# Exercises

## Warmups

1. Analysis Iにも出てきた間違った帰納法の問題

2.
- f n a c := f (n - 1) a b ; f 1 a c ; f (n - 1) b c
a ↔ c が禁止されているなら
を以下に変更
- f n a c := f (n - 1) a b ; f (n - 1) b c ; f 1 a b ; f (n - 1) c a ; f 1 b c ; f (n - 1) a b ; f (n - 1) b c
-/

abbrev Hand := (ℕ × ℕ × ℕ)

partial def hanoi' (dishes : ℕ) (f t o : ℕ) : (StateT (List Hand) (Except String)) (List Hand) := do
  if dishes = 1 then
    modify (· ++ [(1, f, t)])
    get
  else
  let _ ← hanoi' (dishes - 1) f o t
  modify (· ++ [(dishes, f, t)])
  let _ ← hanoi' (dishes - 1) o t f
  get

#eval hanoi' 3 0 2 1 |>.run' []

end Section3

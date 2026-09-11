module

public import Mathlib.Tactic

namespace Chapter2

/-!
# [Section 2.1 The Peano Axioms](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_1.lean)
-/

section section_02_1

/--
我々の自然数の定義
-/
public inductive Nat where
| zero : Nat
| succ : Nat → Nat
deriving Repr, DecidableEq

postfix:100 "++" => Nat.succ

/-!
## Peano's axioms

 1. 0 ∈ ℕ
 2. n ∈ ℕ → n++ ∈ ℕ
 3. ∀ n ∈ ℕ, n++ ≠ 0
 4. ∀ n, m ∈ ℕ, n ≠ m → n++ ≠ m++
 5. ∀ P ∈ (ℕ → Prop), P 0 ∧ (∀ n ∈ ℕ, P n → P n++) → ∀ n ∈ ℕ, P n

5から 無限 は ℕ に含まれないことが言える。
-/

/-- Zero は 0を与える型クラス -/
instance Nat.instZero : Zero Nat := ⟨ zero ⟩

#guard (0 : Nat) = Nat.zero

/-- OfNatで`_root_.Nat`からのparserを提供する　-/
instance Nat.instOfNat {n:_root_.Nat} : OfNat Nat n where
  ofNat := _root_.Nat.rec 0 (fun _ n ↦ n++) n

#guard (1 : Nat) = Nat.succ Nat.zero

/-- One は 1を与える型クラス -/
instance Nat.instOne : One Nat := ⟨ 1 ⟩

/--
Axiom 2.3: ∀ n ∈ ℕ, n++ ≠ 0
-/
theorem Nat.succ_ne (n : Nat) : n++ ≠ 0 := by
  by_contra h -- n++ = zero と仮定
  injection h -- 両辺のconstructorが同じであることを確認

theorem Nat.four_ne : (4 : Nat) ≠ 0 := by
  change 3++ ≠ 0 -- goalを変更
  exact succ_ne _

/-- 頻出する再帰の処理のパターン化
- f: Natをふたつ引数に取る
- c: base caseで使われるNat
- 返値: Nat → Nat(全域関数)
-/
@[simp]
public abbrev Nat.recurse (f: Nat → Nat → Nat) (c: Nat) : Nat → Nat :=
  fun n ↦ match n with
  | zero => c
  | n++  => f n (recurse f c n)

end section_02_1

/-!
# [Section 2.2 Addition](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/

section section_02_2

/-- 加算(+)を定義 -/
@[grind =, simp]
public abbrev Nat.add (n m : Nat) : Nat := Nat.recurse (fun _ sum ↦ sum++) m n

/-- addの第1引数fはmによらないことからこう簡略化できる。 -/
public def Nat.add' (n m : Nat) : Nat :=
  match n with
  | zero => m                     -- 0 + m = 0
  | n'++ => (·++) (Nat.add' n' m) -- n'++ + m = (n' + m)++

/-- 記法(+)を導入 -/
@[grind =, simp]
instance Nat.instAdd : Add Nat where add := Nat.add

#guard Nat.add (1 : Nat) (3 : Nat) = (4 : Nat)
#guard (1 : Nat) + (3 : Nat) = (4 : Nat)

example : ∀ n m : Nat, ((n + m) : Nat) = Nat.add n m := by
  solve_by_elim

#guard Nat.add (5 : Nat) (2 : Nat) = (7 : Nat)

/-- 0は(+)の単位元 -/
lemma lemma_2_2_2 : ∀ n : Nat, n + 0 = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n' ih =>
    -- ここでgrindは無力
    exact cast (congrArg (Eq (n'++ + 0)) (congrArg Nat.succ ih)) rfl

/-- (++)と`Nat.add`の交換 -/
lemma lemma_2_2_3' : ∀ n m : Nat, Nat.add n (m++) = (Nat.add n m)++ := by
  intro n m
  induction n generalizing m with
  | zero      => rfl   -- 0 + (m++) = m++ ∧ 0 + m = m → m++ = 0
  | succ n ih => grind -- ih: n + (m++) = (n + m)++

/--
(++)と(+)の交換
- なぜか直接解くのは大変だった。Nat.instAddが思うように使われない。 -/
@[grind =, simp]
lemma lemma_2_2_3 : ∀ n m : Nat, n + (m++) = (n + m)++ := by
  intro n m
  exact lemma_2_2_3' n m

/-! As a paricular corollary of Lemma 2.2.2 and Lemma 2.2.3 -/
example : ∀ n : Nat, n++ = n + 1 := by
  intro n
  have : n = n + 0 := by exact Eq.symm (lemma_2_2_2 n)
  rw (occs := .pos [1]) [this]
  rw [← lemma_2_2_3 n]
  replace : 0++ = 1 := by rfl
  simp [this]

end section_02_2

end Chapter2

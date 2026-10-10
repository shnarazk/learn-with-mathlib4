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

@[grind =, simp]
lemma zero_eq_0 : Nat.zero = (0 : Nat) := by
  exact (MulOpposite.op_eq_zero_iff Nat.zero).mp rfl

/-- OfNatで`_root_.Nat`からのparserを提供する　-/
instance Nat.instOfNat {n:_root_.Nat} : OfNat Nat n where
  ofNat := _root_.Nat.rec 0 (fun _ n ↦ n++) n

#guard (1 : Nat) = Nat.succ Nat.zero

/-- One は 1を与える型クラス -/
instance Nat.instOne : One Nat := ⟨ 1 ⟩

lemma Nat.zero_succ : 0++ = 1 := by rfl
lemma Nat.one_succ  : 1++ = 2 := by rfl
lemma Nat.two_succ  : 2++ = 3 := by rfl

/--
Axiom 2.3: ∀ n ∈ ℕ, n++ ≠ 0
-/
theorem Nat.succ_ne (n : Nat) : n++ ≠ 0 := by
  by_contra h -- n++ = zero と仮定
  injection h -- 両辺のconstructorが同じであることを確認

example : (4 : Nat) ≠ 0 := by
  change 3++ ≠ 0 -- goalを変更
  exact Nat.succ_ne _

/-- Axiom 2.5 (Principle of mathematical induction). The {tactic}`induction` (or
  {tactic}`induction'`) tactic in Mathlib serves as a substitute for this axiom.  -/
theorem Nat.induction (P : Nat → Prop) (hbase : P 0) (hind : ∀ n, P n → P (n++)) :
    ∀ n, P n := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih => exact hind _ ih

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

/-- Proposition 2.1.16 (recursive definitions). Compare with Mathlib's {name}`Nat.rec_zero`. -/
theorem Nat.recurse_zero (f: Nat → Nat → Nat) (c: Nat) : Nat.recurse f c 0 = c := by rfl

/-- Proposition 2.1.16 (recursive definitions). Compare with Mathlib's {name}`Nat.rec_add_one`. -/
theorem Nat.recurse_succ (f: Nat → Nat → Nat) (c: Nat) (n: Nat) :
    recurse f c (n++) = f n (recurse f c n) := by rfl

/-- Proposition 2.1.16 (recursive definitions). -/
theorem Nat.eq_recurse (f: Nat → Nat → Nat) (c: Nat) (a: Nat → Nat) :
    (a 0 = c ∧ ∀ n, a (n++) = f n (a n)) ↔ a = recurse f c := by
  constructor
  . intro ⟨ h0, hsucc ⟩
    -- this proof is written to follow the structure of the original text.
    apply funext; apply induction
    . exact h0
    intro n hn
    rw [hsucc n, recurse_succ, hn]
  intro h
  rw [h]
  constructor -- could also use `split_ands` or `and_intros` here
  . exact recurse_zero _ _
  exact recurse_succ _ _

/-- Proposition 2.1.16 (recursive definitions). -/
theorem Nat.recurse_uniq (f: Nat → Nat → Nat) (c: Nat) :
    ∃! (a: Nat → Nat), a 0 = c ∧ ∀ n, a (n++) = f n (a n) := by
  apply ExistsUnique.intro (recurse f c)
  . constructor -- could also use `split_ands` or `and_intros` here
    . exact recurse_zero _ _
    . exact recurse_succ _ _
  intro a
  exact (eq_recurse _ _ a).mp

theorem Nat.axiom_4 {a b : Nat} : a ≠ b → a++ ≠ b++ := by
  intro a_ne_b
  by_contra
  injection this
  grind

theorem Nat.axiom_4' {a b : Nat} : a++ = b++ → a = b := by
  intro a1_eq_b1
  by_contra
  apply Nat.axiom_4 at this
  grind

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
@[grind =, simp]
lemma lemma_2_2_2 : ∀ n : Nat, n + 0 = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n' ih =>
    -- ここでgrindは無力
    exact cast (congrArg (Eq (n'++ + 0)) (congrArg Nat.succ ih)) rfl

/-- Compare with Mathlib's {name}`Nat.zero_add`. -/
@[simp]
theorem Nat.zero_add (m: Nat) : 0 + m = m := recurse_zero (fun _ sum ↦ sum++) _

/-- (++)と`Nat.add`の交換 -/
@[grind =, simp]
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
@[grind =, simp]
lemma add1_is_inc : ∀ n : Nat, n + 1 = n++ := by
  intro n
  have : n = n + 0 := by exact Eq.symm (lemma_2_2_2 n)
  rw (occs := .pos [2]) [this]
  rw [← lemma_2_2_3]
  replace : 0++ = 1 := by rfl
  grind

/--
Addition is commutative
-/
@[grind =, simp]
lemma proposition_2_2_4 : ∀ n m : Nat, n + m = m + n := by
  intro n m
  induction n with
  | zero      =>
    change 0 + m = m + 0
    simp [lemma_2_2_2]
  | succ n ih =>
    rw (occs := .pos [1]) [lemma_2_2_3]
    rw [← ih]
    change Nat.add (n++) m = (n + m)++;
    rw [Nat.add.eq_def (n++) m] -- なぜ記法の変換に1 step取られるのだろう
    simp [Nat.recurse]
    rw [← Nat.add.eq_def n m]
    change n + m = n + m
    rfl

/--
Addition is associative
-/
@[grind =, simp]
lemma proposition_2_2_5 {a b c : Nat} : (a + b) + c = a + (b + c) := by
  induction c with
  | zero      =>
    change (a + b) + 0 = a + (b + 0)
    simp
  | succ c ih =>
    have : (a + b) + c++ = (a + b + c)++ := by
      exact lemma_2_2_3 (a + b) c
    rw (occs := .pos [1]) [this]
    rw [lemma_2_2_3]
    rw [lemma_2_2_3]
    rw [← ih]

/-- 加算の右キャンセル -/
lemma proposition_2_2_6 {a b c : Nat} : a + b = a + c → b = c := by
  induction a with
  | zero => intro h ; grind
  | succ a ih =>
    intro h
    replace h : a + b + 1 = a + c + 1 := by grind
    replace h : (a + b)++ = (a + c)++ := by
      have ab : a + b + 1 = (a + b)++ := by grind
      rw [← ab]
      have ac : a + c + 1 = (a + c)++ := by grind
      rw [← ac]
      grind
    replace h : a + b = a + c := by grind
    replace ih := ih h
    grind

/-- 加算の右キャンセル -/
lemma proposition_2_2_6' {a b : Nat} : a = b → ∀ c, a + c = b + c := by
  intro a_eq_b c
  simp [a_eq_b]

/-- Proposition 2.2.7: 正数の定義 -/
@[grind =, simp]
def Nat.IsPos : Nat → Prop := fun n ↦ n ≠ 0

lemma proposition_2_2_8 {a b : Nat} : Nat.IsPos a → Nat.IsPos (a + b) := by
  intro a_is_positive
  induction b with
  | zero => grind
  | succ b ih =>
    have : (a + b)++ ≠ 0 := by exact Nat.succ_ne (a + b)
    grind

lemma corollary_2_2_9 {a b : Nat} : a + b = 0 → a = 0 ∧ b = 0 := by
  intro ab0
  by_contra h
  simp at h
  by_cases a0 : a = 0
  · simp [a0] at ab0
    replace h := h a0
    grind
  · replace a0 : Nat.IsPos a := by grind
    have : Nat.IsPos (a + b) := by exact proposition_2_2_8 a0
    rw [ab0] at this
    grind

lemma lemma_2_2_10 : ∀ a : Nat, Nat.IsPos a → ∃ b : Nat, b++ = a := by
  intro a positive_a
  induction a with
  | zero     => grind
  | succ c _ => use c

/-
## Ordering of Natural Numbers
-/
@[grind =, simp]
instance Nat.instLE : LE Nat where
  le a b := ∃ c : Nat, a + c = b

-- helped out by Claude
@[grind =, simp]
instance Nat.instDecidableLE : DecidableLE Nat
  | .zero, b => isTrue ⟨b, by
      calc (0 : Nat) + b = b + 0 := proposition_2_2_4 0 b
        _ = b := lemma_2_2_2 b⟩
  | a++, .zero => isFalse (by rintro ⟨c, hc⟩ ; grind)
  | a++, b++ =>
      match Nat.instDecidableLE a b with
      | isTrue h => isTrue (h.elim fun c hc => ⟨c, by grind⟩)
      | isFalse h => isFalse (by
          rintro ⟨c, hc⟩
          replace hc : (a + c)++ = b++ := by grind
          exact h ⟨c, by injection hc⟩)

@[grind =, simp]
instance Nat.instLT : LT Nat where
  lt a b := a ≤ b ∧ a ≠ b

@[grind =, simp]
instance Nat.instDecidableLT : DecidableLT Nat :=
  fun a b => inferInstanceAs (Decidable (a ≤ b ∧ a ≠ b))

/-- Order is reflective -/
theorem proposition_2_2_12_a : ∀ a : Nat, a ≥ a := by
  intro a
  change ∃ c : Nat, a + c = a
  use 0
  grind

/-- Order is transitive -/
theorem proposition_2_2_12_b : ∀ a b c : Nat, a ≥ b ∧ b ≥ c → a ≥ c := by
  intro a b c abac
  -- こうやって≥, >を分解する（これしかない?)
  rcases abac with ⟨⟨d1, hd1⟩,  ⟨d2, hd2⟩⟩
  refine ⟨d2 + d1, ?_⟩
  rw [← proposition_2_2_5, hd2, hd1]

/-- Order is antisymmetric -/
theorem proposition_2_2_12_c : ∀ a b : Nat, a ≥ b ∧ b ≥ a → a = b := by
  rintro a b ⟨⟨c1, h1⟩, ⟨c2, h2⟩⟩
  replace h1 : b + (c1 + c2) = a + c2 := by grind
  rw [h2] at h1
  have : b = b + 0 := by grind
  rw (occs := .pos [2]) [this] at h1
  apply proposition_2_2_6 at h1
  replace h1 : c1 = 0 ∧ c2 = 0 := corollary_2_2_9 h1
  grind


/-- Addition preserves order -/
theorem proposition_2_2_12_d : ∀ a b c : Nat, a ≥ b ↔ a + c ≥ b + c := by
  intro a b c
  constructor
  · intro ⟨d, ca⟩
    change b + c ≤ a + c
    change ∃ e : Nat, b + c + e = a + c
    use d
    grind
  · intro ⟨d, ca⟩
    change b ≤ a
    change ∃ e : Nat, b + e = a
    use d
    replace ca : c + b + d = a + c := by grind
    replace ca : c + (b + d) = c + a := by grind
    replace ca : b + d = a := proposition_2_2_6 ca
    grind

/-- 次の命題が難しいので補助定理を証明しておく。`≠` に関する定理がない。 -/
theorem inc_add_ne_self : ∀ n a : Nat, n + 1 + a ≠ n := by
  intro n a
  by_contra
  replace : 1 + a = 0 := by
    rw (occs := .pos [2]) [← lemma_2_2_2 n] at this
    rw [proposition_2_2_5] at this
    apply proposition_2_2_6 at this
    grind
  replace this : (1 : Nat) = (0 : Nat) := by
    apply corollary_2_2_9 at this
    grind
  contradiction

theorem proposition_2_2_12_e : ∀ a b : Nat, a < b ↔ a++ ≤ b := by
  intro a b
  constructor
  · intro ab
    change ∃ c : Nat, a++ + c = b
    rcases ab with ⟨⟨d, ab'⟩, c⟩
    rcases d with ⟨zero, succ⟩
    · simp at ab' ; contradiction
    · expose_names
      use a_1
      change (a + a_1)++ = b
      grind
  · intro ab
    rw [← add1_is_inc] at ab
    rcases ab with ⟨c, ab'⟩
    rw [← ab']
    change a ≤ a + 1 + c ∧ a ≠ a + 1 + c
    constructor
    · change ∃ d : Nat, a + d = a + 1 + c;
      use 1 + c
      grind
    · have : 1 + c ≠ 0 := by exact Ne.symm (ne_of_beq_false rfl)
      exact Ne.symm (inc_add_ne_self a c)

theorem proposition_2_2_12_f : ∀ a b : Nat, a < b ↔ ∃ d : Nat, Nat.IsPos d ∧ b = a + d := by
  intro a b
  constructor
  · rintro ⟨⟨c, ac⟩, ab⟩
    match c with
    | .zero => simp at ac ; contradiction
    | c'++ => use c'++ ; grind
  · rintro ⟨e, ⟨pos_e, h⟩⟩
    change a ≤ b ∧ a ≠ b
    constructor
    · change ∃ e, a + e = b
      use e
      grind
    · by_contra
      have : e = 0 := by
        simp [this] at h
        rw (occs := .pos [1]) [← lemma_2_2_2 b] at h
        exact proposition_2_2_6 (id (Eq.symm h))
      grind

/-- Order is transitive -/
theorem proposition_2_2_12_b' {a b c : Nat} : a > b ∧ b > c → a > c := by
  intro abac
  -- こうやって≥, >を分解する（これしかない?)
  rcases abac with ⟨⟨a_ge_b, a_ne_b⟩,  ⟨b_ge_c, b_ne_c⟩⟩
  refine (proposition_2_2_12_f c a).mpr ?_
  · rcases a_ge_b with ⟨x, ab⟩
    rcases b_ge_c with ⟨y, bc⟩
    use (x + y)
    constructor
    · refine proposition_2_2_8 ?_
      · by_contra this
        simp at this
        grind
    · grind

theorem proposition_2_2_12_g {a b : Nat} : a ≤ b ↔ a < b ∨ a = b := by
  constructor
  · intro le
    rcases le with ⟨c, p⟩
    match c with
    | .zero => simp at p ; grind
    | c'++ =>
      left
      refine (proposition_2_2_12_e a b).mpr ?_
      · change ∃ c, a++ + c = b
        use c'
        rw [lemma_2_2_3, proposition_2_2_4, ← lemma_2_2_3, proposition_2_2_4] at p
        grind
  · intro p
    cases p <;> expose_names
    · rcases h with ⟨e, p⟩
      grind
    · simp [h]
      exact proposition_2_2_12_a b


/-- 次の命題が難しいので補助定理を証明しておく。 -/
lemma succ_gt_self {a : Nat} : a++ > a := by
  exact (proposition_2_2_12_e a (a++)).mpr (proposition_2_2_12_a (a++))

/-- Trichotomy of order for natural numbers
trichotomy とは a division into three categories。
-/
theorem proposition_2_2_13 {a b : Nat} : a < b ∨ a = b ∨ a > b := by
  induction a with
  | zero =>
    simp
    match b with
    | .zero => simp
    | b'++ => left ; exact compareOfLessAndEq_eq_lt.mp rfl
  | succ a' ih =>
    cases ih <;> expose_names
    · apply (proposition_2_2_12_e a' b).mp at h
      apply proposition_2_2_12_g.mp at h
      grind
    · cases h <;> expose_names
      · right ; right
        rw [h]
        change b < b++;
        exact succ_gt_self
      · right ; right
        have : a'++ > a' := by exact succ_gt_self
        apply proposition_2_2_12_b' ⟨this, h⟩

@[grind .]
theorem self_not_lt : ∀ a : Nat, ¬a < a := by
  intro a
  by_contra h
  rcases h with ⟨c, p⟩
  contradiction

theorem self_not_gt : ∀ a : Nat, ¬a > a := fun a ↦ self_not_lt a

theorem not_lt_eq_ge {a b : Nat} : ¬a < b → a ≥ b := by
  intro not_lt
  change b ≤ a
  apply proposition_2_2_12_g.mpr
  by_contra ha
  replace ha : ¬b < a ∧ ¬a = b := by grind
  rcases ha with ⟨not_gt, not_eq⟩
  replace not_gt : ¬a > b := by grind
  have := @proposition_2_2_13 a b
  grind

theorem corollary_2_2_13' : ∀ a b : Nat, a ≠ b ↔ a < b ∨ a > b := by
  intro a b
  constructor
  · intro h
    have := @proposition_2_2_13 a b
    grind
  · intro h
    by_contra h'
    cases h <;> { expose_names ; simp [h'] at h ; grind }

/-- 補助定理 -/
lemma self_lt_inc : ∀ n : Nat, n < n++ := by
  intro n
  change n ≤ n++ ∧ n ≠ n++;
  constructor
  · change ∃ d, n + d = n++;
    use 1
    exact add1_is_inc n
  · by_contra
    rw (occs := .pos [1]) [← lemma_2_2_2 n] at this
    rw [← add1_is_inc] at this
    apply proposition_2_2_6 at this
    injection this

/-- 補助定理 -/
lemma lt_zero_eq_zero {n : Nat} : n ≤ 0 → n = 0 := by
  rintro ⟨d, p⟩
  replace p : n = 0 ∧ d = 0 := by
    exact corollary_2_2_9 p
  exact p.left

/-- 補助定理 -/
lemma lt_inc_eq_le {n m : Nat} : n < m++ ↔ n ≤ m := by
  constructor
  · intro n_lt_m
    change ∃ c, n + c = m;
    obtain ⟨⟨d, n_le_m⟩, n_eq_m⟩ := n_lt_m
    induction d with
    | zero => simp at n_le_m ; grind
    | succ d d_gt_0 =>
      rw (occs := .pos [1]) [lemma_2_2_3] at n_le_m
      replace n_le_m : n + d = m := by grind
      use d
  · rintro ⟨d, n_le_m⟩
    change n ≤ m++ ∧ n ≠ m++;
    constructor
    · change ∃ c, n + c = m++;
      rw [← n_le_m]
      use (d++)
      exact lemma_2_2_3 n d
    · by_contra
      rw [← n_le_m] at this
      rw (occs := .pos [1]) [← lemma_2_2_3] at this
      rw (occs := .pos [1]) [← lemma_2_2_2 n] at this
      apply proposition_2_2_6 at this
      contradiction

/-- 補助定理 -/
lemma lt_is_le {a b : Nat} : a < b → a ≤ b := by
  rintro ⟨a_lt_b, a_ne_b⟩
  grind

/-- 補助定理 -/
lemma le_eq_lt_and_eq {n m : Nat} {P : Prop} : (n ≤ m → P) ↔ (n < m → P) ∧ (n = m → P) := by
  constructor
  · intro n_ge_m
    constructor
    · intro p
      apply lt_is_le at p
      replace n_ge_m := n_ge_m p
      grind
    · intro n_eq_m
      have : n ≤ m := by
        change ∃ c, n + c = m
        use 0
        grind
      grind
  · rintro ⟨n_gt_m, n_eq_m⟩ ⟨c, nm⟩
    match c with
    | .zero => simp at nm ; grind
    | c++   =>
      have : n < m := by
        change  n ≤ m ∧ n ≠ m
        constructor
        · change ∃ d, n + d = m
          use c++;
        · by_contra
          rw [← nm] at this
          rw (occs := .pos [1]) [← lemma_2_2_2 n] at this
          apply proposition_2_2_6 at this
          contradiction
      grind

/-- 補助定理 -/
lemma le_trans {a b c : Nat} : a ≤ b → b ≤ c → a ≤ c := by
  rintro ⟨c1, a_le_b⟩ ⟨c2, b_le_c⟩
  rw [← a_le_b] at b_le_c
  rw [← b_le_c]
  change ∃ c3, a + c3 = a + c1 + c2
  use c1 + c2
  grind

/-- 補助定理 -/
lemma lt_eq_le_and_ne {a b : Nat} : (a < b) ↔ (a ≤ b ∧ a ≠ b) := by
  constructor
  · rintro a_le_b
    rcases a_le_b with ⟨c, ac_eq_b⟩
    grind
  · rintro ⟨a_le_b, a_ne_b⟩
    change a ≤ b ∧ a ≠ b
    constructor <;> grind

/-- 補助定理 -/
lemma le_self {a : Nat} : a ≤ a := by
  change ∃ c, a + c = a
  use 0
  simp

/-- Strong principle of induction
Hint: define `Q n` to be the property that `P m` is true
for all m₀ ≤ m < n; note that `Q n` is vacously true when n ≤ m₀.
-/
theorem proposition_2_2_14 : ∀ m₀ : Nat, ∀ P : Nat -> Prop,
    (∀ m ≥ m₀, (∀ m' ≥ m₀, m' < m → P m') → P m) → ∀ m ≥ m₀, P m := by
  intro m₀ P h m hm
  have hm' : ∃ c, m = m₀ + c := by
    rcases hm with ⟨c, hm'⟩
    grind
  rcases hm' with ⟨c, hm'⟩
  suffices key : ∀ c, ∀ m' ≥ m₀, m' ≤ m₀ + c → P m' by
    have := key c (m₀ + c) (by grind) (proposition_2_2_12_a (m₀ + c))
    grind
  -- この時点でgoalはhをより一般化したものになっている。従って帰納法が使いやすい
  intro c
  induction c with
  | zero      =>
    intro m' hm' hle
    simp at hle
    /-
      m₀ m c m' : Nat
      P : Nat → Prop
      h : ∀ m ≥ m₀, (∀ m' ≥ m₀, m' < m → P m') → P m
      hm : m ≥ m₀
      hm'✝ : m = m₀ + c
      hm' : m' ≥ m₀
      hle : m' ≤ m₀
      ⊢ P m'
    -/
    apply h m' hm'
    /-
      ⊢ ∀ m'_1 ≥ m₀, m'_1 < m' → P m'_1
    -/
    intro m'' hm'' hlt''
    have m'_eq_m₀ : m' = m₀ := by
      rcases hm' with ⟨c1, hm''⟩
      rcases hle with ⟨c2, hle⟩
      rw [← hm''] at hle
      rw (occs := .pos [2]) [← lemma_2_2_2 m₀] at hle
      rw [proposition_2_2_5] at hle
      apply proposition_2_2_6 at hle
      have : c1 = 0 ∧ c2 = 0 := by exact corollary_2_2_9 hle
      simp [this.left] at hm''
      grind
    subst m'_eq_m₀
    expose_names
    clear h hm hm'_1 hm' hle
    rcases hlt'' with ⟨⟨c1, a⟩, ne⟩
    rcases hm'' with ⟨c2, b⟩
    rw [← b] at a
    rw (occs := .pos [2]) [← lemma_2_2_2 m'] at a
    rw [proposition_2_2_5] at a
    apply proposition_2_2_6 at a
    have : c2 = 0 := by
      apply corollary_2_2_9 at a
      grind
    simp [this] at b
    grind
  | succ c ih =>
    intro m' hm' hle
    by_cases heq : m' = m₀ + c++ <;> expose_names
    · subst heq
      have h' := h (m₀ + c++) hm'
      have ih' := fun m' hm' (hlt : m' < m₀ + c++) ↦ ih m' hm' (by
        rw [lemma_2_2_3 m₀ c] at hlt
        exact lt_inc_eq_le.mp hlt )
      grind
    · have : m' ≤ m₀ + c := by
        have : m' < m₀ + c++ := by
          refine lt_eq_le_and_ne.mpr ?_
          · constructor <;> grind
        rw [lemma_2_2_3 m₀ c] at this
        apply lt_inc_eq_le.mp at this
        grind
      exact ih m' hm' this

/-!
## Exercises

- 2.2.1 -> proposition_2_2_5
- 2.2.2 -> lemma_2_2_10
- 2.2.3 -> proposition_2.2.12
- 2.2.4 -> proposition_2.2.13
- 2.2.5 -> proposition_2.2.14
-/

/-- Excercise 2.2.6のための補助定理 -/
lemma le_inc_eq_le {a b : Nat} : a ≤ b++ → a ≠ b++ → a ≤ b := by
  intro a_le_b1 a_ne_b1
  rcases a_le_b1 with ⟨c, le⟩
  match c with
  | .zero => simp at le ; grind
  | c++   =>
    rw [lemma_2_2_3] at le
    change ∃ c, a + c = b
    use c
    have : a + c = b := by grind
    grind

/-- Excercise 2.2.6: Principle of backwards induction
- Hint: apply induction to the variable $n$.
-/
example {n : Nat} {P : Nat → Prop} :
    (∀ m : Nat, P (m++) → P m) → P n → (∀ m : Nat, m ≤ n → P m) := by
  intro h Pn
  induction n with
  | zero      =>
    simp at *
    intro m m_le_0
    have : m = 0 := by exact lt_zero_eq_zero m_le_0
    subst this
    grind
  | succ n ih =>
    intro m m_le_s1
    replace m_le_s1 : m < n++ ∨ m = n++ := by
      rcases m_le_s1 with ⟨c, le⟩
      by_cases c_eq_0 : c = 0
      · simp [c_eq_0] at le ; grind
      · left
        rw [← le]
        rw (occs := .pos [1]) [← lemma_2_2_2 m]
        refine (proposition_2_2_12_e (m + 0) (m + c)).mpr ?_
        · simp
          change ∃ d, m++ + d = m + c
          clear le
          match c with
          | .zero => grind
          | c++ => use c ; grind
    rcases m_le_s1 with ⟨le, ne⟩
    · replace h := h n Pn
      replace ih := ih h
      have : m ≤ n := by exact le_inc_eq_le le ne
      grind
    · grind

/-- Exercise 2.2.7: the principle of induction starting -/
example {n : Nat} {P : Nat → Prop} :
    (∀ m : Nat, P m → P (m++)) → P n → (∀ m : Nat, m ≥ n → P m) := by
  intro pp pn
  suffices key : ∀ c : Nat, P (n + c) by
    intro m hm
    obtain ⟨c, hc⟩ := hm
    rw [← hc]
    exact key c
  intro c
  induction c with
  | zero      => grind
  | succ c ih =>
    replace pp := pp (n + c) ih
    rw [lemma_2_2_3]
    grind

end section_02_2

/-!
## Section 2.3: Multiplication
-/
section section_02_3

open _root_.Chapter2.Nat

/-- Definition 2.3.1 (Multiplication of natural numbers) -/
abbrev Nat.mul (n m : Nat) : Nat := Nat.recurse (fun _ prod ↦ prod + m) 0 n

#guard Nat.mul 0 1 = 0
#guard Nat.mul 1 1 = 1
#guard Nat.mul 3 2 = 6

/-- This instance allows for the {kw (of := «term_*_»)}`*` notation to be used for natural number multiplication. -/
instance Nat.instMul : Mul Nat where
  mul := mul

#guard 0 * 1 = 0
#guard 1 * 1 = 1
#guard 3 * 2 = 6

/-- Definition 2.3.1 (Multiplication of natural numbers)
Compare with Mathlib's {name}`Nat.zero_mul` -/
theorem Nat.zero_mul (m: Nat) : 0 * m = 0 := Nat.recurse_zero (fun _ prod ↦ prod+m) _

/-- Definition 2.3.1 (Multiplication of natural numbers)
Compare with Mathlib's {name}`Nat.succ_mul` -/
theorem Nat.succ_mul (n m: Nat) : (n++) * m = n * m + m := recurse_succ (fun _ prod ↦ prod+m) _ _

theorem Nat.one_mul' (m : Nat) : 1 * m = 0 + m := by
  rw [←zero_succ, succ_mul, zero_mul]
/-- Compare with Mathlib's {name}`Nat.one_mul` -/
theorem Nat.one_mul (m: Nat) : 1 * m = m := by
  rw [one_mul', zero_add]

theorem Nat.two_mul (m : Nat) : 2 * m = 0 + m + m := by
  rw [←one_succ, succ_mul, one_mul']

/-- This lemma will be useful to prove Lemma 2.3.2.
Compare with Mathlib's {name}`Nat.mul_zero` -/
lemma Nat.mul_zero (n : Nat) : n * 0 = 0 := by
  induction n with
  | zero      => exact zero_mul 0
  | succ n ih => rw [succ_mul, ih] ; grind

lemma Nat.mul_one (n : Nat) : n * 1 = n := by
  induction n with
  | zero      => exact zero_mul 0
  | succ n ih => rw [succ_mul, ih] ; grind

/-- This lemma will be useful to prove Lemma 2.3.2.
Compare with Mathlib's {name}`Nat.mul_succ` -/
lemma Nat.mul_succ (n m : Nat) : n * m++ = n * m + n := by
   induction n with
   | zero => simp [zero_mul]
   | succ n' ih =>
     rw [Nat.succ_mul, Nat.succ_mul, ih]
     rw (occs := .pos [1]) [proposition_2_2_5]
     rw (occs := .pos [1]) [proposition_2_2_5]
     have : n' + m++ = m + n'++ := by grind
     rw [this]

/-- Lemma 2.3.2 (Multiplication is commutative) / Exercise 2.3.1
Compare with Mathlib's {name}`Nat.mul_comm` -/
lemma Nat.mul_comm (n m: Nat) : n * m = m * n := by
  induction m with
  | zero => simp [zero_mul] ; exact mul_zero n
  | succ m' ih =>
    rw [Nat.mul_succ, Nat.succ_mul]
    grind

/-- This lemma will be useful to prove Lemma 2.3.3.
Compare with Mathlib's {name}`Nat.mul_pos` -/
lemma Nat.pos_mul_pos {n m: Nat} (h₁: n.IsPos) (h₂: m.IsPos) :
    (n * m).IsPos := by
  simp [Nat.IsPos] at *
  match n with
  | zero => simp at h₁
  | succ n' => match m with
    | zero => simp at h₂
    | succ m' =>
      by_contra eq
      have weird : (n'++ * m') + n'++ = 0 := by
        rw [Nat.mul_succ] at eq
        grind
      replace weired : (n'++ * m') = 0 ∧ n'++ = 0 := by
        exact corollary_2_2_9 weird
      rcases weired with ⟨a, m'succ_eq_0⟩
      exact (iff_false_intro h₁).mp m'succ_eq_0

/-- Lemma 2.3.3 (Positive natural numbers have no zero divisors) / Exercise 2.3.2.
    Compare with Mathlib's {name}`Nat.mul_eq_zero`.  -/
lemma Nat.mul_eq_zero (n m: Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor
  · intro nm
    by_contra eq
    simp at eq
    rcases eq with ⟨n0, m0⟩
    replace n0 : n.IsPos := by simp ; grind
    replace m0 : m.IsPos := by simp ; grind
    have : (n * m).IsPos := by exact pos_mul_pos n0 m0
    grind
  · rintro ⟨_, _⟩
    · exact zero_mul m
    · expose_names; rw [h] ; exact mul_zero n

/-- Left distributivity of multiplication over addition: `a * (b + c) = a * b + a * c`. -/
lemma proposition_2_3_4 {a b c : Nat} : a * (b + c) = a * b + a * c := by
  induction c with
  | zero => simp [Nat.mul_zero a]
  | succ c' ih =>
    rw [lemma_2_2_3 b c']
    rw [Nat.mul_succ, ih]
    rw [Nat.mul_succ]
    exact proposition_2_2_5

/-- Right distributivity of multiplication over addition: `(b + c) * a = b * a + c * a`. -/
lemma proposition_2_3_4' {a b c : Nat} : (b + c) * a = b * a + c * a := by
  rw [Nat.mul_comm]
  rw [proposition_2_3_4]
  rw (occs := .pos [1]) [Nat.mul_comm]
  rw (occs := .pos [2]) [Nat.mul_comm]

/-- Proposition 2.3.5 (Multiplication is associtive) -/
lemma proposition_2_3_5 {a b c : Nat} : a * (b * c) = (a * b) * c := by
  induction c with
  | zero => simp ; rw [mul_zero, mul_zero, mul_zero]
  | succ c ih =>
    rw [Nat.mul_succ]
    rw [proposition_2_3_4]
    rw [Nat.mul_succ]
    rw [ih]

/-- Proposition 2.3.6 のための補助定理 -/
lemma mul_eq_if_eq {a b c : Nat} : a = b → a * c = b * c := by
  intro a_eq_b
  simp [a_eq_b]

/-- Proposition 2.3.6 のための補助定理 -/
lemma lt_def {a b : Nat} : a < b ↔ ∃ c : Nat, c > 0 ∧ a + c = b := by
  constructor
  · intro le
    apply lt_eq_le_and_ne.mp at le
    obtain ⟨⟨d, lt⟩, eq⟩ := le
    use d
    constructor
    · rw [← lt] at eq
      match d with
      | zero => grind
      | succ d' => exact compareOfLessAndEq_eq_lt.mp rfl
    · exact lt
  · intro h
    rcases h with ⟨e, p⟩
    constructor
    · change ∃ e, a + e = b
      use e
      grind
    · by_contra h
      subst h
      rcases p with ⟨le, eq⟩
      have : ¬e = 0 := by
        by_contra h
        subst h
        rcases le with ⟨le', eq'⟩
        grind
      replace p : 0 = e := by
        rw (occs := .pos [2]) [← lemma_2_2_2 a] at eq
        apply proposition_2_2_6 at eq
        grind
      grind

/-- Proposition 2.3.6 のための補助定理 -/

lemma eq_if_mul_two_eq' {a b : Nat} : a * 2 = b * 2 → a = b := by
  intro two
  simp [← one_succ] at two
  simp [Nat.mul_succ] at two
  simp [mul_one] at two
  have := @proposition_2_2_13 a b
  cases this <;> expose_names
  · rcases h with ⟨⟨c, le⟩, ne⟩
    rw [← le] at two
    rw (occs := .pos [1]) [proposition_2_2_5] at two
    rw (occs := .pos [2]) [← proposition_2_2_5] at two
    rw (occs := .pos [4]) [proposition_2_2_4] at two
    rw (occs := .pos [1]) [proposition_2_2_5] at two
    rw (occs := .pos [1]) [← proposition_2_2_5] at two
    rw (occs := .pos [1]) [← lemma_2_2_2 (a + a)] at two
    apply proposition_2_2_6 at two
    replace two : c + c = 0 := by exact Eq.symm (axiom_4' (congrArg succ two))
    apply corollary_2_2_9 at two
    replace two := two.left
    subst two
    simp at *
    grind
  · cases h <;> expose_names
    · grind
    · rcases h with ⟨⟨c, le⟩, ne⟩
      rw [← le] at two
      rw (occs := .pos [1]) [proposition_2_2_5] at two
      rw (occs := .pos [2]) [← proposition_2_2_5] at two
      rw (occs := .pos [3]) [proposition_2_2_4] at two
      rw (occs := .pos [1]) [proposition_2_2_5] at two
      rw (occs := .pos [1]) [← proposition_2_2_5] at two
      rw (occs := .pos [2]) [← lemma_2_2_2 (b + b)] at two
      apply proposition_2_2_6 at two
      apply corollary_2_2_9 at two
      replace two := two.left
      subst two
      simp at *
      grind

lemma eq_if_mul_eq' {a b c : Nat} : a * c++ = b * c++ → a * c = b * c := by
  intro h
  induction c with
  | zero => simp [Nat.zero_succ, Nat.mul_one] at h ; grind
  | succ c' ih =>
    rw (occs := .pos [1]) [Nat.mul_succ] at h
    rw (occs := .pos [2]) [Nat.mul_succ] at h
    have := @proposition_2_2_13 a b
    cases this <;> expose_names
    · rcases h_1 with ⟨⟨d, ad_eq_b⟩, a_ne_b⟩
      replace ad_eq_b : b = a + d := by
        exact axiom_4' (congrArg succ (id (Eq.symm ad_eq_b)))
      subst ad_eq_b
      rw [proposition_2_3_4'] at h
      rw (occs := .pos [1]) [proposition_2_2_5] at h
      apply proposition_2_2_6 at h
      rw [proposition_2_2_4] at h
      rw (occs := .pos [1]) [← lemma_2_2_2 a] at h
      rw (occs := .pos [1]) [proposition_2_2_5] at h
      apply proposition_2_2_6 at h
      replace h : d = 0 ∧ d * c'++ = 0 := by
        exact corollary_2_2_9 (id (Eq.symm h))
      replace h : d = 0 := by grind
      subst h
      simp at a_ne_b
    · cases h_1 <;> expose_names
      · subst h_1
        grind
      · rcases h_1 with ⟨⟨d, a_eq_bd⟩, a_ne_b⟩
        replace a_eq_bd : a = b + d := by
          exact axiom_4' (congrArg succ (id (Eq.symm a_eq_bd)))
        subst a_eq_bd
        rw [proposition_2_3_4'] at h
        rw (occs := .pos [1]) [proposition_2_2_5] at h
        rw (occs := .pos [2]) [proposition_2_2_4] at h
        rw (occs := .pos [1]) [proposition_2_2_5] at h
        rw (occs := .pos [1]) [← proposition_2_2_5] at h
        rw (occs := .pos [2]) [← lemma_2_2_2 (b * c'++ + b)] at h
        apply proposition_2_2_6 at h
        replace h : d = 0 ∧ d * c'++ = 0 := corollary_2_2_9 h
        replace h : d = 0 := by grind
        subst h
        simp at a_ne_b

/-- Proposition 2.3.6 (Multiplication preserves order) -/
lemma proposition_2_3_6 {a b c : Nat} {h : a < b} {c_is_pos : Nat.IsPos c} :
    a * c < b * c := by
  rcases h with ⟨⟨d, ad_eq_b⟩, a_ne_b⟩
  replace ad_eq_b : b = a + d := by grind
  subst ad_eq_b
  rw [proposition_2_3_4']
  have : Nat.IsPos (d * c) := by
    have : Nat.IsPos d := by
      by_contra h
      replace h : d = 0 := by simp at h ; grind
      subst h
      simp at a_ne_b
    exact pos_mul_pos this c_is_pos
  refine lt_eq_le_and_ne.mpr ?_
  · constructor
    · change ∃ e, a * c + e = a * c + d * c
      use (d * c)
    · by_contra h
      replace h : d * c = 0 := by
        rw (occs := .pos [1]) [← lemma_2_2_2 (a * c)] at h
        apply proposition_2_2_6 at h
        grind
      replace h : ¬ Nat.IsPos (d * c) := by grind
      contradiction

/-- Cancellation law -/
lemma corollary_2_3_7 {a b c : Nat} (h : a * c = b * c) (c_ne_0 : c ≠ 0) : a = b := by
  match c with
  | .zero => contradiction
  | c++ =>
    induction c with
    | zero => simp [zero_succ, mul_one] at h ; grind
    | succ c' =>
      expose_names
      apply eq_if_mul_eq' at h
      have : c'++ ≠ 0 := succ_ne c'
      replace a_ih := a_ih h this
      grind

end section_02_3

end Chapter2

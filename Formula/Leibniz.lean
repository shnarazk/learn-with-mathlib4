module

public import Mathlib.Tactic

open Nat Finset Real

/-- the most efficient vaviant -/
public def leibniz₁ (n : Nat) (k: Float) (sum : Float) : Float :=
  match n with
  | zero    => sum + 8 / 3
  | succ n' => leibniz₁ n' (k - 4) (sum + (8 / ((k + 1) * (k + 3))))

/-- define it on `Nat` -/
public def leibniz₂ : Nat → Float
  | zero    => 8 / 3
  | succ n' =>
      let k := (succ n').toFloat * 4
      leibniz₂ n' + 8 / ((k + 1) * (k + 3))

-- def leibniz₃ := (fun k => ∑ i ∈ range k, (-1 : ℝ) ^ i / (2 * i + 1))
-- partial def leibniz₃ (k : Nat) : Real :=
--   ∑ i ∈ range k, (-1 : Real) ^ i.toReal / (2 * i.toReal + 1)

/-- The public interface -/
public def leibniz (n : Nat) : Float := leibniz₁ n (n.toFloat * 4) 0
-- def leibniz (n : Nat) : Float := leibniz₂ n 0.0
-- def leibniz (n : Nat) : Float := leibniz₃ (2 * n) |>.toFloat

public def leibnizIO (n : Nat) : IO Float := do return leibniz n

#guard (leibniz 1000 - 3.1415).abs < 0.001

/-!
-- This is the FUN part only on Lean4
-/
namespace this_is_pi_approximation

open Rat

def leibniz₁R (n : Nat) (k: Rat) (sum : Rat) : Rat :=
  match n with
  | zero => sum + 8 / 3
  | succ n' => leibniz₁R n' (k - 4) (sum + (8 / ((k + 1) * (k + 3))))

def leibniz₂R : Nat → Rat
  | zero => 8 / 3
  | succ n' =>
      let k : Rat := (succ n') * 4
      leibniz₂R n' + 8 / ((k + 1) * (k + 3))

-- #eval (leibniz₂R 3).toFloat

lemma leibniz₁R_sum (n : Nat) :
    ∀ sum : Rat, leibniz₁R n (4 * n) sum = leibniz₁R n (4 * n) 0 + sum := by
  induction' n with n0 ih
  { intro sum ; simp [leibniz₁R] ; exact Rat.add_comm sum (8 / 3) }
  { intro sum ; simp [leibniz₁R] ; grind }

lemma they_are_identical (n : Nat) : leibniz₁R n (4 * n) 0 = leibniz₂R n := by
  induction' n with n0 ih
  { dsimp [leibniz₁R, leibniz₂R] ; norm_num }
  {
    dsimp [leibniz₁R, leibniz₂R]
    have eq1 : ↑(n0 + 1) = ↑n0 + (1 : Rat) := by exact cast_add_one n0
    calc
      leibniz₁R n0 (4 * ↑(n0 + 1) - 4)
          (0 + 8 / ((4 * ↑(n0 + 1) + 1) * (4 * ↑(n0 + 1) + 3)))
        = leibniz₁R n0 (4 * (↑n0 + 1) - 4)
            (0 + 8 / ((4 * ↑(n0 + 1) + 1) * (4 * ↑(n0 + 1) + 3))) := by rw [eq1]
      _ = leibniz₁R n0 (4 * ↑n0)
           (0 + 8 / ((4 * ↑(n0 + 1) + 1) * (4 * ↑(n0 + 1) + 3))) := by
          simp [Rat.mul_add]
      _ = leibniz₁R n0 (4 * ↑n0) 0
            + (0 + 8 / ((4 * ↑(n0 + 1) + 1) * (4 * ↑(n0 + 1) + 3))) := by
            apply leibniz₁R_sum n0 _
      _ = leibniz₂R n0 + (0 + 8 / ((4 * ↑(n0 + 1) + 1) * (4 * ↑(n0 + 1) + 3))) := by
          rw [ih]
      _ = leibniz₂R n0 + 8 / ((4 * ↑(n0 + 1) + 1) * (4 * ↑(n0 + 1) + 3)) := by
          rw [Rat.zero_add]
      _ = leibniz₂R n0 + 8 / ((↑(n0 + 1) * 4 + 1) * (↑(n0 + 1) * 4 + 3)) := by
          simp [mul_comm]
  }

#guard ∑ x ∈ Finset.Iic 1, x == 1

variable (n : Nat)

lemma sum_def (f : Nat → Rat) : ∑ i ∈ {n}, f i = f n := by exact sum_singleton f n

lemma range_add_one_eq_sup_self : Finset.range (n + 1) = Finset.range n ⊔ {n} := by
  refine Finset.ext_iff.mpr ?_
  intro k
  constructor
  · intro kn1
    by_cases kn : k ∈ range n
    · rw [sup_eq_union] ; exact mem_union_left {n} kn
    · simp [range] at kn
      simp [range] at kn1
      rcases kn1 with a|b
      · simp ; left ; exact a
      · contrapose! b ; exact kn
  · intro H
    refine mem_range.mpr ?_
    simp at H
    rcases H with A | B
    · simp [A]
    · exact Nat.lt_add_right 1 B

lemma range_sup_eq_add (f : Nat → Rat) :
   ∑ i ∈ Finset.range n ⊔ {n}, f i = ∑ i ∈ Finset.range n, f i + ∑ i ∈ {n}, f i := by
  grind

/-!
[Mathlib/Data/Real/Pi/Leibniz.lean](https://github.com/leanprover-community/mathlib4/blob/6a2ce9480a312b180ac91c687d6686c6479c398b/Mathlib/Data/Real/Pi/Leibniz.lean#L17)
上記のリンク先で以下のLが円周率に収束することが示されているが定理には名前があっても
数列に名前がついてないのでLと等しいことが言えない。見比べて同じと言うしかない。
正確には上記のリンク先の数列は実数上に定義されている。
まあ円周率は実数上にしか存在しないからなあ。
-/
def L : Rat := 4 * ∑ i ∈ Finset.range (n + 1), ((-1 : Rat) ^ i / (2 * i + 1 :Rat))
-- #eval (L 200).toFloat
-- #eval L 1

lemma nat_to_rad : (↑(n + 1) : Rat) = ((↑n + ↑1) : Rat) := by
  exact cast_add_one n

/-- Lの再帰性 -/
lemma L_rec : L (n + 1) = L n + 4 * (-1 : Rat) ^ (n + 1) / (2 * n + 3) := by
  calc
    L (n + 1) = 4 * ∑ i ∈ range (n + 1 + 1), (-1 : Rat) ^ i / (2 * i + 1) := by
        simp [L]
    _ = 4 * ∑ i ∈ (range (n + 1) ⊔ {n + 1}), (-1 : Rat) ^ i / (2 * i + 1) := by
        rw [← range_add_one_eq_sup_self]
    _ = 4 * (
      ∑ i ∈ range (n + 1), (-1 : Rat) ^ i / (2 * i + 1)
        + ∑ i ∈ {n + 1}, (-1 : Rat) ^ i / (2 * i + 1)) := by
          rw [range_sup_eq_add]
    _ = 4 * ∑ i ∈ range (n + 1), (-1 : Rat) ^ i / (2 * i + 1)
        + 4 * ∑ i ∈ {n + 1}, (-1 : Rat) ^ i / (2 * i + 1) := by
          rw [Rat.mul_add]
    _ = L n + 4 * (∑ i ∈ {n + 1}, (-1 : Rat) ^ i / (2 * i + 1)) := by
        rw [←L]
    _ = L n + 4 * ((-1 : Rat) ^ ↑(n + 1) / (2 * ↑(n + 1) + 1)) := by
        rw [sum_def]
    _ = L n + 4 * ((-1 : Rat) ^ ↑(n + 1) / (2 * (↑n + ↑1) + 1)) := by
        rw [nat_to_rad]
    _ = L n + 4 * ((-1 : Rat) ^ ↑(n + 1) / (2 * ↑n + 2 * ↑1 + 1)) := by
        simp [Rat.mul_add]
    _ = L n + 4 * ((-1 : Rat) ^ ↑(n + 1) / (2 * ↑n + 2 + 1)) := by simp
    _ = L n + 4 * ((-1 : Rat) ^ ↑(n + 1) / (2 * ↑n + (2 + 1))) := by
        rw [Rat.add_assoc]
    _ = L n + 4 * ((-1 : Rat) ^ ↑(n + 1) / (2 * ↑n + 3)) := by norm_num
    _ = L n + 4 * ((-1 : Rat) ^ ↑(n + 1) / (2 * n + 3)) := by norm_num
    _ = L n + 4 * (-1 : Rat) ^ ↑(n + 1) / (2 * n + 3) := by rw [mul_div]

/-- leibniz₂Rの再帰性 -/
lemma l₂_rec :
    leibniz₂R (n + 1) = leibniz₂R n + 4 * 1 / (4 * n + 5) - 4 * 1 / (4 * n + 7) := by
  have non0 (k : Rat) (h : 0 < k) : (4 : Rat) * (↑n + 1) + k ≠ (0 : Rat) := by
    have : (0 : Rat) < ↑n + 1 := by exact cast_add_one_pos n
    have : (4 : Rat) * (↑n + 1) > (0 : Rat) := by refine Left.mul_pos rfl this
    have : (4 : Rat) * (↑n + 1) + k > (0 : Rat) := by
      exact Right.add_pos_of_pos_of_nonneg this (by exact le_of_lt h : 0 ≤ k)
    exact Ne.symm (_root_.ne_of_lt this)
  calc
    leibniz₂R (n + 1) = leibniz₂R n + 8 / ((4 * (n + 1) + 1) * (4 * (n + 1) + 3))
      := by
        rw [leibniz₂R, succ_eq_add_one, mul_comm _ 4]
        rw [nat_to_rad, mul_comm]
    _ = leibniz₂R n
        + 4 * (1 / ((4 * (n + 1) + 1) * 1) - 1 / (1 * (4 * (n + 1) + 3))) :=
        by grind
    _ = leibniz₂R n + 4 * (1 / (4 * (n + 1) + 1) - 1 / (4 * (n + 1) + 3)) := by
        group
    _ = leibniz₂R n + 4 * 1 / (4 * (n + 1) + 1) - 4 * 1 / (4 * (n + 1) + 3) := by
        group
    _ = leibniz₂R n + 4 * 1 / (4 * n + 5) - 4 * 1 / (4 * n + 7) := by group

/-- Lとleibniz₂Rの関連 -/
lemma L_is_Leibniz₂ : L (2 * n + 1) = leibniz₂R n := by
  induction' n with n0 ih
  · simp [L, leibniz₂R] ; norm_num
  · set c1 : Rat := 4 * 1  / (4 * n0 + 5) with ← C1
    set c2 : Rat := 4 * -1 / (4 * n0 + 7) with ← C2
    have L' : L (2 * (n0 + 1) + 1) = L (2 * n0 + 1) + c1 + c2 := by
      calc
        L (2 * (n0 + 1) + 1)
          = L (2 * (n0 + 1))
              + 4 * (-1 : Rat) ^ (2 * (n0 + 1) + 1) / (2 * (2 * (n0 + 1)) + 3)
          := by
            rw [L_rec (2 * (n0 + 1))] ; norm_num
        _ = L (2 * (n0 + 1))
            + 4 * (-1 : Rat) ^ (2 * (n0 + 1) + 1) / (4 * n0 + 7) := by
              group
        _ = L (2 * (n0 + 1))
            + 4 * (((-1 : Rat) ^ (2 * (n0 + 1)) * ((-1 : Rat) ^ 1))) / (4 * n0 + 7)
          := by rw [@pow_add]
        _ = L (2 * (n0 + 1)) + 4 * (1 * (-1 : Rat) ^ 1) / (4 * n0 + 7)
          := by
            have e : Even (2 * (n0 + 1)) := by exact even_two_mul (n0 + 1)
            have p : (-1 : Rat) ≠ (1 : Rat) := by
              exact Ne.symm (ne_of_beq_false rfl)
            rw [(neg_one_pow_eq_one_iff_even p).mpr]
            exact e
        _ = L (2 * (n0 + 1)) + 4 * (-1 : Rat) / (4 * n0 + 7) := by norm_num
        _ = L (2 * (n0 + 1)) + c2 := by rw [C2]
        _ = L (2 * n0 + 1 + 1) + c2 := by group
        _ = L (2 * n0 + 1)
            + 4 * (-1 : Rat) ^ (2 * n0 + 1 + 1) / (2 * (2 * n0 + 1) + 3) + c2
          := by rw [L_rec (2 * n0 + 1)] ; norm_num
        _ = L (2 * n0 + 1)
            + 4 * (-1 : Rat) ^ (2 * (n0 + 1)) / (2 * (2 * n0 + 1) + 3) + c2 := by
              group
        _ = L (2 * n0 + 1) + 4 * (1 : Rat) / (2 * (2 * n0 + 1) + 3) + c2
          := by
            have e : Even (2 * (n0 + 1)) := by
              exact even_two_mul (n0 + 1)
            have p : (-1 : Rat) ≠ (1 : Rat) := by
              exact Ne.symm (ne_of_beq_false rfl)
            rw [(neg_one_pow_eq_one_iff_even p).mpr]
            exact e
        _ = L (2 * n0 + 1) + 4 * (1 : Rat) / (4 * n0 + 5) + c2 := by group
        _ = L (2 * n0 + 1) + c1 + c2 := by rw [C1]
    have C2' : 4 * 1 / (4 * ↑n0 + 7) = -c2 := by
      rw [← C2]
      group
    have l₂' : leibniz₂R (n0 + 1) = leibniz₂R n0 + c1 + c2 := by
      calc
        leibniz₂R (n0 + 1)
          = leibniz₂R n0 + 4 * 1 / (4 * n0 + 5) - 4 * 1 / (4 * n0 + 7) := by
            exact l₂_rec n0
        _ = L (2 * n0 + 1) + 4 * 1 / (4 * n0 + 5) - 4 * 1 / (4 * n0 + 7) := by
            rw [ih]
        _ = L (2 * n0 + 1) + c1 - 4 * 1 / (4 * n0 + 7) := by exact rfl
        _ = L (2 * n0 + 1) + c1 - (4 * 1 / (4 * n0 + 7)) := by exact rfl
        _ = L (2 * n0 + 1) + c1 - (- c2) := by rw [C2']
        _ = L (2 * n0 + 1) + c1 + c2 := by
            exact sub_neg_eq_add (L (2 * n0 + 1) + c1) c2
        _ = leibniz₂R n0 + c1 + c2 := by grind
    simp only [L', l₂']
    rw [ih]

module

public import Mathlib.Tactic

namespace Chapter2_aux

/-- proposition_2_2_14がよくわからないのでℕで考えてみる。 -/
theorem proposition_2_2_14' : ∀ m₀ : ℕ, ∀ P : ℕ -> Prop,
    (∀ m ≥ m₀, (∀ m' ≥ m₀, m' < m → P m') → P m) → ∀ m ≥ m₀, P m := by
  intro m₀ P h m m_ge_m₀
  replace m_ge_m₀ : ∃ c, m = m₀ + c :=
    Nat.exists_eq_add_of_le m_ge_m₀
  -- この時点で m = m₀ + c としてしまうとcが固定されてしまうので帰納法が使えなくなる。
  -- Strengthen to: every m' in [m₀, m₀+c] satisfies P,
  -- so the induction hypothesis covers all smaller values.
  suffices key : ∀ c, ∀ m' ≥ m₀, m' ≤ m₀ + c → P m' by
    obtain ⟨c, rfl⟩ := m_ge_m₀   -- unpack c here, where it is in scope
    exact key c (m₀ + c) (by grind) (le_refl _)
  intro c   -- introduce c for the ∀ before inducting on it
  /-
    m₀ m c : ℕ
    P : ℕ → Prop
    h : ∀ m ≥ m₀, (∀ m' ≥ m₀, m' < m → P m') → P m
    m_ge_m₀ : ∃ c, m = m₀ + c
    ⊢ ∀ m' ≥ m₀, m' ≤ m₀ + c → P m'
  -/
  induction c with
  | zero =>
    -- goal: ∀ m' ≥ m₀, m' ≤ m₀ + 0 → P m'
    -- m' ≤ m₀ and m' ≥ m₀ forces m' = m₀; predecessors are vacuously covered
    intro m' hm' hle
    apply h m' hm'
    intro m'' hm'' hlt''
    /-
      m₀ m m'' : ℕ
      P : ℕ → Prop
      h : ∀ m ≥ m₀, (∀ m' ≥ m₀, m' < m → P m') → P m
      m_ge_m₀ : ∃ c, m = m₀ + c
      hm' : m' ≥ m₀
      hle : m' ≤ m₀ + 0
      hm'' : m'' ≥ m₀
      hlt'' : m'' < m'
      ⊢ P m''
    -/
    grind  -- m'' ≥ m₀ and m'' < m' ≤ m₀ is a contradiction
  | succ c' ih =>
    -- ih : ∀ m' ≥ m₀, m' ≤ m₀ + c' → P m'  ← strong enough now
    -- goal: ∀ m' ≥ m₀, m' ≤ m₀ + (c' + 1) → P m'
    intro m' hm' hle
    by_cases heq : m' = m₀ + (c' + 1)
    · -- top of the range: apply h, predecessors covered by ih
      -- use `subst` first; after that `m'` is gone so reference it via h directly
      -- `subst`は`simp [heq] at *; clear heq`をスマートにしたもの
      subst heq
      -- ∀ m ≥ m₀, に対して`(m₀ ++ (c' + 1))`を割り当てる
      have h' := h (m₀ + (c' + 1)) hm' -- (fun m'' hm'' hlt'' => ih m'' hm'' (by omega))
      -- ∀ 下での変数変換したものを関数として生成: 新しいcontextを今あるcontextから作り出している
      have ih' := fun m' hm' (hlt'' : m' < m₀ + (c' + 1)) ↦ ih m' hm' (by grind: m' ≤ m₀ + c')
      grind
      -- 元々の解法
      -- exact h _ hm' (fun m'' hm'' hlt'' => ih m'' hm'' (by omega))
    · -- strictly below the top: directly covered by ih
      exact ih m' hm' (by omega)

  end Chapter2_aux

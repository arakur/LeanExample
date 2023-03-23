import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import Std.Util.ExtendedBinder
import Mathlib.Tactic.Ring

-- 二項係数 C n k を定義する
@[simp]
def C (n : ℕ) (k : ℕ) : ℕ := match n, k with
  | _, 0 => 1
  | 0, _ => 0
  | n + 1, k + 1 => C n k + C n (k + 1)

#eval C 5 3 -- 10

-- 証明の利便性のため，k の定義域を ℤ に拡張したものを定義する 
@[simp]
def C' (n : ℕ) (k : ℤ) : ℕ := match n with
  | 0 => if k == 0 then 1 else 0
  | n + 1 => C' n (k - 1) + C' n k

-- 以降ではこの C' を用いて命題を記述する
-- C と C' が等しいことを示すには若干の補題の用意が必要である

-- k < 0 ならば C' n k = 0
lemma c_n_k_eq_zero_of_k_neg (n : ℕ) (k : ℤ) : k < 0 → C' n k = 0 := by
  -- h : k < 0 を仮定する
  intro (h : k < 0)
  -- n に関する帰納法で示す
  induction n generalizing k
  case zero => -- n = 0 の場合
    simp
    -- C' n k = 0 となるのは k ≠ 0 の場合に限るので，これを示す
    show k ≠ 0
    -- 仮定 h : k < 0 より k ≠ 0 が成り立つ
    exact LT.lt.ne h
  case succ n' ih => -- n = n' + 1 の場合
    -- ih : ∀ k, k < 0 → C' n' k = 0
    -- h : k < 0 より k - 1 < 0 である
    -- (linarith は線形(不)等式を示すタクティク)
    have h' : k - 1 < 0 := by linarith
    --  よって帰納法の仮定より C' n' (k - 1) も C' n' k も 0
    calc
        C' (n' + 1) k
      = C' n' (k - 1) + C' n' k := rfl
    _ = 0                       := by rw [ih (k - 1) h', ih k h]

-- k = 0 ならば C' n k = 1
lemma c_n_zero_eq_one (n : ℕ) : C' n 0 = 1 := by
  -- n に関する帰納法で示す
  induction n
  case zero => -- n = 0 の場合
    show C' 0 0 = 1
    -- 計算すればわかる
    simp
  case succ n' ih => -- n = n' + 1 の場合
    -- ih : C' n' 0 = 1
    -- 補題 c_n_k_eq_zero_of_k_neg と帰納法の仮定を用いて計算
    calc
        C' (n' + 1) 0
      = C' n' (-1) + C' n' 0  := rfl
    _ = 1                   := by simp [c_n_k_eq_zero_of_k_neg, ih]

-- C と C' は等しい
theorem c_eq_c' (n k : ℕ) : C n k = C' n k := by
  -- n に関する帰納法で示す
  induction n generalizing k
  case zero => -- n = 0 の場合
    show C 0 k = C' 0 k
    -- k = 0 が成り立つかどうかで場合分け
    apply dite (k = 0)
    -- どちらにしても計算すればわかる
    case t | e => intro h; simp [h]
  case succ n' ih => -- n = n' + 1 の場合
    -- ih : ∀ k, C n k = C' n k
    show C (n' + 1) k = C' (n' + 1) k
    -- k について場合分け
    cases k
    case zero => -- k = 0 の場合
      show 1 = C' (n' + 1) 0
      -- 補題 c_n_zero_eq_one (n' + 1) より従う
      rw [c_n_zero_eq_one (n' + 1)]
    case succ k' => -- k = k' + 1 の場合
      -- 帰納法の仮定より成り立つ
      simp
      show C n' k' + C n' (k' + 1) = C' n' k' + C' n' (k' + 1)
      simp [ih, ih]

-- C' n k = C' n (n - k)
lemma c_rev (n : ℕ) (k : ℤ) : C' n k = C' n (n - k) := by
  -- n に関する帰納法で示す
  induction n generalizing k
  case zero => -- n = 0 の場合
    show C' 0 k = C' 0 (0 - k)
    -- 計算すればわかる
    simp
  case succ n' ih => -- n = n' + 1 の場合
    -- ih : ∀ k, C' n' k = C' n' (n' - k)
    -- 計算
    calc
        C' (n' + 1) k
      = C' n' (k - 1) + C' n' k               := rfl
    _ = C' n' (n' - (k - 1)) + C' n' (n' - k) := by rw [ih (k-1), ih k]
                                              -- 帰納法の仮定より
    _ = C' n' ((n' + 1) - k) + C' n' (((n' + 1) - k) - 1)
                                            := by congr 2; repeat linarith
                                            -- 形を整える
    _ = C' n' (((n' + 1) - k) - 1) + C' n' ((n' + 1) - k)
                                            := by rw [add_comm]
                                            -- 項を入れ替える
    _ = C' (n' + 1) ((n' + 1) - k)           := rfl

-- これにより先の補題の対称版が示せる
-- k > n ならば C' n k = 0
lemma c_n_k_eq_zero_of_k_gt_n (n : ℕ) (k : ℤ) : k > n → C' n k = 0 := by
  intro (h : k > n)
  have h' : n - k < 0 := calc
    n - k < k - k := sub_lt_sub_right h k
    _     = 0     := by simp
  rw [c_rev]
  exact c_n_k_eq_zero_of_k_neg n (n - k) h'

-- C' n n = 1
lemma c_n_n_eq_one (n : ℕ) : C' n n = 1 := by
  rw [c_rev]
  simp
  exact c_n_zero_eq_one n

-- C' n 1 = n
theorem c_n_one_eq_n (n : ℕ) : C' n 1 = n := by
  induction n
  case zero =>
    simp
  case succ n' ih =>
    -- ih : C' n' 1 = n'
    calc
        C' (n' + 1) 1
      = C' n' 0 + C' n' 1 := rfl
    _ = 1 + n'          := by rw [c_n_zero_eq_one n', ih]
    _ = n' + 1          := by rw [add_comm]

-- C' n (n - 1) = n
theorem c_n_prec_eq_n (n : ℕ) : C' n (n - 1) = n := by
  rw [c_rev]
  simp
  exact c_n_one_eq_n n

/-
  二項定理
  
    (a + b)^n = ∑ k ≤ n, C' n k * a^k * b^(n - k)

  が任意の可換環 R において成り立つことを示す．
-/

open BigOperators
open Std.ExtendedBinder

-- Mathlib.Algebra.BigOperators.Basic では有限集合 s に亙る総和の記法
-- ∑ k in s, f k
-- が定義されている．
-- ここでは新たに ∑ k ≤ n, f k という記法を定義しておく．

syntax (name := bigsumle) "∑ " ident " ≤ " term "," term:67 : term
macro_rules (kind := bigsumle)
  | `(∑ $x:ident ≤ $s, $r) => `(Finset.sum (.range ($s + 1)) (fun $x ↦ $r))

#eval let n := 5; ∑ x ≤ n, C' n x -- 32

-- 二項定理
theorem binomial_thm {R} [CommRing R] (a b : R) (n : ℕ)
  : (a + b)^n = ∑ k  ≤ n, C' n k * a^k * b^(n - k)
  := by
  -- n に関する帰納法で示す
  induction n
  case zero => -- n = 0 の場合
    show (a + b)^0 = ∑ k ≤ 0, C' 0 k * a^k * b^(0 - k)
    -- 計算すればわかる
    simp
  case succ n' ih => -- n = n' + 1 の場合
    -- ih : (a + b) ^ n' = ∑ k in .range n', C' n' k * a ^ k * b ^ (n' - k)
    -- ひたすら計算する
    -- ところどころ強いタクティクを使ってはいるが，一つ一つの式変形は難しいものではない
    calc
        (a + b) ^ (n' + 1)
        -- (a + b) をひとつ取り出す
      = (a + b) ^ n' * (a + b)
        := pow_succ' (a + b) n'
        -- 帰納法の仮定により (a + b) ^ n' を置き換える
    _ = (∑ k ≤ n', C' n' k * a ^ k * b ^ (n' - k)) * (a + b)
        := by simp [ih]
        -- (∑ f) * (a + b) = ∑ (f * (a + b))
    _ = ∑ k ≤ n',
          C' n' k * a ^ k * b ^ (n' - k) * (a + b)
        := by apply Finset.sum_mul
        -- 分配法則で展開したのち整理する
        -- (ring_nf: 等式の左辺を環の公理で整理する)
    _ = ∑ k ≤ n',
          ( C' n' k * a ^ (k + 1) * b ^ (n' - k)
          + C' n' k * a ^ k * b ^ (n' - k + 1) )
        := by ring_nf; apply Eq.symm; ring_nf
        -- 指数の部分を変形
    _ = ∑ k ≤ n',
          ( C' n' k * a ^ (k + 1) * b ^ ((n' + 1) - (k + 1))
          + C' n' k * a ^ k * b ^ ((n' + 1) - k) )
        := by
          apply Finset.sum_congr rfl
          intro k h; simp at h
          have h' : k ≤ n' := Nat.le_of_lt_succ h
          congr 3
          rw [Nat.succ_sub_succ_eq_sub]
          rw [Nat.sub_add_comm h']
        -- ∑ (f + g) = (∑ f) + (∑ g)
    _ = ( ∑ k ≤ n',
            C' n' k * a ^ (k + 1) * b ^ ((n' + 1) - (k + 1)) )
        + ∑ k ≤ n',
            C' n' k * a ^ k * b ^ ((n' + 1) - k)
          := by apply Finset.sum_add_distrib
        -- 和の一つ目を変形
    _ = ( ∑ k ≤ n',
            C' n' ((1 + k) - 1) * a^(1 + k) * b^((n' + 1) - (1 + k)) )
        + ∑ k ≤ n',
            C' n' k * a^k * b^((n' + 1) - k)
          := by
            congr 1
            . apply Finset.sum_congr rfl
              intro k h; simp at h
              simp
              congr 2
              . congr 1
                show k + 1 = 1 + k
                simp [add_comm]
              . show n' - k = n' + 1 - (1 + k)
                apply Eq.symm
                calc
                    n' + 1 - (1 + k)
                  = n' + 1 - (k + 1) := by simp [add_comm]
                _ = n' - k           := by rw [Nat.succ_sub_succ_eq_sub]
        -- 一つ目の和の先頭に 0 と等しい項を追加して一つの和にまとめる
    _ = ( ∑ k ≤ 0,
            C' n' (k - 1) * a^k * b^((n' + 1) - k)
        + ∑ k ≤ n',
            C' n' ((1 + k) - 1) * a^(1 + k) * b^((n' + 1) - (1 + k)) )
        + ∑ k ≤ n', C' n' k * a^k * b^((n' + 1) - k)
          := by simp [c_n_k_eq_zero_of_k_neg n' (-1)]
    _ = ( ∑ k ≤ n' + 1, C' n' (k - 1) * a^k * b^((n' + 1) - k) )
        + ∑ k ≤ n', C' n' k * a^k * b^((n' + 1) - k)
          := by
            let f := λ k : ℕ ↦ C' n' (k - 1) * a^k * b^((n' + 1) - k)
            have :
              ( ∑ k ≤ 0, C' n' (k - 1) * a^k * b^((n' + 1) - k)
              + ∑ k ≤ n', C' n' ((1 + k) - 1) * a^(1 + k) * b^((n' + 1) - (1 + k)) )
              = ∑ k ≤ n' + 1, C' n' (k - 1) * a^k * b^((n' + 1) - k)
              := calc
                  (∑ k ≤ 0, f k) + ∑ k ≤ n', f (1 + k)
                = ∑ k in .range (1 + (n' + 1)), f k
                  := by simp only [Finset.sum_range_add f 1 (n' + 1)]
              _ = ∑ k ≤ n' + 1, f k
                  := by congr 2; simp [Nat.add_comm]
            rw [this]
        -- 二つ目の和の末尾に 0 と等しい項を追加して一つの和にまとめる
    _ = ( ∑ k  ≤ n' + 1, C' n' (k - 1) * a^k * b^((n' + 1) - k) )
        + ( ∑ k  ≤ n', C' n' k * a^k * b^((n' + 1) - k)
          + C' n' (n' + 1) * a^(n' + 1) * b ^((n' + 1) - (n' + 1)) )
          := by simp [c_n_k_eq_zero_of_k_gt_n n' (n' + 1) (by simp)]
    _ = ( ∑ k  ≤ n' + 1, C' n' (k - 1) * a^k * b^((n' + 1) - k) )
        + ∑ k  ≤ n' + 1, C' n' k * a^k * b^((n' + 1) - k)
          := by simp [Finset.sum_range_succ]
        -- (∑ f) + (∑ g) = ∑ (f + g)
    _ = ∑ k  ≤ n' + 1,
          ( C' n' (k - 1) * a^k * b^((n' + 1) - k)
          + C' n' k * a^k * b^((n' + 1) - k) )
          := by simp [Finset.sum_add_distrib]
        -- 分配法則
    _ = ∑ k  ≤ n' + 1,
          (C' n' (k - 1) + C' n' k) * a^k * b^((n' + 1) - k)
          := by simp [add_mul]
        -- C' n' (k - 1) + C' n' k = C' (n' + 1) k
    _ = ∑ k  ≤ n' + 1,
          C' (n' + 1) k * a^k * b^((n' + 1) - k)
          := by simp
-- QED

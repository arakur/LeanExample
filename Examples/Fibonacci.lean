import Mathlib.Data.Nat.Basic

-- Fibonacci 数列の定義
def fib : ℕ → ℕ
| 0 => 0 -- 0 番目の要素は 0
| 1 => 1 -- 1 番目の要素は 1
| n + 2 => fib n + fib (n + 1)
  -- (n+2) 番目の要素は n 番目の要素と (n+1) 番目の要素の和

-- 上の定義の本来の形は以下のようになる
-- match の文脈では n+2 を自動的に .succ (.succ n) と見做してくれる(頭がいい)
def _fibExpl : ℕ → ℕ := λ n ↦ match n with
| .zero => .zero
| .succ .zero => .succ .zero
| .succ (.succ n) => _fibExpl n + _fibExpl (.succ n)

#eval fib 10 -- 55
-- 現在の定義は無駄な再帰を行うので少し数が大きくなるだけで遅くなる
#eval fib 30 -- 832040
-- #eval fib 35

-- 以下のように書き換えてみる
-- まず，n 番目の要素と (n+1) 番目の要素をペアで表し，次のペアを計算する関数 fib'Step を定義する
def fib'Step : ℕ × ℕ → ℕ × ℕ
| (a, b) => (b, a + b)

-- fib'Step を n 回繰り返す関数 fib'Inner を定義する
def fib'Inner : ℕ → ℕ × ℕ → ℕ × ℕ
| 0, p => p
| n + 1, p => fib'Inner n (fib'Step p)

-- 最後に，(0, 1) を初期値として fib'Inner を計算し，結果のペアの1つ目の値を返す
def fib' : ℕ → ℕ
| n => (fib'Inner n (0, 1)).1

-- こちらは大きい数でも高速に計算できる
#eval fib' 10 -- 55
#eval fib' 35 -- 9227465
#eval fib' 100 -- 354224848179261915075
#eval fib' 1000 -- 4346655768693743...

-- これらの定義が同じ数列を定めることを証明する
-- まずは，fib'Inner の定義を反転させても結果が等しいことを示す
-- (初めからこうしないのは末尾再帰にするため)
lemma fib'Inner_rev : fib'Inner (n + 1) p = fib'Step (fib'Inner n p) := by
  induction n generalizing p
  case zero => simp [fib'Inner]
  case succ n ih =>
    -- ih : ∀ {p}, fib'Inner (n + 1) p = fib'Step (fib'Inner n p)
    calc
    fib'Inner (n + 1 + 1) p
      = fib'Inner (n + 1) (fib'Step p) := by rw [fib'Inner]
    _ = fib'Step (fib'Inner n (fib'Step p)) := ih
    _ = fib'Step (fib'Inner (n + 1) p) := by rw [fib'Inner]

theorem fib_eq_fib' : fib = fib' := by
  -- 2つの関数 Fib, FaseFib が等しいことを示すために，任意の n に対して fib n = fib' n が成り立つことを証明する
  funext n
  show fib n = fib' n
  -- n に関する帰納法で示す
  -- Nat.two_step_induction を使い，n=0, n=1 の場合を示した後，n=k, n=k+1 の場合を仮定して n=k+2 の場合を示す
  induction n using Nat.two_step_induction
  case H1 | H2 => -- n = 0 または n = 1 の場合
    -- これらの場合は実際に両辺を計算すれば証明できる
    simp [fib, fib']
  case H3 k ih₀ ih₁ => -- n = k + 2 の場合
    -- ih₀ : fib k = fib' k
    -- ih₁ : fib (k + 1) = fib' (k + 1)
    show fib (k + 2) = fib' (k + 2)
    -- 名前が長いので省略
    let i := fib'Inner; let s := fib'Step
    -- 左辺を式変形して右辺に書き換える
    -- (p.1 はペアの1つ目の要素，p.2 は2つ目の要素を表す)
    calc
      fib (k + 2)
        = fib k + fib (k + 1)                   := by simp [fib]
                                                -- fib の定義より
      _ = fib' k + fib' (k + 1)                 := by simp [ih₀, ih₁]
                                                -- 帰納法の仮定より
      _ = (i k (0, 1)).1 + (i (k + 1) (0, 1)).1 := by simp [fib', fib'Inner]
                                                -- fib', fib'Inner の定義より
      _ = (i k (0, 1)).1 + (s (i k (0, 1))).1   := by simp [fib'Inner_rev]
                                                -- 補題 fib'Inner_rev より
      _ = (i k (0, 1)).1 + (i k (0, 1)).2       := by simp [fib'Step]
                                                -- fib'Step の定義より
      _ = (s (i k (0, 1))).2                    := by simp [fib'Step]
                                                -- fib'Step の定義より
      _ = (s (s (i k (0, 1)))).1                := by simp [fib'Step]
                                                -- fib'Step の定義より
      _ = (i (k + 2) (0, 1)).1                  := by simp [fib'Inner_rev]
                                                -- 補題 fib'Inner_rev より
      _ = fib' (k + 2)                          := by simp [fib']
                                                -- fib' の定義より
-- QED

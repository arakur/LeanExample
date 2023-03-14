import Std.Data.Rat.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Qify

/-
有理数 r : ℚ は以下の4つのフィールドからなる構造体である：

  r.num : ℤ -- 分子；
  r.den : ℕ -- 分母；
  r.den_nz : r.den ≠ 0 -- 分母は0でない；
  r.reduced : Nat.coprime (r.num.natAbs) (r.den) -- 分子と分母は互いに素．

Lean では，ℤ 型の期待される場所に ℕ 型の値が現れた場合などに自動的に型強制(type coercion)を行う機能が備わっているが，それでも ℕ 型と ℤ 型と ℚ 型の値が入り乱れると明示的な型変換を挟む必要があるなどやや面倒がある．
そのため，分母を単に ℤ 型に変換して返す関数 Rat.den' と，Rat.num と Rat.den' が互いに素であるという仮定 Rat.reduced' を定義して用いる．

なお，有理数をそのまま cases すると上記の4つのフィールドを直に取り出せるが，有理数型の生のコンストラクタに対する操作はかなり複雑で関連する lemma も少なく詰みやすいため，後に行うようにフィールドは let で束縛した上で本体に対しては Std.Data.Rat.Lemmas の補題などを用いていくほうがよいと思われる．
-/

@[simp]
def Rat.den' (r : ℚ) : ℤ := r.den

lemma Rat.reduced' (r : ℚ) : r.num.natAbs.coprime r.den'.natAbs := by
  simp; exact r.reduced

/-
さらに補題を一つ示しておく：a, b, c : ℕ について，a * b と a * c が互いに素ならば a = 1 .
-/
lemma Nat.coprime_mul_imp_one (a b c : ℕ) : (a * b).coprime (a * c) → a = 1 := by
  --　a * b と a * c が互いに素と仮定する
  intro (h : (a * b).coprime (a * c))
  show a = 1
  -- a * b と a * c が互いに素より a と a * c は互いに素
  have : a.coprime (a * c) := by
    exact Nat.coprime.coprime_mul_right h
  -- a と a * c が互いに素より a と a は互いに素
  have : a.coprime a := by
    rw [Nat.coprime_comm] at this
    exact Nat.coprime.coprime_mul_right this
  -- ゆえに a = 1
  exact a.coprime_self.mp this

/-
定理: 任意の有理数は二乗して2にはならない．
-/
theorem rat_not_sqrt2 (r : ℚ) : r * r ≠ 2 := by
  -- r * r = 2 と仮定して矛盾を導く
  intro (h : r * r = 2)
  show False
  -- p/q := r (p,q : ℤ, q ≠ 0 かつ h_red : p, q は互いに素) とおく
  let p : ℤ := r.num
  let q : ℤ := r.den'
  have h_red : p.natAbs.coprime q.natAbs := r.reduced'
  -- p,q の定義より p = r * q
  have : p = r * q := by simp
  -- r * r = 2 より p * p = 2 * q * q
  have hpq : p * p = 2 * q * q := by
    -- 主張を ℤ におけるものから ℚ におけるものに変換する
    qify
    -- あとは計算
    calc p * p
        = (r * q) * (r * q) := by rw [this] -- p = r * q より
      _ = (r * r) * q * q   := by linarith  -- 適切に変形する
      _ = 2 * q * q         := by rw [h]
  -- 2 ∣ p を示す
  have : 2 ∣ p * p := by
    -- hpq で p * p を 2 * q * q に置き換える
    rw [hpq, Int.mul_assoc]
    show 2 ∣ 2 * (q * q)
    -- 結論が a ∣ a * b の形なので成り立つ
    exact dvd_mul_right 2 (q * q)
  have : 2 ∣ p := by
    -- 2 ∣ p * p より 2 ∣ p または 2 ∣ p，
    have : 2 ∣ p ∨ 2 ∣ p := Int.prime_two.dvd_or_dvd this
    -- よっていずれの場合も 2 ∣ p
    cases this; repeat assumption
  -- よってある p' が存在して p = 2 * p' である
  cases this with | intro p' hp' =>
  -- hp' : p = 2 * p'
  -- 同様に 2 ∣ q を示していく
  have : q * q = 2 * (p' * p') := by
    -- 2 ≠ 0 かつ 2 * (q * q) = 2 * (2 * (p' * p')) より
    -- q * q = 2 * (p' * p') がいえる
    have h₀ : (2 : ℤ) ≠ 0 := by simp
    have h₁ : 2 * (q * q) = 2 * (2 * (p' * p')) := calc
      2 * (q * q)
        = 2 * q * q           := by rw [Int.mul_assoc]
      _ = p * p               := by rw [hpq]
      _ = (2 * p') * (2 * p') := by rw [hp']
      _ = 2 * (2 * (p' * p')) := by linarith
    exact Int.eq_of_mul_eq_mul_left h₀ h₁
  -- あとは p の場合と同様
  have : 2 ∣ q * q := by
    rw [this]
    exact dvd_mul_right 2 (p' * p')
  have : 2 ∣ q := by
    have : 2 ∣ q ∨ 2 ∣ q := Int.prime_two.dvd_or_dvd this
    cases this; repeat assumption
  -- よってある q' が存在して q = 2 * q' である
  cases this with | intro q' hq' =>
  -- hq' : q = 2 * q'
  -- すると 2 * |p'| と 2 * |q'| が互いに素であることになる
  have : (2 * p'.natAbs).coprime (2 * q'.natAbs) := by
    have : ∀ x : ℤ, (2 * x).natAbs = 2 * x.natAbs := by
      intro x
      calc (2 * x).natAbs
        = (2 : ℤ).natAbs * x.natAbs := Int.natAbs_mul 2 x
      _ = 2 * x.natAbs              := by simp
    rw [←this p', ←this q', ←hp', ←hq']
    show p.natAbs.coprime q.natAbs
    exact h_red
  -- よって補題 Nat.coprime_mul_imp_one から矛盾が導かれる
  have : 2 = 1 := by
    exact Nat.coprime_mul_imp_one 2 p'.natAbs q'.natAbs this
  contradiction
-- QED

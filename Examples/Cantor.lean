import Mathlib.Init.Set

-- Set α は α の部分集合全体を表す
#check Set Nat -- Set Nat : Type

-- 関数 f の値域 range f を定義する
def range (f : α → β) : Set β := { b : β | ∃ a : α, f a = b }

-- 関数 f が全射であるとは， f の値域が全体集合(Set.univ)であることをいう
def surjective (f : α → β) : Prop := range f = Set.univ

-- Cantor の定理: 全射 f : α → Set α は存在しない
theorem cantor : ¬ ∃ f : α → Set α, surjective f := by
  -- 全射 f : α → Set α が存在すると仮定して矛盾(False)を示せばよい
  intro (h : ∃ f, surjective f)
  show False
  -- 仮定 h から関数 f と仮定 hf :surjective f を取り出す
  cases h with | intro f hf =>
  -- ここから対角線論法で矛盾を導く
  -- 集合 S を，元 a : α で集合 f a が自分自身を含まないものの集合と定義する
  let S : Set α := { a : α | a ∉ f a }
  -- f は全射なので S ∈ range f である
  have hS₀ : S ∈ range f := by
    -- surjective の定義を展開する
    simp [surjective] at hf
    -- すると hf : range f = Set.univ となる
    -- これで結論を書き換える
    rw [hf]
    show S ∈ Set.univ
    -- 全体集合は全ての要素を含むので，結論は明らかに成り立つ
    trivial
  -- 従ってある a : α が存在して f a = S である
  have hS : ∃ a : α, f a = S := by
    -- さきほど示した hS₀ : S ∈ range f における range の定義を展開する
    unfold range at hS₀
    -- すると hS₀ : S ∈ { b | ∃ a, f a = b } となり，結論が得られる
    exact hS₀
  -- 再び存在の仮定 hS から元 a と仮定 haS : f a = S を取り出す
  cases hS with | intro a haS =>
  -- 取り出した a について，a ∈ f a の場合と a ∉ f a の場合に場合分けして，それぞれで矛盾を導く
  by_cases ha : a ∈ f a
  case inl => -- a ∈ f a の場合
    -- 仮定 a ∈ f a および haS : f a = S より a ∈ S である
    have : a ∈ S := by rw [haS] at ha; exact ha
    -- すると S の定義より a ∉ f a である
    have : a ∉ f a := by
      exact this
    -- 従って矛盾する
    contradiction
  case inr => -- a ∉ f a の場合
    -- 仮定 a ∉ f a および haS : f a = S より a ∉ S である
    have : a ∉ S := by rw [haS] at ha; exact ha
    -- すると S の定義より a ∉ f a ではない，すなわち a ∈ f a である
    have : a ∈ f a := by
      exact Classical.byContradiction this
    -- 従って矛盾する
    contradiction
  -- QED


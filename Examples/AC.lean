import Mathlib.Tactic.Choose

/-
  大雑把に言えば，選択公理とは仮定
  
    ∀ x, ∃ y, ~~~

  から結論

    ∃ y(x), ∀ x, ~~~

  を得ることができるというものである．
-/

-- theorem axiomOfChoice
--   {α : Sort u} {β : α → Sort v}
--   {r : ∀ x, β x → Prop}
--   (h : ∀ x, ∃ y, r x y) :
--   ∃ (f : ∀ x, β x), ∀ x, r x (f x)
#check Classical.axiomOfChoice

/-
  Classical.axiomOfChoice は我々が見慣れた形に整形されたもので，大元にあるのは Classical.choice という axiom である．
  これは

    型 α が空ではない (Nonempty α)
  
  という仮定から実際に型 α の値をひとつ得る関数 Nonempty α → α である．
-/

-- axiom Classical.choice {α : Sort u} :
--   Nonempty α → α
#check Classical.choice

#check Nonempty

/-
  Mathlib.Tactic.Choose にある choose タクティクを使うと，仮定

    ∀ x₁ ... xₙ, ∃ y₁ ... yₘ, r x₁ ... xₙ y₁ ... yₘ
  
  から以下を得ることができる：

    yᵢ :
      x₁ → ... → xₙ → βᵢ (i = 1, ..., m)
    hy :
      ∀ x₁ ... xₙ,
        r x₁ ... xₙ (y₁ x₁ ... xₙ) ... (yₘ x₁ ... xₙ)
  
  これにより，Mathlib 下ではフランクに選択公理を用いた証明を遂行することが可能である．勿論，組み込みの Choose.axiomOfChoice を直接呼び出してもよい．
-/

theorem ex₀
  (r : α₁ → α₂ → β₁ → β₂ → Prop)
  (h : ∀ (x₁ : α₁) (x₂ : α₂),
        ∃ (y₁ : β₁) (y₂ : β₂),
          r x₁ x₂ y₁ y₂) :
  ∃ (y₁ : α₁ → α₂ → β₁) (y₂ : α₁ → α₂ → β₂),
    ∀ (x₁ : α₁) (x₂ : α₂),
      r x₁ x₂ (y₁ x₁ x₂) (y₂ x₁ x₂)
  := by
  -- h に選択公理を適用
  choose y₁ y₂ hy using h
  -- 以下を得る：
  -- y₁ : α₁ → α₂ → β₁
  -- y₂ : α₁ → α₂ → β₂
  -- hy : ∀ x₁ x₂, r x₁ x₂ (y₁ x₁ x₂) (y₂ x₁ x₂)
  exists y₁, y₂

/-
  要するに，各 x に対して条件を満たす要素 y が「存在する」と主張されている中，実際に y を「選ぶ」ことができると主張するのが選択公理である．
  選択公理を用いたかどうかは，使用した公理の一覧を表示する #print axioms で確認できる．
  これにより，選択公理を用いない証明を行いたいという場合に特定の補題を用いてもよいかどうか判断することができる．
-/
#print axioms ex₀
-- => 'ex₀' depends on axioms: [Classical.choice]

/-
  選択公理を使うと排中律 p ∨ ¬ p が証明できる．
  参考: https://plato.stanford.edu/entries/axiom-choice/#AxiChoLog
-/

def ac := ∀ {α : Type} {β : Type} (r : α → β → Prop), (∀ x, ∃ y, r x y) → ∃ f : α → β, ∀ x, r x (f x)

def lem := ∀ p, p ∨ ¬ p

-- 2つの要素 t, f からなる型 T を定義する
inductive T := | t | f

-- 選択公理を用いて排中律を証明する
theorem ac_implies_lem : ac → lem := by
  -- 選択公理を仮定
  intro (hac : ac)
  -- 命題 p を任意に取る
  intro p

  -- まず，2つの関数 U, V : T → Prop を定義する
  let U : T → Prop := λ x ↦ x = .f ∨ p
  let V : T → Prop := λ x ↦ x = .t ∨ p
  -- 関数 χ : T → Prop に対して命題 Φ χ を定義する
  let Φ (χ : T → Prop) : Prop := χ = U ∨ χ = V

  -- 命題 Φ χ が成り立つような χ : T → Prop からなる部分型を TPΦ とおく
  let TPΦ := {χ : T → Prop // Φ χ}
  -- (部分型(Subtype) {x : T // p x} は値 val : T と条件 property : p val の組 ⟨ val, property ⟩ からなる型)
  -- Φ, U, V の定義より Φ (U) と Φ (V) は明らかに成り立つ
  have hU : Φ (U) := by simp
  have hV : Φ (V) := by simp
  -- よって U, V を TPΦ の元にできる
  let U' : TPΦ := ⟨ U, hU ⟩
  let V' : TPΦ := ⟨ V, hV ⟩

  -- ⟨χ, hχ⟩ : TPΦ に対して χ x が真となるような x : T を選ぶ関数を作るために選択公理を用いる
  -- そのためにまず関数 r : TPΦ → T → Prop を定義する
  let r (χ_hχ : TPΦ) (x : T) : Prop := χ_hχ.val x
  -- 選択公理の仮定が成り立つことを示す
  have : ∀ χ_hχ : TPΦ, ∃ x, r χ_hχ x := by
    -- χ_hχ を値 χ : T → Prop と条件 hχ : Φ χ に分解する
    intro ⟨ χ, (hχ : Φ χ) ⟩
    show ∃ x, χ x
    -- Φ の定義を展開すると hχ : χ = U ∨ χ = V となる
    have : χ = U ∨ χ = V := hχ
    cases this
    case inl hχₗ => -- χ = U の場合
      -- hχₗ ; χ = U
      -- U x := x = .f ∨ p なので，x = .f とすれば明らか
      exists .f
      rw [hχₗ]; simp
    case inr hχᵣ => -- χ = V の場合
      -- hχᵣ ; χ = V
      -- この場合も同様で，今度は x = .t とする
      exists .t
      rw [hχᵣ]; simp
  -- r に関する選択公理を使う
  cases hac r this with | intro x hx =>
  -- 以下を得る：
  -- x : { χ // Φ χ } → T
  -- hx : ∀ (χ_hχ : { χ // Φ χ }), r χ_hχ (x χ_hχ)

  -- hx を整理する
  simp at hx
  -- hx : ∀ (χ_hχ : { χ // Φ χ }), χ.val (x χ hχ)
  -- hx を U', V' に適用して以下を得る
  have hxU : U (x U') := hx U'
  have hxV : V (x V') := hx V'
  -- 整理すると以下のようになる
  have hxU' : x U' = .f ∨ p := hxU
  have hxV' : x V' = .t ∨ p := hxV

  -- hxU', hxV' それぞれについて，左右どちらが成り立つかで場合分け
  cases hxU'
  case inr => left; assumption -- p が成り立つ場合(明らかに p ∨ ¬ p)
  case inl h₁ => -- x U' = .f の場合
    cases hxV'
    case inr => left; assumption -- p が成り立つ場合(明らかに p ∨ ¬ p)
    case inl h₂ => -- x U' = .t の場合
      -- h₁ : x U' = .f
      -- h₂ : x V' = .t
      -- このとき，¬ p を示すことができる
      right; show ¬ p
      -- p と仮定して矛盾を導く
      intro (hp : p)
      show False
      -- いま，p が成り立つので任意の x に対して U x が成り立つ
      have hU' : ∀ x, U x = True := by
        intros; simp; right; assumption
      -- 同様に任意の x に対して V x が成り立つ
      have hV' : ∀ x, V x = True := by
        intros; simp; right; assumption
      -- よって U = V が成り立つ
      have : U = V := by
        funext x; rw [hU' x, hV' x]
      -- ゆえに U' = V' も成り立つ
      have : U' = V' := by
        simp only [this]
      -- 従って，x U' hU = x V' hV が成り立つ
      have : x U' = x V' := by
        simp only [this]
      -- よって h₁, h₂ より T.t = T.f が示される
      have : T.t = T.f := by
        rw [← h₁, ← h₂, this]
      -- これは矛盾
      contradiction

-- 仮定した選択公理以外の公理を使っていないか確認
#print axioms ac_implies_lem
-- => 'lem' depends on axioms: [propext, Quot.sound]

/-
  Classical.choice は現れていないが，2つの公理が必要になっていることがわかる
  この2つの公理は以下の要請で，ロジックの観点では重要な代物だが，通常の数学をやる上ではそれほど気にしなくていいと思われる

  - propext ... 同値な2つの命題は「等しい」: (a ↔ b) → a = b
  - Quot.sound ... 商型(Quotient type)の要素の等しさを定める: r a b → Quot.mk r a = Quot.mk r b
-/

#print propext
#print Quot.sound

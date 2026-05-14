/-
対偶の片側は排中律なしで証明できるので、依存関係なくして学べる良い例らしい。
僕が知っている証明方法は、古典論理の中でA -> Bが ¬A ∨ Bであるという定義使って真理値表を書いて同値性を確かめること。
Leanによるプログラミングでなぜそれを証明できるのかを知りたい。
ラムダ計算とかCICとかカリー＝ハワード同型対応とかが何か重要な概念であると聞いたことあるけど、今は何も知らない。
あと、対偶のもう片側の証明は排中律が必要になるらしい
-/

theorem taigu_1 (A B: Prop): (A → B) → (¬B → ¬A) := by
  intro apple
  intro banana
  intro coffee
  apply banana
  apply apple
  exact coffee
/-
これでエディタが赤くならなくなった。これをGoalが閉じるとか、Type checkが通っているというらしい。
intro, apply, exactって何？なんでこれが証明になっているの？
introはこの場合3つ書くことが確定しているの？
¬X は X → FalseのSyntax Suger的なものと聞いたので、それを信じて展開してみる
-/
theorem taigu_2 (A B: Prop): (A → B) → ((B → False) → (A → False)) := by
  intro apple -- ここにカーソル当てたら、Goalは(B → False) → A → Falseになった
  intro banana -- ここにカーソル当てたら、GoalはA → Falseになった
  intro coffee -- ここにカーソル当てたら、GoalはFalseとなった
  -- introというのは、X → YというGoalに対してXに名前をつけて前提にし、Goalをより単純なYにする操作のことっぽい
  -- ここからappleとbananaとcoffeeという前提を使ってFalse"作る"(?)ことをすればGoalが閉じるらしい
  -- applyが何か知らないけど、次はそれを使うらしい
  -- ここで`apply apple`としたら、Tactic `apply` failed: could not unify the conclusionというエラーになった
  -- 前提の中に"False"が含まれているのはbanana: B → Falseだけだから、次の一手はそれに確定するっぽい
  apply banana -- GoalはBになった
  apply apple -- GoalはAになった
  -- applyというのは、YというGoalに対してX → Yという前提を作用させることで、XをGoalにする操作のことっぽい
  exact coffee -- Goalがcoffeeと一致することがなぜか嬉しいらしく、こうすると証明完了らしい
  -- これを、`exact apple`としたらそれは違うと怒られた。そのエラーメッセージは理解できた
/-
ここまでの理解の進展
- intro, apply, exactがどういうものかが分かった
- この場合、introは最大3つまでかけるが、4つは書けない。
  - 3つ全部使ってできるだけ前提をバラバラにしているのは初学の時点では明示性の観点から適切だと思った
  - でも、2つだけ、1つだけで証明できるのかは知らない
- introもapplyも`→`に作用するから、¬X を X → Falseと定義する必然性を感じた

だけど、なんでこれが証明になってるの？初めて帰納法を教わった時のような感覚。
-/

-- [tsでも似たようなことができるのを確認](./taigu.ts)したので、これはシンプルにこう書けることがわかった
theorem taigu_raw (A B: Prop): (A → B) → (B → False) → (A → False) :=
  fun hab hb ha => hb (hab ha)
-- by introとかいうのはTacticといって、こういう生の証明関数が辛くなる時に活躍するマクロのようなもの
-- 今回はむしろ生の証明がとても単純に終わったけど、Tacticの充実が証明支援システムに重要な役割を担っているのを感じた
-- #print axioms taigu_raw -- どの公理も使っていない（CICが公理）


/-
とりあえず「なんでそれで証明になってるの？」という疑問は置いておいて、上の逆を示す
Lean4では排中律を古典的公理ではなく、
古典の公理を[choice](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice)としている。ZFCのCとは厳密には違うっぽいけど型理論を知ってないと理解できなそうな感じだった。
排中律thorem Classical.em (p : Prop) : p ∨ ¬pは、Classical.ChoiceからDiaconescuの定理とやらで証明されるらしい。
Leanでは他にpropext(外延性公理)とQuot.sound(商型の健全性公理)にも依存しているらしい
それらの定義は以下のとおり：
axiom Classical.choice {α : Sort u} : Nonempty α → α
axiom propext {a b : Prop} : (a ↔ b) → a = b
axiom sound : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b
よく分かんないけど、propextだけは「マジかそんなことも構成論理じゃ言えないの？」って思った。
-/

theorem taigu_gyaku_1 (A B : Prop): (¬B → ¬A) → (A → B) := by
  intro h1
  intro ha
  have hem : B ∨ ¬B := Classical.em B -- haveの説明は後で
  apply Or.elim hem -- ∨ がある命題を2つに分割する
  ·
    intro hb
    exact hb -- この命題hbが真であることを提出
  ·
    intro hnb
    have hna : ¬A := h1 hnb
    -- haveとは、const hna = h1(hnb)みたいに結果を新た名前で前提に追加する操作のこと
    -- これは1行だけだから明示性のためでしかないけど、複数行で := by ...と小さな証明問題を始める時に便利
    have hfalse : False := hna ha
    exact False.elim hfalse -- hFalse(矛盾)からはどんな命題（今回はB）も導ける
    -- いまいちしっくりこないけど、まあそういうもんだと思うことにする
-- #print axioms taigu_gyaku_1 -- propext, Classical.choice, Quot.sound
-- #print axioms Or.elim -- no axioms
-- #print axioms Classical.em -- propext, Classical.choice, Quot.sound

-- だからTacticを使わないとこう書ける
theorem taigu_gyaku_raw (A B : Prop): (¬B → ¬A) → (A → B) :=
  fun h1 ha =>
    Or.elim (Classical.em B)
      (fun hb => hb)
      (fun hnb => False.elim (h1 hnb ha))

--　by_casesというTacticがあるが、
-- Classicalを使っていないように見せかけて排中律まんま使ってる
theorem taigu_gyaku_2 (A B: Prop): (¬B -> ¬A) → (A → B) := by
  intro h1
  intro ha
  by_cases hb: B
  .
    exact hb
  .
    have hna: ¬A := h1 hb -- こちらの分岐でhbが¬Bになる
    have hfalse: False := hna ha
    exact False.elim hfalse
-- #print axioms taigu_gyaku_2

-- 矛盾も古典論理で、それを使うと見かけ上分岐なしで書ける
theorem taigu_gyaku_3 (A B: Prop): (¬B → ¬A) → (A → B) := by
  intro h1
  intro ha
  apply Classical.byContradiction -- GoalがBから ¬B → False になる
  intro hnb
  have hna : ¬A := h1 hnb
  exact hna ha
-- #print axioms taigu_gyaku_3
-- #print axioms Classical.byContradiction

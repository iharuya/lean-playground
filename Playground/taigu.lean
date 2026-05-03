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
/--
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


namespace MultiJanken

inductive Hand where
  | rock
  | scissors
  | paper
  deriving Repr, DecidableEq

def Hand.toString : Hand → String
  | .rock     => "rock"
  | .scissors => "scissors"
  | .paper    => "paper"

instance : ToString Hand where
  toString := Hand.toString

def Hand.ofString? : String → Option Hand
  | "rock"     => some .rock
  | "scissors" => some .scissors
  | "paper"    => some .paper
  | _          => none

def Hand.beats : Hand → Hand → Bool
  | .rock,     .scissors => true
  | .scissors, .paper    => true
  | .paper,    .rock     => true
  | _,         _         => false

/--
勝ちの定義（仕様）：
手 `h` が場（`hands`）における勝ち手であるとは、
1. `h` 自身が場に出ている
2. 場に出ている手のうち、少なくとも1つに勝っている
3. 場に出ているどの手にも負けていない
-/
def isWinningHandSpec (hands : List Hand) (h : Hand) : Bool :=
  hands.contains h &&
  hands.any (fun other => h.beats other) &&
  hands.all (fun other => !other.beats h)

/-- 場に出た手の種類を1パスで集計するためのビットセット相当の構造体 -/
structure HandSet where
  rock     : Bool := false
  scissors : Bool := false
  paper    : Bool := false
  deriving Repr, DecidableEq

def HandSet.insert (h : Hand) (s : HandSet) : HandSet :=
  match h with
  | .rock     => { s with rock := true }
  | .scissors => { s with scissors := true }
  | .paper    => { s with paper := true }

def HandSet.ofList (hands : List Hand) : HandSet :=
  hands.foldr HandSet.insert {}

def HandSet.contains (s : HandSet) : Hand → Bool
  | .rock     => s.rock
  | .scissors => s.scissors
  | .paper    => s.paper

def HandSet.any (s : HandSet) (p : Hand → Bool) : Bool :=
  (s.rock && p .rock) || (s.scissors && p .scissors) || (s.paper && p .paper)

def HandSet.all (s : HandSet) (p : Hand → Bool) : Bool :=
  (!s.rock || p .rock) && (!s.scissors || p .scissors) && (!s.paper || p .paper)

def HandSet.isWinningHandSpec (s : HandSet) (h : Hand) : Bool :=
  s.contains h &&
  s.any (fun other => h.beats other) &&
  s.all (fun other => !other.beats h)

def HandSet.winningHand? (s : HandSet) : Option Hand :=
  match s.rock, s.scissors, s.paper with
  | true,  true,  false => some .rock
  | false, true,  true  => some .scissors
  | true,  false, true  => some .paper
  | _,     _,     _     => none

def winningHand? (hands : List Hand) : Option Hand :=
  (HandSet.ofList hands).winningHand?

theorem HandSet.contains_ofList (hands : List Hand) (h : Hand) :
    (HandSet.ofList hands).contains h = hands.contains h := by
  induction hands with
  | nil =>
    cases h <;> rfl
  | cons head tail ih =>
    simp only [HandSet.ofList, List.foldr_cons, List.contains_cons] at *
    rw [← ih]
    rcases List.foldr HandSet.insert {} tail with ⟨r, sc, pa⟩
    cases head <;> cases h <;> cases r <;> cases sc <;> cases pa <;> rfl

theorem HandSet.any_ofList (hands : List Hand) (p : Hand → Bool) :
    (HandSet.ofList hands).any p = hands.any p := by
  induction hands with
  | nil => rfl
  | cons head tail ih =>
    simp only [HandSet.ofList, List.foldr_cons, List.any_cons] at *
    rw [← ih]
    rcases List.foldr HandSet.insert {} tail with ⟨r, sc, pa⟩
    dsimp [HandSet.insert, HandSet.any]
    cases head <;>
      cases p .rock <;> cases p .scissors <;> cases p .paper <;>
      cases r <;> cases sc <;> cases pa <;> rfl

theorem HandSet.all_ofList (hands : List Hand) (p : Hand → Bool) :
    (HandSet.ofList hands).all p = hands.all p := by
  induction hands with
  | nil => rfl
  | cons head tail ih =>
    simp only [HandSet.ofList, List.foldr_cons, List.all_cons] at *
    rw [← ih]
    rcases List.foldr HandSet.insert {} tail with ⟨r, sc, pa⟩
    dsimp [HandSet.insert, HandSet.all]
    cases head <;>
      cases p .rock <;> cases p .scissors <;> cases p .paper <;>
      cases r <;> cases sc <;> cases pa <;> rfl

theorem isWinningHandSpec_eq_ofList (hands : List Hand) (h : Hand) :
    isWinningHandSpec hands h = (HandSet.ofList hands).isWinningHandSpec h := by
  simp [isWinningHandSpec, HandSet.isWinningHandSpec,
    HandSet.contains_ofList, HandSet.any_ofList, HandSet.all_ofList]

/--
何人でじゃんけんしても、手`h`が
HandSetを利用した（効率的な）実装で勝利と返すことと、
仕様（を愚直に実装したら全探索を要する）によって勝利と判定されることは同値
-/
theorem winningHand?_eq_some_iff (hands : List Hand) (h : Hand) :
    winningHand? hands = some h ↔ isWinningHandSpec hands h = true := by
  rw [winningHand?, isWinningHandSpec_eq_ofList]
  rcases HandSet.ofList hands with ⟨r, sc, pa⟩
  cases h <;> cases r <;> cases sc <;> cases pa <;> decide

/--
勝者の単一性
Xを出した人とYを出した人が両方勝者ならばX=Y
-/
theorem winning_hand_unique (hands : List Hand) (h₁ h₂ : Hand)
    (hw₁ : isWinningHandSpec hands h₁ = true)
    (hw₂ : isWinningHandSpec hands h₂ = true) : h₁ = h₂ := by
  rw [← winningHand?_eq_some_iff] at hw₁ hw₂
  rw [hw₁] at hw₂
  injection hw₂

/--
全員同じ手なら必ずあいこ
-/
theorem replicate_is_draw (n : Nat) (h : Hand) :
    winningHand? (List.replicate n h) = none := by
  have h_set : HandSet.ofList (List.replicate n h) =
      if n = 0 then {} else HandSet.insert h {} := by
    induction n with
    | zero => rfl
    | succ m ih =>
      simp only [HandSet.ofList, List.replicate_succ, List.foldr_cons] at *
      rw [ih]
      cases m <;> cases h <;> rfl
  rw [winningHand?, h_set]
  cases n <;> cases h <;> rfl

/--
場に3種類すべてが出ていれば必ずあいこ
-/
theorem three_way_tie (hands : List Hand)
    (h_rock : hands.contains .rock = true)
    (h_scissors : hands.contains .scissors = true)
    (h_paper : hands.contains .paper = true) :
    winningHand? hands = none := by
  rw [← HandSet.contains_ofList] at h_rock h_scissors h_paper
  simp only [HandSet.contains] at h_rock h_scissors h_paper
  simp [winningHand?, HandSet.winningHand?, h_rock, h_scissors, h_paper]

/--
順列不変性・公平性
参加者の並び順をどのように入れ替えても判定結果は変わらない
-/
theorem winningHand?_perm_invariant {hands₁ hands₂ : List Hand}
    (hp : hands₁.Perm hands₂) :
    winningHand? hands₁ = winningHand? hands₂ := by
  have h_eq : HandSet.ofList hands₁ = HandSet.ofList hands₂ := by
    induction hp with
    | nil => rfl
    | cons x _ ih =>
      simp only [HandSet.ofList, List.foldr_cons] at *
      rw [ih]
    | swap x y l =>
      simp only [HandSet.ofList, List.foldr_cons]
      rcases List.foldr HandSet.insert {} l with ⟨r, sc, pa⟩
      cases x <;> cases y <;> cases r <;> cases sc <;> cases pa <;> rfl
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  simp [winningHand?, h_eq]

end MultiJanken

/-
N人じゃんけんにおいて`List Hand`は無限通りで全探索はできないため、
2^3 = 8状態の `HandSet` に還元（商集合化）し、還元後の有限状態空間（`HandSet` と `Hand`）を `cases` で総当たりする検証している。

この仕様（`isWinningHandSpec`）から実装（`winningHand?`）への変形の同値性をLeanでは明示的な定理として機械検証できる。ただし今回これは人間にとっても直感的に認められることである：

「場に出たのが3種類か1種類ならあいこ、2種類の時だけどちらが勝利か判定すれば済むからSetを使おう」
と、普通のプログラミング（ref: ./MultiJanken.ts）ではその同値性を暗黙の了解として短く実装し、テストもほぼ不要とされるだろう。今回の問題をLeanで取り組むのはオーバーエンジニアリングだったが、直感に思えた同値性を信じ込む恐ろしさ・本当に証明しようと思ったらこうやってできるという凄さを実感できた。

直感では通用しない領域でLeanを活用する例は別の機会に譲る。
-/

open MultiJanken in
def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.println "使い方: lake exe multi-janken <n> <hand1> <hand2> ... (rock|scissors|paper)"
    return 1
  | nStr :: handStrs =>
    let some n := nStr.toNat?
      | IO.println s!"エラー: '{nStr}' は有効な自然数ではありません。"
        return 1
    if handStrs.length != n then
      IO.println s!"エラー: 指定された人数 ({n}) と手の数 ({handStrs.length}) が一致しません。"
      return 1
    let some hands := handStrs.mapM Hand.ofString?
      | IO.println "エラー: 手には rock, scissors, paper のいずれかを指定してください。"
        return 1
    match winningHand? hands with
    | some winner =>
      IO.println s!"勝ち手: {winner}"
      return 0
    | none =>
      IO.println "あいこ！"
      return 0

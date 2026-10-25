abbrev Hand := Fin 3 -- 値とそれが{0,1,2}である証明`isLt`

def handToString : Hand → String
  | ⟨0, _⟩ => "グー"
  | ⟨1, _⟩ => "チョキ"
  | ⟨2, _⟩ => "パー"

def stringToHand? : String → Option Hand
  | "グー"   | "rock"     => some 0
  | "チョキ" | "scissors" => some 1
  | "パー"   | "paper"    => some 2
  | _                     => none

inductive Result where
  | win
  | lose
  | draw
  deriving Repr, DecidableEq

def Result.invert : Result → Result
  | .win  => .lose
  | .lose => .win
  | .draw => .draw

def Result.toMessage : Result → String
  | .win  => "あなたの勝ち！🎉"
  | .lose => "あなたの負け...😭"
  | .draw => "あいこ！"

def judge (player cpu : Hand) : Result :=
  if player == cpu then .draw
  else if (player == 0 && cpu == 1) || (player == 1 && cpu == 2) || (player == 2 && cpu == 0) then
    .win
  else
    .lose

theorem judge_same_hand_is_draw (h : Hand) : judge h h = .draw := by
  simp [judge]

-- ゼロサム性
theorem judge_symm_invert (player cpu : Hand) : judge player cpu = (judge cpu player).invert := by
  revert player cpu
  decide

-- 必勝手は存在しない
theorem no_dominant_hand (player : Hand) :
    (∃ cpu, judge player cpu = .win) ∧ (∃ cpu, judge player cpu = .lose) := by
  revert player
  decide

/-

これらの定理の証明はDecidableで普通のユニットテストで全探索（3^2パターン）やってるのと同じ。

勝ちパターン3通りをベタ書きしたハードコードになっているため、背後の代数的な法則が存在しない。
そのため、decide を使わずに手動で証明をやるにしても結局全探索を書くしかない。

1対1のじゃんけんをLeanでやる優位性は見出しにくい。
-/


def main (args : List String) : IO UInt32 := do
  if h : args = [] then
    IO.println "使い方: lake exe janken [グー|チョキ|パー]"
    return 1
  else
    -- `h` の型が自動的に `args ≠ []`（空でない証明）になる
    let playerStr := args.head h

    match stringToHand? playerStr with
    | none =>
      IO.println s!"エラー: '{playerStr}' は無効な手です。"
      return 1
    | some player =>
      let cpuNat ← IO.rand 0 2
      -- ただの Nat
      if h_lt : cpuNat < 3 then
        let cpu : Hand := ⟨cpuNat, h_lt⟩
        -- こうやってチェックしないとHandは作れない
        IO.println s!"あなた: {handToString player}\n相手: {handToString cpu}\n---\n{(judge player cpu).toMessage}"
        return 0
      else
        return 1

/-
ランダム性について

https://github.com/leanprover/lean4/blob/3bb14931395f6d77f634169e68ebcb3d8dd379ff/src/Init/Data/Random.lean#L124-L126

ユーザーがIO.setRandSeedとかを明示しない場合、シードはデフォルトで
UInt64.toNat (ByteArray.toUInt64LE! (← IO.getRandomBytes 8))
であり、
[IO.getRandomBytes](https://lean-lang.org/doc/reference/latest/IO/Random-Numbers/#IO___getRandomBytes)
はシステムのエントロピーソースを使うので、ほぼほぼ非決定的になる
-/

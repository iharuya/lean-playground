def handToString (h : Nat) : String :=
  if h == 0 then "グー"
  else if h == 1 then "チョキ"
  else "パー"

-- optionalな関数の名前に?をつけるのは慣習
def stringToHand? (s : String) : Option Nat :=
  match s with
  | "グー" => some 0
  | "rock" => some 0
  | "チョキ" => some 1
  | "scissors" => some 1
  | "パー" => some 2
  | "paper" => some 2
  | _ => none

-- 0=グー, 1=チョキ, 2=パー
-- 勝ち: (0, 1), (1, 2), (2, 0)
def judge (player cpu : Nat) : String :=
  if player == cpu then
    "あいこ！"
  else if (player == 0 && cpu == 1) || (player == 1 && cpu == 2) || (player == 2 && cpu == 0) then
    "あなたの勝ち！🎉"
  else
    "あなたの負け...😭"

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.println "使い方: lake exe mycli [グー|チョキ|パー]"
    return 1

  let playerStr := args.head! -- Emptyチェックをしたので絶対にある。これでなかったらpanicしていいという意味で!
  match stringToHand? playerStr with
  | none =>
    IO.println s!"エラー: '{playerStr}' は無効な手です。「グー」「チョキ」「パー」のいずれかを入力してください。"
    return 1
  | some player =>
    let cpu ← IO.rand 0 2

    IO.println s!"あなた: {handToString player}"
    IO.println s!"相手: {handToString cpu}"
    IO.println "---"
    IO.println (judge player cpu)

    return 0

/-
ランダム性について

https://github.com/leanprover/lean4/blob/3bb14931395f6d77f634169e68ebcb3d8dd379ff/src/Init/Data/Random.lean#L124-L126

ユーザーがIO.setRandSeedとかを明示しない場合、シードはデフォルトで
UInt64.toNat (ByteArray.toUInt64LE! (← IO.getRandomBytes 8))
であり、
[IO.getRandomBytes](https://lean-lang.org/doc/reference/latest/IO/Random-Numbers/#IO___getRandomBytes)
はシステムのエントロピーソースを使うので、ほぼほぼ非決定的になる

-/

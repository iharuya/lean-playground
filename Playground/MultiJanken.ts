export type Hand = "rock" | "scissors" | "paper";

const VALID_HANDS = new Set<string>(["rock", "scissors", "paper"]);

export function isHand(value: string): value is Hand {
  return VALID_HANDS.has(value);
}

export function winningHand(hands: readonly Hand[]): Hand | null {
  const uniqueHands = new Set(hands);
  if (uniqueHands.size !== 2) {
    return null;
  }
  if (!uniqueHands.has("paper")) return "rock";
  if (!uniqueHands.has("rock")) return "scissors";
  return "paper";
}

function main(args: readonly string[]): number {
  const [nStr, ...handStrs] = args;
  if (nStr === undefined) {
    console.error("使い方: node Playground/MultiJanken.ts <n> <hand1> <hand2> ... (rock|scissors|paper)");
    return 1;
  }

  const n = Number(nStr);
  if (!Number.isInteger(n) || n < 0) {
    console.error(`エラー: '${nStr}' は有効な自然数ではありません。`);
    return 1;
  }

  if (handStrs.length !== n) {
    console.error(`エラー: 指定された人数 (${n}) と手の数 (${handStrs.length}) が一致しません。`);
    return 1;
  }

  if (!handStrs.every(isHand)) {
    console.error("エラー: 手には rock, scissors, paper のいずれかを指定してください。");
    return 1;
  }

  const winner = winningHand(handStrs);
  console.log(winner !== null ? `勝ち手: ${winner}` : "あいこ！");
  return 0;
}

if (import.meta.main) {
  process.exitCode = main(process.argv.slice(2));
}

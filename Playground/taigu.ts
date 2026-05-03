function prove_taigu_1<A, B>(apple: (a: A) => B) {
    return function (banana: (b: B) => never) {
        return function (coffee: A): never {
            //「型：命題、関数：ならば（論理包含）」として読み替える
            // 仮定: $A \to B$（apple）と $B \to False$（banana）が正しい
            // 目標: $A \to False$（coffee を受け取ったら矛盾を返す関数）となることを示す
            // この「仮定 $\to$ 目標」は対偶の片側の主張そのものであることが分かる

            const resultB = apple(coffee); // Aについて、仮定より$A \to B$であり、Typescriptもそのように推論した
            const resultNever = banana(resultB); // Bについて、仮定より$B \to False$であり、Typescriptもそのように推論した
            return resultNever // 初めと最後を見ると、$A \to False$になっている。よって目標達成
        };
    };
}
// これは以下と全く同じ
type Taigu = <A, B>(apple: (a: A) => B) => (banana: (b: B) => never) => (coffee: A) => never;
const prove_taigu_2: Taigu = (apple) => (banana) => (coffee) => {
  return banana(apple(coffee));
};

// 関数が「(引数を受け取って)値を返す」ことを主作用というなら、それ以外の作用を副作用という。
// 関数の外にある変数を変えることや、関数が実行されるICの外部の世界に対するあらゆる変化・影響が副作用に相当する
// また、「実行の強制終了」も主作用でないから副作用
const side_effect = () => {
    throw new Error("never召喚!")
}
const prove_taigu_3: Taigu = (apple) => (banana) => (coffee) => {
    const _dummy = apple(coffee)
    return side_effect()
    // 副作用がたまたまneverを返したからTypescriptのLSPはエラーを出さない
    // けど副作用を含むプログラムは証明として対応付けられないらしい
    // カルテシアン閉圏？ちょっとよく分からないな
}


// あまり関係ないけど、いろんな型の階層関係の復習
type Relation<A, B> = [A] extends [B] ? [B] extends [A] ? "identical" : "A <: B" : "A :> B"
type VoidIsSuperOfUndefined = Relation<void, undefined>
type UndefinedSuperOfNever = Relation<undefined, never>
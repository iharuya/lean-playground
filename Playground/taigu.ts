// Leanで証明を書いた後、TSでもできないか試す場所
// まずは、いろんな型の階層関係の復習
type Relation<A, B> = [A] extends [B] ? [B] extends [A] ? "identical" : "A <: B" : "A :> B"
type VoidIsSuperOfUndefined = Relation<void, undefined>
type UndefinedSuperOfNever = Relation<undefined, never>

// まずは(A → B) → (¬B → ¬A)の証明
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
    // けど副作用を含むプログラムは証明として対応付けられない
    // それをきちっと言うには、カルテシアン閉圏とやらを理解する必要があるみたい
}


// 次に[Leanでやった対偶の逆の証明](./taigu.lean)がTSでもできないか考える。
type Not<T> = (t: T) => never
type Or<L, R> = { _tag: "Left", value: L } | { _tag: "Right", value: R }
type ExcludedMiddle = <X>() => Or<X, Not<X>>
// 対偶の逆の証明ではこの排中律が必要だったから、これを満たす純粋な関数を先に示しておきたい...
// @ts-ignore
const _excluded_middle: ExcludedMiddle = () => {
    // 引数ないからなんも返せない. グローバル変数を使ったら副作用になる
    // これを構成論理のみでは証明不可能と言う
}
/**
Leanでも同様の問題に直面する。そこでLeanでは3つの公理を使ってemを証明していたが、同じことはTypescriptでは絶対できないらしい。AI曰く、

---
## 依存型の不在

Diaconescuの定理で出てくる集合 $U$： $\{x \in \{0, 1\} \mid x = 0 \lor P \}$を型として表現するには、型の中に命題Pや数字01を埋め込んだ型（依存型）を表現するプログラミング言語が必要になる。
しかしTSでの型はプロパティの形しか表現できないので、「$x$ の値が $0$ であるか、または命題 $P$ が真であるような $x$ の集まり」という論理的な制約を型として表現し、コンパイラに計算させる能力がない。

## 等価性という型の不在

Leanの外延性公理 `{a b : Prop} : (a ↔ b) → a = b`に出てくる`a = b`は、aとbが等しいという証拠の型（Eq a b）。
だけどTSでの`a === b`で推論されるboolean型には、「等しいことの証拠」を型として持ち運び、別の関数の引数として渡す（それによって型チェックを通す）という概念が存在しない。だから`propext` をdeclareしても、それをTSの制御フローの中で活用することができない。

## 商型の不在

`Quot.sound` が提供する商型とは、「ある同値関係を満たすものは、プログラム上で同一視する新しい型を作る」という機能。
TSで言えば、「{ id: 1, name: "A" } と { id: 1, name: "B" } は id が同じという関係があるから、コンパイラレベルで全く同じモノとして扱え」と強制するようなものだけど、構造的型付けを選択している以上、構造の異なる型を同じモノとして扱うことは不可能。

---
とのこと。分かったような分からないような...（分かってない）
ともかくTSでは無理らしいので、排中律を公理とした上で対偶の逆の証明ができるか試してみる
*/
declare const excluded_middle: ExcludedMiddle;
type FalseElimination = <T>(f: never) => T
const false_elimination: FalseElimination = (f) => f // 爆発律は意味はよく分かってないけど証明できちゃった！

// type TaiguGyaku = <A, B>(h1: (nb: Not<B>) => Not<A>) => (ha: A) => B;
// このように型宣言を先にやってから実装を与えると見通しが立ちやすいけど、今回はジェネリクスBを実装側に持たせないと排中律が使えなかった。
const taigu_gyaku = <A, B>(h1: (nb: Not<B>) => Not<A>) => (ha: A): B => {
    const b_or_not_b = excluded_middle<B>()
    switch (b_or_not_b._tag) {
        case "Left": {
            const hb = b_or_not_b.value;
            return hb;
        }
        case "Right": {
            const hnb = b_or_not_b.value;
            const hna = h1(hnb);
            const hfalse = hna(ha);
            return false_elimination(hfalse);
        }
    }
}

# tiny-metaf

Code-golfing Brown & Palsberg's typed meta-circular self-interpreter for System Fω.

The core is pure Fω: lambdas, type lambdas, type operators, and type-level application. The host language adds `Int`, `Bool`, `if`, `let`, and arithmetic for writing examples. These keep the language strongly normalizing, but only the pure fragment can be quoted.

The idea comes from Brown & Palsberg, [_Breaking Through the Normalization Barrier: A Self-Interpreter for F-omega_](http://compilers.cs.ucla.edu/popl16/popl16-full.pdf). It matters historically because it was widely believed that a strongly-normalizing language could not have a total self-interpreter, since a total universal function lets you build a diagonalizer. The paper's typed HOAS quotation avoids that diagonal gadget, so `unquote : forall a. Exp a -> Op Id a` exists, type-checks, and reduces `unquote [t] [e]` to `e`. There is deliberately no `fix`: general recursion would break strong normalization, and with it the whole point.

The shallow encoding from Section 3 of the paper works in plain System F and is in [`shallow.f`](examples/shallow.f). The deep encoding (Figure 3, Sections 4 to 7) needs Fω's type operators. [`deep.f`](examples/deep.f) implements it with `unquote`, `size`, `isAbs`, `isNF`, and `cps` as folds over the same represented terms. [`quote.rs`](src/quote.rs) is the quoter, available in the REPL as `:quote`. [`tests/quoter.rs`](tests/quoter.rs) checks that its output is β-normal and checks Theorem 7.4 (`unquote τ ⌜e⌝ →* e`, up to type equivalence) against a full β-normalizer.

```sh
cargo build --release
cargo run -- run examples/shallow.f
cargo run -- run examples/deep.f
cargo run -- repl
```

```
fself> (/\a. \(x:a). x) [Int] 42
fself> :t /\a. \(x:a). x
fself> :quote /\a. \(x:a). x
fself> :l examples/shallow.f
fself> :l examples/deep.f
fself> :q
```

- [`basics.f`](examples/basics.f) polymorphic identity, const, compose
- [`church.f`](examples/church.f) Church-encoded naturals
- [`self.f`](examples/self.f) Church-encoded AST with three interpretations (tagless final)
- [`shallow.f`](examples/shallow.f) the Brown-Palsberg shallow self-interpreter
- [`deep.f`](examples/deep.f) the full Brown-Palsberg deep self-interpreter

## License

This project is licensed under the MIT License. See the [LICENSE](LICENSE) file for details.

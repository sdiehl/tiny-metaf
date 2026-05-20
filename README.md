# tiny-fself

System F-omega with a typed self-interpreter. Polymorphic lambda calculus (`\x:T.e`, `e e`, `/\a.e`, `e [T]`, `forall a. T`) plus kinds (`*`, `* -> *`), type-level lambdas (`lam (a : *). T`), type-level application (`F T`), `fix` for recursion, and Church-encoded ADTs.

The core example is the shallow self-interpreter from Brown & Palsberg, [_Breaking Through the Normalization Barrier: A Self-Interpreter for F-omega_](http://compilers.cs.ucla.edu/popl16/popl16-full.pdf) (POPL 2016). It's cool because folklore said a total self-interpreter for a strongly-normalizing language was impossible (a total universal function lets you build a diagonalizer), but the paper's HOAS-style typed quotation avoids that diagonal gadget so `unquote : forall a. (Iota -> a) -> a` exists, type-checks, and reduces `unquote [t] [e]` to `e`.

The shallow encoding from Section 3 works in plain System F and is in [`shallow.f`](examples/shallow.f). The deep encoding from Section 5 needs F-omega's type operators; [`deep.f`](examples/deep.f) demonstrates the F-omega ingredients (kinds, type-level lambdas, types polymorphic in a type constructor) that Section 5 builds on.

```sh
cargo build --release
cargo run -- run examples/shallow.f
cargo run -- repl
```

```
fself> let id : forall a. a -> a = /\a. \(x:a). x;
fself> id [Int] 42
fself> :t /\a. \(x:a). x
fself> :l examples/shallow.f
fself> :q
```

- [`basics.f`](examples/basics.f) polymorphic identity, const, compose
- [`church.f`](examples/church.f) Church-encoded naturals
- [`fix.f`](examples/fix.f) factorial and fibonacci via `fix`
- [`self.f`](examples/self.f) Church-encoded AST with three interpretations (tagless final)
- [`shallow.f`](examples/shallow.f) the Brown-Palsberg shallow self-interpreter
- [`deep.f`](examples/deep.f) F-omega type operators and the deep representation skeleton

## License

This project is licensed under the MIT License. See the [LICENSE](LICENSE) file for details.

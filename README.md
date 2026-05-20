# tiny-fself

System F with a typed self-interpreter. Polymorphic lambda calculus (`\x:T.e`, `e e`, `/\a.e`, `e [T]`, `forall a. T`) plus `fix` for recursion, Church-encoded ADTs, and a tagless final interpreter as the headline example.

## Build

```sh
cargo build --release
```

## REPL

```sh
cargo run -- repl
```

```
fself> let id : forall a. a -> a = /\a. \(x:a). x;
fself> id [Int] 42
fself> :t /\a. \(x:a). x
fself> :l examples/self.f
fself> :q
```

## Run a file

```sh
cargo run -- run examples/self.f
```

## Examples

- `examples/basics.f` polymorphic identity, const, compose
- `examples/church.f` Church-encoded naturals
- `examples/fix.f` factorial and fibonacci via `fix`
- `examples/self.f` Church-encoded AST with three interpretations

## License

MIT

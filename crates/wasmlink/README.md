<div align="center">
  <h1><code>wasmlink</code></h1>

  <p>
    <strong>A WebAssembly module linker that uses the module linking proposal.</strong>
  </p>

  <strong>A <a href="https://bytecodealliance.org/">Bytecode Alliance</a> project</strong>

  <p>
    <a href="https://github.com/bytecodealliance/wit-bindgen/actions?query=workflow%3ACI"><img src="https://github.com/bytecodealliance/wit-bindgen/workflows/CI/badge.svg" alt="build status" /></a>
    <img src="https://img.shields.io/badge/rustc-stable+-green.svg" alt="supported rustc stable" />
  </p>
</div>

# Wasmlink

_Please note: this is currently an experimental project._

`wasmlink` is a prototype [WebAssembly](https://webassembly.org/) module linker that can link together a module and its dependencies using [module linking](https://github.com/WebAssembly/module-linking) and the [Canonical Interface Types ABI](https://github.com/WebAssembly/interface-types/pull/132).

When used in combination with [wit-bindgen](https://github.com/bytecodealliance/wit-bindgen), it is capable of generating interface adapter functions in WebAssembly that enables WebAssembly modules to exchange interface types such as strings, records, lists, and variants.

## Building

To build `wasmlink`:

```text
$ cargo build -p wasmlink-cli
```

## Running

To run `wasmlink`:

```text
$ cargo run -p wasmlink-cli
```

## Testing

To run tests, first install the `wasm32-wasi` target:

```text
$ rustup target install wasm32-wasi
```

With the target installed, run the tests:

```text
$ cargo test --all
```

## Demo

### Prerequisites

The demo requires [cargo-wasi](https://github.com/bytecodealliance/cargo-wasi), so install it using `cargo`:

```text
$ cargo install cargo-wasi
```

### Building the `markdown` module

The `markdown` module exposes an interface consisting of a `render` function that takes a string (the [Markdown](https://en.wikipedia.org/wiki/Markdown)) as an argument and returns a string (the rendered HTML).

The interface for the `markdown` module is:

```wit
render: function(markdown: string) -> string
```

To build the `markdown` module:

```text
$ cargo wasi build --manifest-path demo/markdown/Cargo.toml
```

### Building the `renderer` module

The `renderer` module will read input via `stdin`, pass the input as a string to the `render` function from the `markdown` module, and then print the returned HTML to `stdout`.

To build the `renderer` module:

```text
$ cargo wasi build --manifest-path demo/renderer/Cargo.toml
```

### Linking the two modules together

With the two modules now built, it is time to link them together so that they can be run directly with [Wasmtime](https://github.com/bytecodealliance/wasmtime):

```text
$ cargo run --release -p wasmlink-cli -- -m markdown=demo/markdown/target/wasm32-wasi/debug/markdown.wasm -i markdown=demo/markdown/markdown.wit -p wasmtime -o linked.wasm demo/renderer/target/wasm32-wasi/debug/renderer.wasm
```

This command produces a linked module named `linked.wasm` in the current directory.

### Running the linked module

As the linked module uses features from both the [module linking](https://github.com/WebAssembly/module-linking) and [multi-memory](https://github.com/WebAssembly/multi-memory) WebAssembly proposals, support has to be explicitly enabled in Wasmtime to enable the module to run.

To run the linked module:

```text
$ printf '# Hello\nworld' | wasmtime --wasm-features=module-linking,multi-memory linked.wasm
```

If everything worked correctly, this should render the Markdown echoed on the command line:

```markdown
# Hello
world
```

as the following HTML:

```html
<h1>Hello</h1>
<p>world</p>
```

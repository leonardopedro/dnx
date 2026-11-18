# dnx-verify

Check a Nix → AustralVM translation by reducing both sides to DeltaNets and
comparing their canonical identities.

```bash
dnx-verify check --nix '2 + 3' --austral '(2 + 3)'
# nix       fadee973...3804  agents=1  value=5
# austral   fadee973...3804  agents=1  value=5
# verdict   equivalent (canonical nets identical; witness covers 1 node(s))

dnx-verify check --nix '2 + 3' --austral '(2 + 4)'
# verdict   NOT equivalent (canonical nets differ)   # exit 1

# A real catch: the AustralVM arithmetic parser does not apply * before +,
# so this translation silently computes 9 instead of Nix's 7.
dnx-verify check --nix '1 + 2 * 3' --austral '(1 + 2 * 3)'
# nix       ...  value=7
# austral   ...  value=9
# verdict   NOT equivalent

dnx-verify nix-hash --expr '1 + 2'
dnx-verify austral-hash --expr '(1 + 2)'
dnx-verify check --nix-file default.nix --austral-file Main.aum --json
dnx-verify austral-check --reference Ref.aum --austral-file Main.aum
```

| flag | meaning |
|---|---|
| `--nix EXPR` / `--nix-file PATH` | the Nix expression |
| `--austral SRC` / `--austral-file PATH` | the AustralVM source fragment (`let … return e;`, a bare expression, a function declaration, or `module body … end module body.`) |
| `--reference` / `--reference-file` | the known-good AustralVM module for `austral-check` |
| `--expr`, `--file` | the single input for `nix-hash` / `austral-hash` |
| `--json` | machine-readable result |
| `--dump` | print the reduced kernel net (debugging) |

Exit status: `0` equivalent, `1` not equivalent, `2` could not compare
(parse/normalization failure, or an unsupported fragment).

## Batch mode

`check --manifest FILE` checks every pair in a JSON manifest and reports each
verdict without stopping at the first failure:

```json
{
  "pairs": [
    { "name": "arith", "nix": "arith.nix", "austral": "arith.aum" },
    { "nix": "bool.nix", "austral": "bool.aum" },
    { "name": "precedence", "nix": "precedence.nix", "austral": "precedence.aum", "expect": "different" }
  ]
}
```

A bare JSON array is also accepted. Paths resolve relative to the manifest's
directory; `name` is optional and defaults to the Nix file's stem. `expect` is
optional and declares the verdict the pair *must* have: `"equivalent"` (also
the rule when the field is absent) or `"different"`.

```
$ just verify-examples
[ok]     arith                    equivalent  4214d7f6...fdd8  witness=1
[ok]     apply                    equivalent  2eb771db...d0b4  witness=1
[ok]     bool                     equivalent  25dfd29c...412a  witness=1
[ok]     float                    equivalent  c874bca8...6b56  witness=1
[ok]     precedence               different   nix=bf20e9c9...7cb2 austral=7fbc9534...67cc  (expected)
5 pair(s): 4 equivalent, 1 different, 0 error(s); expectations met
```

The precedence pair is a deliberately wrong translation. Nix binds `*` before
`+`, so `1 + 2 * 3` is 7, while the AustralVM expression parser groups left to
right and reads the same text as `(1 + 2) * 3` — 9. The tool still reports the
mismatch (`--json` carries both values); what `"expect": "different"` changes
is that the batch treats it as the required outcome instead of a failure. A
mismatch with no `expect`, or an `"expect": "equivalent"` that differs, or an
`"expect": "different"` that matches, is reported `[fail] … (expected …)` and
makes the batch exit `1`. An unrecognised `expect` value is a manifest error
(exit `2`).

`--json` emits one object with a `pairs` array and a `summary`; each pair
carries `passed` and, when declared, `expected`. Batch exit status aggregates:
`2` if any pair could not be compared, else `1` if any pair misses its expected
verdict, else `0`. Unreadable or malformed manifests are exit `2` before any
pair is checked. The committed example manifest is
`crates/dnx-verify/examples/pairs.json`, run by `just verify-examples`;
`just verify-examples path/to/pairs.json` checks another manifest (the path is
positional; `MANIFEST=…` would be read by `just` as a variable override).

## Generating a starter manifest

`scan` turns a folder of translation outputs into a manifest: it walks `DIR`
recursively, pairs `X.nix` with `X.aum` at the same path stem, and writes
`DIR/pairs.json` (paths relative to that file).

```bash
$ dnx-verify scan --dir translations
wrote 2 pair(s) to translations/pairs.json
$ cat translations/pairs.json
{
  "pairs": [
    { "name": "arith", "nix": "arith.nix", "austral": "arith.aum" },
    { "name": "sub/bool", "nix": "sub/bool.nix", "austral": "sub/bool.aum" }
  ]
}
```

Files without a counterpart are reported on stderr (`unpaired …`) but do not
stop the scan; two Nix entry points for one module stay unpaired rather than one
being guessed. A folder with no pairs at all is exit `2` and writes nothing.
`--output PATH` writes elsewhere (paths become relative to the manifest's new
directory), and `--output -` prints the manifest to stdout with paths relative
to the working directory. Regeneration carries over the `expect` declarations
recorded under the same pair names in the file it replaces, so scanning a
folder again does not silently downgrade a known-bad translation to a required
pass; an unreadable previous manifest contributes nothing.

The result is directly usable with `check --manifest`, so
`dnx-verify scan --dir out && just verify-examples out/pairs.json` is the whole
loop — or in one step:

```bash
$ just scan out                  # scan, then check every pair
$ just scan out no               # only write out/pairs.json
```

`just scan`'s arguments are positional; `just scan out CHECK=no` would be read
by `just` as a variable override, not as the recipe's second argument. The
committed examples are stem-paired, so `just scan crates/dnx-verify/examples`
regenerates the shipped manifest (keeping `precedence`'s expectation) and
checks all five pairs.

## Structural checks over entities

A module whose `main` reduces to a constructor or an unresolved name — e.g.
`return ExitSuccess();` — produces a net with `Entity` agents. Those names have
no Nix counterpart, so `check` cannot accept that side as a *value* comparison.
`austral-check` compares two AustralVM modules structurally instead: the known-
good reference against the translation under test.

```bash
$ dnx-verify austral-check --reference Ref.aum --austral-file Main.aum
reference  8220fa7a...266e  agents=1  value=-  entities=ExitSuccess
translated 8220fa7a...266e  agents=1  value=-  entities=ExitSuccess
verdict   equivalent (canonical nets identical; witness covers 1 node(s))
```

Entity names are part of the canonical serialization, so `ExitSuccess` and
`ExitFailure` are different terms and a renamed constructor is a genuine
mismatch, not an isomorphism. The `entities` list (also in `--json`) is the
opaque vocabulary each side still mentions, which makes a structural mismatch
readable: two modules can have the same agent count and still differ only in
one name. Exit status is the same `0/1/2`.

## How the comparison works

The two projects have **different canonical byte encodings**, so comparing
dnx's BLAKE3 digest with the kernel's SHA-256 digest directly is meaningless.
The tool instead:

1. reduces the Nix expression with dnx to `Net<Canonical, ΔK>`
   (`NixRuntime::eval_net`, full `normalize_demand`);
2. exports that net into the kernel's net type
   (`unfer/logos/src/deltanet/types.rs`) — the same `Net` the AustralVM plugin
   hashes;
3. reduces the AustralVM source with the kernel's own translator
   (`logos::translate::translate_austral_any`) and keeps its reduced net;
4. hashes **both** nets with the kernel's `unf_hash`
   (`unf.rs`: SHA-256 over a root-directed canonical serialization that
   assigns canonical indices and emits back-references, so allocation history
   and node numbering do not affect the digest);
5. when the digests are equal, asks the kernel for the isomorphism witness
   (`isomorphism_witness`) — the node permutation, not just equal bytes.

So "equal" means the two reduced nets are the same canonical graph, exactly the
notion `uk_austral_defeq` reports with `equivalent: true`. It is deliberately
**not** a value comparison: two nets that compute the same number through
different normal forms hash differently, as they do in the kernel.

## Conversion details

| dnx | kernel |
|---|---|
| `FAN_ABS` (`aux0`=body, `aux1`=var) | `Abs` (slot 1=var, slot 2=body) |
| `FAN_APP` (`principal`=fn, `aux0`=result, `aux1`=arg) | `App` (slot 1=arg, slot 2=result) |
| `REP_IN` (level in `data`) | `Dup(level)` |
| `PortId::ERA` sentinel | one `Era` node per erased wire |
| `PRIM_VAL` `Int`/`Float`/`Bool` + `PrimState` | `Lit(Int64/F64/Bool)` |
| root free slot | `net.root` (the slot is elided) |

## Supported fragment (and how failures are reported)

The Nix net must be closed and built from the constructs above after full
normalization. Everything else is refused as `Unsupported` — never compared
approximatively, because a guessed encoding would produce a false verdict:

- **open terms** (a live free-variable slot other than the named root) — the
  kernel's `Entity` naming does not align with dnx's numeric `var_id` (use
  `austral-check` for entity-bearing Austral nets);
- **strings, paths, null, lists, attribute sets, closures, opaque lambdas** —
  the kernel's `Literal` covers `Int64`, `F64`, `Bool` only;
- **rep-out copies and partially erased replicators** — `Dup` carries only a
  level, so direction/erasure state has no kernel spelling (this is the same
  information loss noted in `canonical_hash.rs`);
- **unreduced primitive functions** — a live `PrimFun` means the net is not a
  value in the kernel's numeric subset.

Function declarations on the AustralVM side translate to an *open* body (its
parameters/unknown names become entities), so a Nix lambda and an AustralVM
`function …` declaration are not comparable as nets. Compare closed
applications instead, e.g. Nix `(x: x + 1) 2` with AustralVM `(2 + 1)`, or
full modules whose `main` returns a closed value. For entity-bearing nets —
modules that return a constructor or call an unresolved function — use
`austral-check` against a reference module instead.

## What the AustralVM examples cover

The kernel translator accepts a small *syntactic* fragment: bare
arithmetic/comparison expressions, `let … return e;` statement lists,
`function … end;` declarations, and `module body Name is … end module body.`
with no pragmas, imports, records, unions or generics. Full `.aum` modules in
`australVM/examples/` are therefore outside the shared fragment — measuring all
392 `.aum` files in `australVM` and `unfer` found 5 that translate at all, and
those 5 reduce to the same open `ExitSuccess` entity, i.e. not a value a Nix
expression can match. They are comparable to each other, and `austral-check`
confirms all five hash to the same net (`8220fa7a…266e`, one entity node) —
which is also the caveat: structural equality alone cannot tell a faithful
translation from a module that returns the same trivial term, so an
`austral-check` pass means "same reduced structure", not "same program".
The committed examples use the fragment the tool actually compares; a
translation of a larger module must first be lowered to a closed value, or be
held to a reference module through `austral-check`.

## Wiring

`dnx-verify` depends on the kernel's `logos` crate by path
(`../../../unfer/logos`) so both nets are hashed in-process by the one
serializer. There is no FFI boundary and no second hash implementation. The
workspace needs `../unfer` checked out beside `../dnx`.

`.github/workflows/dnx-verify.yml` runs `cargo test -p dnx-verify` and
`just verify-examples` when the crate (or `dnx-core`/`dnx-lang`) changes,
checking out `unfer` as a sibling (`UNFER_TOKEN` if the repository is private,
otherwise the workflow token).

## Tests

```bash
cargo test -p dnx-verify
```

Covered: closed arithmetic equivalence, expression-vs-literal normal forms,
booleans, floats, a genuine mismatch, the committed precedence fixture staying
a mismatch (Nix 7 vs AustralVM 9), unsupported strings, module `main`
comparison, hash stability, manifest parsing/aggregation (including CLI exit
codes and expected verdicts: a declared mismatch passes, an unmet expectation
and an unknown `expect` both fail), entity-bearing structural checks (including
entity-name mismatches and the CLI's `entities=` output), folder scanning plus a
generated manifest that round-trips through batch mode, regeneration preserving
recorded expectations, and that the committed example manifest meets all five
of its expectations. The `Abs`/`App`/`Dup`/`Era` port mapping is
pinned against **hand-built kernel nets** for `x: y: x`, `f: x: f x` and
`x: x x`, so the converter is checked against the kernel's own encoding rather
than against a second call to itself.

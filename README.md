# ghc-typelits-proof-assist

## What is it?

`ghc-typelits-proof-assist` is a GHC typechecker plugin enabling the developer
to rely on an external proof assistant (e.g. Coq) to prove statements that are
either impossible or too difficult to prove in Haskell.

Examples of such statements are presented in `app/Main.hs`.

This plugin is in a prototyping stage, and we advise against using it in
production. Code may change unexpectedly, and many failure modes are not
addressed yet.

## How does it work?

The plugin works as an interface between GHC and a chosen external prover. The
only currently supported proof assistant is Coq.

For expressions on `Nat` that GHC can't handle, you can offload the burden of
proof to the prover. As an example, let's take the following code snippet:

```haskell
foo :: (KnownNat n, KnownNat m) => Proxy n -> Proxy m -> Proxy (n + m) -> Proxy (m + n)
foo = id
```

When encountering this snippet, GHC will tell the plugin that it needs a proof
for `n + m ~ m + n`, because it can't prove it by itself. The plugin will then
check the description file (a sort of database for the plugin) to see if the
expression is already present.

If the expression is not yet present, the plugin will populate the description
file with a new expression and an associated proof file that contains the
outline for the lemma corresponding to the expression.

If the expression is already present, the plugin will try and check the
associated proof file, returning evidence for the assertion if the proof is
valid. Otherwise, typechecking will fail.

In order not to run the proofs everytime you build your Haskell program, the
plugin uses an additional layer of (rather basic) bookkeeping, running the
proofs again only if they were modified since last run.

## Awesome, now I want to run it!

This project is managed using Nix (flakes) and Cabal. I guess that you can
run it without Nix but I didn't try it out. The plugin depends on GHC 9.8.2
and, because of changes in GHC's typechecker types, won't run with a version
older than 9.8.

To compile the example, run `nix shell` and then `cabal build`. It'll print
too much information, so consider redirecting the output to a file, e.g. `cabal
build > log`.

If ever you want to try the plugin outside the scope of this project, remember
to call it with the bookkeeping file as argument, e.g. `-fplugin=ProverPrototype
-fplugin-opt=ProverPrototype:description`.

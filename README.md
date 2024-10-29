# ghc-typelits-proof-assist

## What is it?

`ghc-typelits-proof-assist` is a GHC plugin enabling the developer to rely
on an external proof assistant (e.g. Coq) to prove statements that are either
impossible or too difficult to prove in Haskell.

Examples of such statements are presented in `app/Main.hs`.

This plugin is in a prototyping stage, and we advise against using it in
production. Code may change unexpectedly, and many failure modes are not
addressed yet.

## How does it work?

The plugin works as an interface between GHC and a chosen external prover. The
only currently supported proof assistant is Coq.

For expressions (on `Nat`, but scope might prove larger) that GHC can't prove by
itself, you can offload the burden of proof to the prover. As an example, let's
take the following code snippet:

```haskell
{-PrototypeProver test proof
  Require Import Coq.Arith.PeanoNat.
  intros.
  apply le_S in H.
  apply le_S_n.
  rewrite <- PeanoNat.Nat.add_0_l at 1.
  rewrite PeanoNat.Nat.add_comm.
  rewrite PeanoNat.Nat.add_succ_l.
  rewrite PeanoNat.Nat.add_comm.
  rewrite <- PeanoNat.Nat.add_succ_l.
  rewrite PeanoNat.Nat.add_comm.
  apply H.
  @-}
test :: forall (n :: Nat) (m :: Nat) . (m + 1 <= n) => Dict (m <= n)
test = unsafeCoerce ((0 :: Nat) <= 0)
```

`ghc-typelits-proof-assist` will create a temporary Coq file, with a lemma
whose signature correspond to Haskell's `test` function here, and the proof
being the Coq snippet in the comment above the function. It then runs `coqc`
on it to check the proof, and compilation should fail if the proof doesn't work.

The syntax for comments is to be documented further.

## Awesome, now I want to run it!

This project is managed using Nix (flakes) and Cabal. I guess that you can
run it without Nix but I didn't try it out. The plugin depends on GHC 9.8.2
and, because of changes in GHC's typechecker types, won't run with a version
older than 9.8.

It should be adapted to run on GHC 9.10 pretty soon.

To compile the example, run `nix shell` and then `cabal build`. It'll print
too much information, so consider redirecting the output to a file, e.g. `cabal
build > log`.

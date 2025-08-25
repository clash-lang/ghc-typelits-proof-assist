# ghc-typelits-proof-assist

## What is it?

`ghc-typelits-proof-assist` is a GHC plugin enabling the developer to rely
on an external proof assistant (e.g. Coq) to prove statements that are either
impossible or too difficult to prove with the existing constraint solver of GHC.

Some first introductory examples can be found in `examples/Intro.hs`. Building
them is disabled by default due to the additional dependencies on the supported
proof assistants. The `examples` flag needs to be enabled for building them, e.g.,

```
cabal build -f examples
```

_**Important:** The plugin still is in a prototyping stage. We are currently
collecting some first internal and external feedback, which might lead to future
changes in the way how the plugin works._

## How does it work?

The plugin works as an interface between GHC and a chosen external prover. The
currently supported proof assistants are [Agda](https://github.com/agda/agda),
[Rocq](https://rocq-prover.org) and [Lean](https://lean-lang.org).

### Teaching Haskell about proofs

Let's say you need type-level evidence that `n <= m` due to the GHC constraint
solver not being able to deduce this evidence on its own, e.g., it blocks you
with a compile time error message such as
```
Cannot satisfy: n <= m
```
GHC's complaint is reasonable, because `n <= m` does not hold in general. However,
let's assume that there is already some evidence that `n + 1 <= m`, given as
a type level constraint. Then this evidence is sufficient to also deduce `n <= m`.
Nevertheless, GHC cannot create the evidence for such a deduction on its own, as
it has no proof that `n + 1 <= m` implies `n <= m`. We need to provide GHC with
that proof and the corresponding evidence first.

Unfortunately, there is no builtin mechanism to introduce such a proof in GHC,
which is where this plugin comes into play. We start with the introduction of
the statement to be proven, by utilizing the `class` and `instance` system
Haskell already has in place.

First, we define a new class `Lemma`, naming the proof, which declares the
proof goal and is parameterized in the type variables `n` and `m`.

```haskell
class
  ( n <= m
  ) => Lemma n m
```

This declaration simply connects the proof goal `n <= m` with the class name
`Lemma`. Next, we extend it to the full statement to be proven, which we do
by introducing an instance of `Lemma n m` that requires a proof for the premise
`n + 1 <= m`.

```haskell
instance
  ( n + 1 <= m
  ) => Lemma n m
```

If we now just give these two declarations to GHC, it will complain with the
aforementioned `Cannot satisfy: n <= m` error, as GHC still cannot deduce the
correctness of the given statement on its own. The plugin solves this issue,
but only if there is an actual proof of the statement that can be verified
with one of the supported proof assistants. We pick Coq here, which allows to
prove the statement with the following proof.

```Coq
Require Import Coq.Arith.PeanoNat.

Lemma hsLemma: forall n m, n + 1 <= m -> n <= m.
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
Qed.
```

This proof can now be added at the Haskell side with a so called
_proof comment_. It is introduced by adding a comment that starts with
`{-/ Proof (<prover>): <name>` and ends with `/-}` to the module defining
the `Lemma` instance and class. `<prover>` selects the proof assistant
(`Coq` in our case) and `<name>` matches with the name of the corresponding
class. In summary, we have

```haskell
instance
  ( n + 1 <= m
  ) => Lemma n m
class -- =>
  ( n <= m
  ) => Lemma n m where
{-/ Proof (Coq): Lemma
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
/-}
```

_(Note that you also can introduce multiple premises and multiple conclusions
within the same proof, by `,`-separating them at the left-hand-side of the
`=> Lemma n m` statements above.)_

### Verifying the proof

The plugin now takes care of verifying the proof and introducing the required
evidence. To this end, the `UndecidableInstances` and `UndecidableSuperClasses`
language extensions and the plugin must be enabled. You can do so easily via
adding the following pragmas at the top of your file.

```haskell
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_GHC -fplugin=GHC.TypeNats.Proof.Plugin #-}
```

With all that at hand, GHC accepts the proof without further complaints. Note
that the plugin is calling `coqc` in the background to actually verify the proof.
Thus, you also need to have `coqc` in your PATH to make this work. See below on
how to disable proof verification, if this is not desired. We currently do not
support using `rocq compile` instead.

### Using the proof

While GHC now accepts the given instance / class combination, due to the plugin
and the provided proof, it still is not obvious yet how to actually make use of
that proof. To this end, the plugin also comes with a new `QED` class in
`GHC.TypeNats.Proof`, which offers some simple interfaces to make use of the
proof. The final step is to make `Lemma n m` an instance of `QED`.

```haskell
instance Lemma n m => QED (Lemma n m)
```

This allows to use the proof wherever this `QED` instance is in scope. There are
three possible options for applying a proof.

  1. Via the `apply` method eliminating a constraint that has a `QED` instance.

     ```haskell
     apply :: QED c => (c => a) -> a
     ```

  2. Via the `using` method and a pattern match on the `Rewrite` that brings the
     proven constraint into scope.

     ```haskell
     using :: QED c => Rewrite c
     ```

  3. Via the `AutoProve` feature of the plugin, enabled by

     ```
     {-# OPTIONS_GHC -fplugin-opt=GHC.TypeNats.Proof.Plugin:AutoProve=True #-}
     ```

     The feature is disabled by default.

Have a look at `examples/Intro.hs` to see all three of these methods in action.

### More features of the plugin

#### Checking the proof files

Developing a proof usually won't happen within a Haskell source comment.
Therefore, the plugin generates a prover specific file for every proof
comment it encounters. These files are stored in the _proof directory_
(`proofs` by default), which is automatically generated by the plugin. Within
this folder, you will find another sub-folder, depending on the chosen prover,
followed by a copy of your module hierarchy tree leading to the actual proofs.

If you don't immediately have a proof for your Haskell defined property at hand,
just leave out the actual proof from the comment and use the generated file to
develop your proof separately first. The generated files will contain the proof
signatures as they have been derived from the Haskell definitions and been
translated to the syntax of the selected prover. As soon as you developed a
working proof, you can copy it back to the comment in your Haskell code.

The folder for storing the proofs can be adjusted by the following plugin command
line option:

```haskell
{-# OPTIONS_GHC -fplugin-opt=GHC.TypeNats.Proof.Plugin:ProofDir=<path> #-}
```

#### Adding a preamble to the proof

It might be necessary to import existing proofs or other features from a library,
or to declare some intermediate lemmata. The proof comments only contain the
actual proofs of the final statements, hence, they are not amenable to bring
such dependencies into scope. Instead, you can use a _preamble comment_ for that,
which starts with `{-/ Preamble (<prover>):` and ends with `/-}`. Preamble
comments can appear anywhere in your source file. Their content is concatenated
and added at the start of every proof resulting from a proof comment within the
same file.

For example, a preamble that is required by the introductory example above
would be

```haskell
{-/ Preamble (Coq):
Require Import Coq.Arith.PeanoNat.
/-}
```

Note that the plugin automatically adds imports for some of the standard libraries
on demand to support most of the popular type level operations on naturals.

#### Disabling proof verification

The plugin requires the utilized proof assistants to be installed for checking
the proofs. However, that might not be desirable when sharing a package, as
users might not have the particular proof assistants set up. In that regard,
proof checking can be disabled via

```haskell
{-# OPTIONS_GHC -fplugin-opt=GHC.TypeNats.Proof.Plugin:VerifyProofs=False #-}
```

In that case, the plugin still will provide the evidence required by GHC's
constraint solver to compile the code, but it will neither create any files
nor call any external tools.

### Incompleteness of `AutoProve`

It might be important to note that the `AutoProve` feature won't always be able
to deduce the required evidence from the available proofs being in scope. The
feature is sound, but incomplete due to the problem being undecidable in
general.

If automatic proof application fails, you still are able to manually select
the right proofs via `using` and `apply`. The `AutoProve` feature is designed
to fail if multiple proofs with an applicable proof goal are in scope and the
choice of the right proof to apply is ambiguous.

### GHC Requirements

The plugin currently only supports GHC 9.10.

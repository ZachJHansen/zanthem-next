# anthem

These are usage instructions for the version deployed on anya (May 1st, 2024).

## Translate

Translating a logic program into a first-order theory:
```sh
$ ./anthem translate <path>.lp --with tau-star
$ ./anthem translate <path>.lp --with completion
$ ./anthem translate <path>.lp --with gamma 
```

Translating a first-order theory into another first-order theory:
```sh
$ ./anthem translate <path>.spec --with completion
$ ./anthem translate <path>.spec --with simplify
```

By default, simplifications are NOT applied. To enable simplifications, add a `--simplify` or `-s` flag. For example,
```sh
$ ./anthem translate <path>.lp --with tau-star -s
```

## Verify

Verifying a logic program against a specification:
```sh
$ ./anthem verify <specification path>.spec <program path>.lp <user guide>.ug --direction forward
$ ./anthem verify <specification path>.spec <program path>.lp <user guide>.ug --direction backward
```
The preceding pair of calls is equivalent to 
```sh
$ ./anthem verify <specification path>.spec <program path>.lp <user guide>.ug --direction universal
```
or, since universal is the default proof direction, to
```sh
$ ./anthem verify <specification path>.spec <program path>.lp <user guide>.ug
```

Verifying the external equivalence of two logic programs:
```sh
$ ./anthem verify <original>.lp <alternative>.lp <user guide>.ug
```

For convenience, you can use the `verify-alt` command in conjunction with a problem directory. For example, the primes problem is arranged as follows:
```sh
primes/
  primes.1.lp
  primes.2.lp
  primes.ug
  primes.help.spec
```
The alphabetically first program (in this case, `primes.1.lp`) is treated as the specification/original program. The commands
```sh
$ ./anthem verify primes/primes.1.lp primes/primes.2.lp primes/primes.ug primes/primes.help.spec
$ ./anthem verify-alt primes
```
can be used interchangeably.

By default, simplifications and equivalence breaking are applied. To disable these features, add the flags `--no-simplify` and `--no-break`. For example,
```sh
$ ./anthem verify-alt primes --no-simplify --no-break
```

The general form of a verify command is:
```sh
$ ./anthem verify <specification path> <program path>.lp <user guide>.ug <proof outline>.help.spec --with <strategy> --cores <n> --parallel
```
where `strategy` is "default" or "sequential", `cores` specifies the number of cores for `vampire` to use, and the setting the `--parallel` flag instructs `anthem` to run both directions of the proof simultaneously.

## Writing Proof Outlines
`anthem` supports lists of helper lemmas with a ".help.spec" extension. Lemmas have the syntax `lemma(direction): formula`. For example:
```sh
lemma(forward): exists N$i (p(N$i) and N$i > 0).
lemma(backward): exists N$i (q(N$i) and N$i < 0).
lemma(universal): forall X M$i N$i ( M$i > 1 and N$i > 1 and X = M$i * N$i -> M$i <= X and N$i <= X ).
```
`anthem` will attempt to prove the first lemma as the first step of the forward direction of the proof (deriving the program from the specification). Similarly, it will attempt to prove the second lemma as the first step of the backward direction of the proof (deriving the specification from the program). The last lemma will be the first step attempted in both directions. It can also be written as
```sh
lemma: forall X M$i N$i ( M$i > 1 and N$i > 1 and X = M$i * N$i -> M$i <= X and N$i <= X ).
```

## Extra Information
Prefacing a command with `RUST_LOG=INFO` will provide additional information like system runtimes. For example, running
```sh
$ RUST_LOG=INFO ./anthem verify-alt examples/primes
```
will display summaries (premises and conjectures) of the claims being proven (forward, backward) and the time in milliseconds required to prove each conjecture.

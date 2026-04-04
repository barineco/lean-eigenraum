# Contributing

[日本語](CONTRIBUTING-ja.md)

## Issues

Issue reports are welcome. In particular:

- mathematical errors or unjustified steps in the proof chain
- missing or unclear premises in theorem statements
- Mathlib API breakage after upstream updates

## Pull Requests

Pull requests must satisfy:

- **Zero `sorry`.** The build (`lake build`) must complete with no `sorry` in any theorem.
- **Premises declared.** Every theorem must be self-contained: all assumptions appear in the type signature. No implicit axioms beyond what Mathlib provides.
- **Narrowly scoped.** One theorem file or topic per PR.

If adding a new file, add its import to `Eigenraum.lean` and update the proof map in both README files.

## Build

```sh
lake exe cache get
lake build
```

## Mathlib Updates

When updating the Mathlib dependency, verify that all existing theorems still build. If Mathlib API changes break a proof, fix it in the same commit.

# ACE Verification Setup

We aim to verify parts of the ACE Security Monitor using the [RefinedRust toolchain](https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev) and the [Coq proof assistant](https://coq.inria.fr/).
This file documents the basic verification setup.


## Architecture


## Installation
For using the RefinedRust toolchain and checking the verified parts of the code, you need to install both the Coq proof assistant and RefinedRust Coq libraries as well as the RefinedRust frontend.

First of all, open a terminal and navigate to the directory containing this file.
Then, clone the RefinedRust repository into a subdirectory:
```
git clone https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev.git refinedrust
```

### Installing Coq and the RefinedRust Coq libraries

First of all, we will install Coq and the RefinedRust Coq implementation.
For that, you are going to need [opam](https://opam.ocaml.org/) installed.
If you have not installed opam yet, refer to the instructions at https://opam.ocaml.org/doc/Install.html.
After the first installation, run `opam init`.

Now, run the following commands in the shell opened previously:
```
opam switch create refinedrust-ace --packages=ocaml-variants.4.14.1+options,ocaml-option-flambda
eval $(opam env)
opam switch link refinedrust-ace .

REFINEDRUST_ROOT=$PWD/refinedrust ./refinedrust/scripts/setup-coq.sh
REFINEDRUST_ROOT=$PWD/refinedrust ./refinedrust/scripts/install-typesystem.sh

```

The setup script will setup your opam switch to include all dependencies of RefinedRust.
Afterwards, we install Lithium (the proof automation engine RefinedRust uses) as well as RefinedRust itself.

### Installing the RefinedRust frontend

In the next step, we setup the RefinedRust frontend used for translating Rust code into Coq.
For that, you are going to need a working installation of Rust and [rustup](https://rustup.rs/).
If you do not have rustup installed yet, follow the instructions at https://rustup.rs/.  If you already have rustup installed, but it is old, you may want/need to run `rustup update`

Now, run the following commands in the shell opened previously:
```
REFINEDRUST_ROOT=$PWD/refinedrust ./refinedrust/scripts/setup-rust.sh
cd $PWD/refinedrust/rr_frontend && rustup target add riscv64gc-unknown-none-elf
REFINEDRUST_ROOT=$PWD/refinedrust ./refinedrust/scripts/install-frontend.sh
```

This will install binaries `refinedrust-rustc` and `cargo-refinedrust` in your cargo path.
This allows us to run `cargo refinedrust` in Rust projects.

## Verifying the code

Now, we are ready to run the verification.
To that end, run
```
make verify
```

This repo is the home of **FreerDPS**.

FreerDPS stands for : **Freer** *E*quational *R*easoning for **D**istributed and **P**robabilistic **S**ystems.

# Install

## Libraries

You need to install the following libraries for the project to work :
- coq 9.0 (it will use rocq as soon as monae makes the move)
- monae
- infotheo
- mathcomp

## Commands

Mainly for interns installing it first time :

```sh
opam switch create . ocaml-base-compiler.4.14.2
eval $(opam env)
opam pin add coq 9.0.0

```

In case monae / infotheo can not be installed through opam, you can clone them from github and fix their versions.

Versions known to work :
- monae : dev
- infotheo : 0.9.6

# Publications 

As of now, no work have been peer-reviewed.
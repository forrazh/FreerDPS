This repo is the home of **FreerDPS**.

FreerDPS stands for : **Freer** *E*quational *R*easoning for **D**istributed and **P**robabilistic **S**ystems.

# Code structure

As of now, the code base is mainly a rewrite/extension of [FreeSpec Core](https://github.com/lthms/FreeSpec) using [monae](https://github.com/affeldt-aist/monae) / ssreflect.

# Install

## Libraries

You need to install the following libraries for the project to work :
- Rocq 9.0
- monae
- infotheo
- mathcomp
- hierarchy builder

## Commands

Mainly for interns installing it first time :

```sh
opam switch create . ocaml-base-compiler.4.14.2
eval $(opam env)
opam pin add coq 9.0.0
eval $(opam env)

opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-hierarchy-builder coq-mathcomp-ssreflect coq-mathcomp-algebra coq-mathcomp-character coq-mathcomp-field coq-mathcomp-fingroup coq-mathcomp-solvable coq-mathcomp-classical
opam install coq-monae coq-infotheo
```

In case monae / infotheo can not be installed through opam, you can clone them from github and fix their versions.

Versions known to work :
- monae : 0.9.2
- infotheo : 0.9.7

You just need to clone the repositories and run : 

```sh
eval $(opam env) # it should be the same switch as the one created above
oam pin add .
```

inside the repository.

Once everything is installed, you can run the following commands :

```sh
make
```


# Publications 

This work has been submitted and accepted to [COMPAS26](https://2026.compas-conference.fr/) (no paper available online). 

# Formalization of PoS-NSB probabilistic bounds

This repository contains a formaltization of the probabilistic bounds in the 
the article Formalizing Nakamoto-Style Proof-of-Stake that can be found here :

[Formalizing Nakamoto-Style Proof-of-Stake](https://arxiv.org/pdf/2007.12105)



The formalization is currently not finished, only the probabilistic bound for the Chain Growth theorem is. 

You can find the bounds formalization in : 
- Properties/Prob_Bounds.v

I added some usefull lemmas that are used in my formalization in :
- Properties/additional_lemmas.v

The three theorems can be found in those files :
- Properties/CG.v (for Chain Growth)
- Properties/CQ.v (for Chain Quality) 
- Properties/CP.v (for Common Prefix)


The Chernoff lemma used can be found in :
- Properties/sampling.v (using mainly sampling_ineq2 and sampling_ineq3)

I also had to add the Rstruct_topology file that can be found here :
- Properties/Rstruct_topology.v (will be removed or moved at the end)



## Meta

- Author(s) of the article:
  - Søren Eller Thomsen
  - Bas Spitters
- Compatible Rocq versions: 9.0.0 or later
- Additional dependencies:
  - [rocq-mathcomp-ssreflect 2.5.0](https://math-comp.github.io)
  - [rocq-mathcomp-finmap 2.2.2](https://github.com/math-comp/finmap)
  - [rocq-mathcomp-analysis 1.16.0](https://github.com/math-comp/analysis)
  - [rocq Equations 1.3.1](https://github.com/mattam82/Coq-Equations)
  - [Coq record update 0.3.6](https://github.com/tchajed/coq-record-update)
  - [rocq-hierarchy-builder 1.10.2](https://github.com/math-comp/hierarchy-builder)
- Coq namespace: `AUChain`
- Related publication(s):
  - [Formalizing Nakamoto-Style Proof of Stake](https://arxiv.org/abs/2007.12105) 

## Building
The requirements can be installed via [OPAM](https://opam.ocaml.org/doc/Install.html):
```
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install \
     rocq-prover.9.0.0 \
     rocq-mathcomp-ssreflect.2.5.0 \
     rocq-mathcomp-finmap \
     rocq-mathcomp-analysis \
     rocq-equations \
     coq-record-update \
     rocq-hierarchy-builder
```
Then, run `make clean; make` from the root folder. This will build all
the libraries and check all the proofs.

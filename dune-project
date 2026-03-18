(lang dune 3.21)
(warnings (deprecated_coq_lang disabled))
(using coq 0.9)

(name FreerDPS)

(generate_opam_files true)

(authors "Hugo Forraz <hugo.forraz@univ-lille.fr>")


(package
 (name freerdps)
 (synopsis "A FreeSpec rewrite to bring the power of equational reasoning and probabilities.")
 (description "A longer description")
 (depends 
    (coq-monae (= "dev"))
    (coq-equations (="latest"))
    (coq-hierarchy-builder (= "latest"))
    (coq-mathcomp-ssreflect (= "latest"))
    (coq-mathcomp-algebra (= "latest"))
    (coq-mathcomp-character (= "latest"))
    (coq-mathcomp-field (= "latest"))
    (coq-mathcomp-fingroup (= "latest"))
    (coq-mathcomp-solvable (= "latest"))
    (coq-mathcomp-classical (= "latest"))
    (coq (= "9.0"))
    (coq-stdlib (= "9.0.0"))
    (coq-infotheo (= "dev"))
    ))

; monae and infotheo are in dev for now because we want 
; to use the latest coq version available, which is not 
; possible using the current opam versions.

(tags (rocq "distributed systems" probabilities))
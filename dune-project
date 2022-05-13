(lang dune 3.0)

(name miniml_compiler)

(generate_opam_files true)

(authors "samosica <samosic4@gmail.com>")

(package
 (name miniml_compiler)
 (synopsis "A compiler that translates a ML-like language into ARM assembly")
 (depends ocaml dune menhir))

(using menhir 2.0)

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project

(lang dune 3.13)

(name baby_pascal)

(generate_opam_files true)
(using menhir 3.0)

(source
 (github username/reponame))

(authors "Author Name")

(maintainers "Maintainer Name")

(license LICENSE)

(documentation https://url/to/documentation)

(map_workspace_root false)

(package
 (name baby_pascal)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml dune ppx_deriving ppx_expect containers containers-data logs alcotest)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project

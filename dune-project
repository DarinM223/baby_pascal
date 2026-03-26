(lang dune 3.7)

(name baby_pascal)

(generate_opam_files true)

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
 (depends ocaml dune ppx_deriving ppx_expect containers logs alcotest)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project

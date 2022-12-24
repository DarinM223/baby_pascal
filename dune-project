(lang dune 3.5)

(name baby_pascal)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name")

(maintainers "Maintainer Name")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name baby_pascal)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml dune ppx_deriving containers)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project

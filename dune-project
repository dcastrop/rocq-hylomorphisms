(lang dune 3.21)
(using rocq 0.11)

(name rocq-hylomorphisms)

(generate_opam_files true)

(source (github dcastrop/rocq-hylomorphisms))
(authors "David Castro-Perez" "Marco Paviotti" "Michael Vollmer")
(license GPL-3.0-or-later)
(maintainers "David Castro-Perez <David.CastroPerez@rhul.ac.uk>")

(package
 (name rocq-hylomorphisms)
 (synopsis "Hylomorphisms in Rocq")
 (depends
  (rocq-core (>= 9.2))
  rocq-stdlib
  (rocq-paco (>= 4.2.3))
  rocq-elpi))

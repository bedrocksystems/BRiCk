(lang dune 3.8)
(using coq 0.8)
(name coq-cpp2v)

(generate_opam_files)

(maintainers
 "Gregory Malecha <gregory@bedrocksystems.com>"
 "Abhishek Anand <abhishek@bedrocksystems.com>"
 "Gordon Stewart <gordon@bedrocksystems.com>")
(authors
 "Gregory Malecha <gregory@bedrocksystems.com>"
 "Abhishek Anand <abhishek@bedrocksystems.com>"
 "Gordon Stewart <gordon@bedrocksystems.com>")
(source (github bedrocksystems/cpp2v))

(package
 (name coq-cpp2v)
 (synopsis "Frontend and program logic for C++")
 (depends
  (coq (and (>= 8.18.0) (< 8.19~)))
  (coq-ext-lib (= 0.11.8))
  (coq-iris (= dev.2023-10-17.0.b990ffb7))
  coq-lens
  coq-lens-elpi
  (elpi (= 1.17.3)) ; We stick to a public version on the package.
  (coq-elpi (= 1.19.3))))

(package
 (name coq-cpp2v-bin)
 (synopsis "Binary package for cpp2v")
 (depends conf-clang))

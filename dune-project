(lang dune 3.14)
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
  (coq (and (>= 8.19.0) (< 8.20~)))
  coq-upoly
  (coq-iris (= dev.2024-03-06.1.9c192c8d))
  coq-lens
  coq-lens-elpi
  (elpi (= 1.18.2))
  (coq-elpi (= 2.0.2+bedrock+vanilla-coq)) ; FIXME this is not a public version.
  ))

(package
 (name coq-cpp2v-bin)
 (synopsis "Binary package for cpp2v")
 (depends conf-clang))

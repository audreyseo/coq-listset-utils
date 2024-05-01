(lang dune 3.14)

(name coq-listset-utils)

(using coq 0.8)

(generate_opam_files true)

(using directory-targets 0.1)

(source
 (github audreyseo/coq-listset-utils))

(homepage "https://github.com/audreyseo/coq-listset-utils")

(authors "Audrey Seo <audreyleeseo@gmail.com>")

(maintainers "Audrey Seo <audreyleeseo@gmail.com>")

(package
 (name coq-listset-utils)
 (synopsis
  "ListSetUtils: Utilities and helper lemmas for working with list-based sets")
 (description
  "The built-in Coq.Lists.ListSet has many useful lemmas for lightweight list-based sets, but is not complete by any means. This package supplements Coq.Lists.ListSet with extra utilities and tactics for making proofs about list-based sets easier.")
 (license MIT)
 (depends
  (coq-stdlib
   (and
    (>= 8.16)
    (< 8.17~)))))

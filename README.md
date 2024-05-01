coq-listset-utils
=======================

Working with Coq's `Coq.Lists.ListSet` library provides some
advantages: it's built on Coq's standard library, and doesn't
introduce any overhead of learning a new library. It is also, of
course, included with most installations of Coq. It's lightweight, and
often, this is the most I need. It also doesn't require instantiating
multiple modules, as with the standard library's implementations of
finite sets.

However, when reasoning about these list-based sets, I've often found
myself repeatedly re-proving the same properties over and over again,
or copying and pasting code from different projects.

While this library is not an exhaustive repository of all of the
properties and facts one might want about list-based sets, it includes
faculties for reasoning about a few key points:

- (In/ex)clusion in sets produced by folds (e.g., `List.fold_left`)
- Breaking down exclusion from unions, differences, etc. (e.g., `~ In
  x (set_union Xeq_dec s1 s2) -> ~ In x s1 /\ ~ In x s2`)
- Tactics for reducing set inclusions/exclusions down to their basic
  components (when this does not introduce more branches)

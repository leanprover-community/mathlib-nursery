## `mathlib-nursery`

[![Build Status](https://travis-ci.org/leanprover-community/mathlib-nursery.svg?branch=master)](https://travis-ci.org/leanprover-community/mathlib-nursery)

This is a community-maintained library for [Lean](https://leanprover.github.io/)
code under development for contribution to
[`mathlib`](https://github.com/leanprover/mathlib).

### Background

`mathlib` has a high standard for contributions. This is natural because it
aspires to be the best common source for formalized mathematics in Lean. (And we
applaud this goal!)

A community has formed around `mathlib` due to a combination of the joy of
formalizing mathematics in Lean, `mathlib`'s coverage of mathematics, and the
quality of `mathlib`'s definitions and theorems.

Not everyone working on formalizing mathematics in Lean has the experience or
time to meet `mathlib`'s contribution standard. Therefore, some of us decided to
create `mathlib-nursery` to support each other in nursing projects by improving
upon them until they can be contributed to `mathlib`. Similarly, we can share
these work-in-progress projects here even though they may not be perfect.

### Contributions

Contributions to the `mathlib-nursery` are welcome!

**When should you contribute to `mathlib-nursery`?**

First of all, do you have some code that you believe could be a useful
contribution to `mathlib`? Consider these points:

* You're unsure about the quality of your code.
* You want support in improving it.
* You want to share your code with a wider audience (e.g. to get feedback before
  submission to `mathlib`).

If any of these apply, you've come to the right place!

**What are the requirements<sup>[1](#footnote1)</sup> for contribution?**

1. Your code should build.
2. There should be no `sorry`s or `_`.
3. The directory and file structure should roughly follow that of `mathlib`s.

That's it!

We'll gladly accept bad proofs and incomplete theories. But some people rely on
`mathlib-nursery` in their projects, so we don't want to burden them with broken
builds and `sorry` warnings.

If you do have a work-in-progress project that doesn't meet these requirements,
we recommend you create a repository for it. When it's ready, feel free to
contribute it to `mathlib-nursery`.

Note that an implication of our contribution policy is that the
`mathlib-nursery` could undergo significant changes from one commit to the next.
If you do depend on it, you should stick to the `git` revision that works for
you.

---

<sup><a name="footnote1">1</a></sup> These requirements apply only to the `master` branch.
If you work on a non-`master` branch, you can do whatever you want.

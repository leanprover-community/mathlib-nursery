## `mathlib-nursery`

[![Build status](https://travis-ci.org/leanprover-community/mathlib-nursery.svg?branch=master "Check the Travis CI build status")](https://travis-ci.org/leanprover-community/mathlib-nursery)
[![Join the chat](https://img.shields.io/badge/zulip-join_the_chat-blue.svg "Join the Zulip chat")](https://leanprover.zulipchat.com/)

This is a community-maintained library for [Lean](https://leanprover.github.io/)
code under development for contribution to
[`mathlib`](https://github.com/leanprover/mathlib).

### Background

`mathlib` has a high standard for contributions. This is natural because it
aspires to be the best common source for formalized mathematics in Lean. (And we
applaud this goal!)

A community (find us on [Zulip](https://leanprover.zulipchat.com/)) has formed
around `mathlib` due to a combination of the joy of formalizing mathematics in
Lean, `mathlib`'s coverage of mathematics, and the quality of `mathlib`'s
definitions and theorems.

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

1. Your code builds without errors or warnings.
2. The directory and file structure roughly follows `mathlib`'s.

That's it!

We will gladly accept “bad” proofs and incomplete theories. We're pretty relaxed
about code naming and quality. After all, the goal is to improve it
cooperatively towards the `mathlib` standard.

However, `mathlib-nursery` is still intended for sharing. Since some people rely
on `mathlib-nursery` in their projects, we don't want to burden them with broken
builds and warnings. Sorry, this means no `sorry`s or `don't know how to
synthesize placeholder` errors!

If you have a work-in-progress project that doesn't meet the above requirements,
we recommend creating a repository for it. When it's ready, feel free to
contribute it to `mathlib-nursery`.

Note that an implication of our contribution policy is that `mathlib-nursery`
could undergo significant changes from one commit to the next. If you do depend
on it, you should stick to the `git` revision that works for you.

---

<sup><a name="footnote1">1</a></sup> These requirements apply only to the `master` branch.
If you work on a non-`master` branch, you can do whatever you want.

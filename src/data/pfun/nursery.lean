/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import data.set.basic data.option data.equiv.basic data.pfun

namespace roption
variables {α : Type*} {β : Type*} {γ : Type*}

open function
lemma assert_if_neg {p : Prop}
  (x : p → roption α)
  (h : ¬ p)
: assert p x = roption.none :=
by { dsimp [assert,roption.none],
     have : (∃ (h : p), (x h).dom) ↔ false,
     { split ; intros h' ; repeat { cases h' with h' },
       exact h h' },
     congr,
     repeat { rw this <|> apply hfunext },
     intros h h', cases h', }

lemma assert_if_pos {p : Prop}
  (x : p → roption α)
  (h : p)
: assert p x = x h :=
by { dsimp [assert],
     have : (∃ (h : p), (x h).dom) ↔ (x h).dom,
     { split ; intros h'
       ; cases h' <|> split
       ; assumption, },
     cases hx : x h, congr, rw [this,hx],
     apply hfunext, rw [this,hx],
     intros, simp [hx] }

@[simp]
lemma roption.none_bind {α β : Type*} (f : α → roption β)
: roption.none >>= f = roption.none :=
by simp [roption.none,has_bind.bind,roption.bind,assert_if_neg]

end roption

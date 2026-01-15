import Mathlib


/- ### Exercises for January 13 -/

/- Starting examples and exercises. I'll explain a few things as I go along, and later post notes with the explanations, but there will be a lot learning by imitating.  

In the next class there will be a more detailed explanation of what's going on. -/

/- I will give several different proofs of the identity

(a + b) + cd = (dc + b) + a

-/

example (a b c d : ℝ) : (a + b) + c * d = (d * c + b) + a := by
  sorry


/- Now you try. Give a proof using `rw` and (optionally) `calc`. (But not `ring`.) There is something a bit tricky here -/
/- # Exercise  1 -/

example (a b c d  : ℝ): a + (b + c) = b + (a + c) := by
  sorry

/- # Exercise 2 -/


example (a b c d  : ℝ) : a * b * c * d = d * c * a * b := by
  sorry


/- Prove something from hypotheses.  -/

example(a b c d : ℝ ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d :=
by
  rw [hyp, hyp']
  rw [mul_comm]
  rw [<-two_mul ]
  rw [<-mul_assoc]

/-another proof of the same thing using `ring`,`calc`, and rewriting hypotheses-/
example(a b c d : ℝ ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d :=
by
  rw [hyp'] at hyp
  calc
    c = d * a + a * d := hyp
    _ = 2 * a * d := by ring

/-
# Exercise 3
Now you try.  -/
example (a b c d e f: ℝ ) (h : b * c = e * f):
a * b * c * d = a * e * f * d := by
  sorry



/- For the next exercise, use the theorem  `sub_self` along with the theorems about commutativity and associativity of addition and multiplication: If `x` is an expression of type ℝ, then `sub_self x` proves `x - x = 0`. -/

/- # Exercise 4 -/
example (a b c d : ℝ)(h₁: c = b * a - d)(h₂: d = a * b): c = 0 := by
  sorry

/- Using distributivity and subtraction. -/
/- Do not use `ring`.-/

example  (a b c d : Real) : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  calc
     (a + b) * (c + d) = a * (c + d) + b * (c + d) := by rw [add_mul]
     _                 = a * c + a * d + b * c + b *d := by rw [mul_add,mul_add,<-add_assoc]

/-
# Exercise 5

Now you try it. You need to know the names of theorems like

a * (b - c) = a * b - a * c ,
and maybe some others
What do you think it might be called?  How can you find out?-/

example (a b c d : ℝ): (a + b) * (c - d) = a * c - a * d + b * c - b * d := by
  sorry


/- I will illustrate this one in class:-/

example (a b  : ℝ): (a + b)^2 = a^2 + 2 * a * b + b ^2 :=
by
  calc
    (a + b)^2 = (a + b) * (a + b) := pow_two (a + b)
    _         = a * (a + b) + b * (a + b) := by rw [add_mul]
    _         = a * a + a * b + b * a + b * b := by rw [mul_add,mul_add,<-add_assoc]
    _         = a^2 + a * b + a * b + b^2 := by rw [pow_two,pow_two,mul_comm b a]
    _         = a^2 + 2 * a * b + b^2 := by rw [add_assoc,add_assoc,<-add_assoc (a * b),<-two_mul,<-mul_assoc,add_assoc]


/- Try this exercise, which is more challenging. -/

/- # Exercise 6-/

example (a b  : ℝ): (a - b)^2 = a^2 - 2 * a * b + b ^2 :=
by sorry

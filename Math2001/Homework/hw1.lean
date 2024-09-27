/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import AutograderLib

math2001_init

/-! # Homework 1

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-1,
for clearer statements and any special instructions. -/


@[autograded 5]
theorem problem1 {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 := by
  have h3 : q = 3 := by addarith[h2]
  calc
    p = p + 4*q - 4*q := by ring
    _ = 1 - 4*3 := by rw[h1,h3]
    _ = -11 := by numbers

@[autograded 5]
theorem problem2 {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 := by
  have hn : b = 1 :=
  calc
    b = ((a+2*b)-(a-b))/3 := by ring
    _ = (4 - 1) /3 := by rw[h1,h2]
    _ = 1 := by numbers
  calc
    a = a - b + b := by ring
    _ = 1 + 1 := by rw[h2,hn]
    _ = 2 := by numbers


@[autograded 5]
theorem problem3 {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 := by
  calc
    x^3 - 8*x^2 + 2*x = (x-8)*x^2 + 2*x := by ring
    _ ≥ (9-8)*x^2 + 2*x := by rel[hx]
    _ = x*(x+2) := by ring
    _ ≥ 9*(9+2) := by rel[hx]
    _ ≥ 3 := by numbers

@[autograded 5]
theorem problem4 {x : ℚ} : x ^ 2 - 2 * x ≥ -1 := by
  calc
    x^2 - 2*x = (x-1)^2 - 1 := by ring
    _ ≥ -1 := by extra

@[autograded 5]
theorem problem5 (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have hp: 0 ≤ (b+a) := by addarith[h1]
  have hm: 0 ≤ (b-a) := by addarith[h2]
  calc
    b^2 = b^2 - a^2 + a^2 := by ring
    _ = (b-a)*(b+a) + a^2 := by ring
    _ ≥ a^2 := by extra

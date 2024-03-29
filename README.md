# Simpl

Simpl is a simple imperative language designed for teaching programming languages theory. This project implements Simpl as both an untyped dialect with only ints and a typed dialect allowing for both bools and ints. These assignments were done at UTD under Professor Kevin Hamlen.

## Untyped Simpl

An untyped dialect for Simpl with an automatic [large step semantics](https://www.cs.cornell.edu/courses/cs4110/2012fa/lectures/lecture04.pdf) deriver.

We can implement a prime checking algorithm in untyped simpl like so:

```
if (arg0 <= 1) then ret := 0 else ret := 1;
x := 2;
while (!(ret <= 0) && (2*x <= arg0)) do (
  y := x;
  while (!(ret <= 0) && (y <= arg0)) do (
    if (arg0 <= y) then
      ret := 0
    else
      y := y + x
  );
  x := x + 1
)
```

A large step semantics derivation for the prime checking algorithm would look like so:
```
if (arg0 <= 1) then (ret := 0) else (ret := 1); x := 2; while ((!(ret <= 0)) && ((2 * x) <= arg0)) do (y := x; while ((!(ret <= 0)) && (y <= arg0)) do (if (arg0 <= y) then (ret := 0) else (y := (y + x))); x := (x + 1))

<ret, σ2> ⇓ 0  <0, σ2> ⇓ 0  <2, σ2> ⇓ 2  <x, σ2> ⇓ 2

<(ret <= 0), σ2> ⇓ true  <(2 * x), σ2> ⇓ 4  <arg0, σ2> ⇓ 0

<(!(ret <= 0)), σ2> ⇓ false  <((2 * x) <= arg0), σ2> ⇓ false

<arg0, σ0> ⇓ 0  <1, σ0> ⇓ 1  <0, σ0> ⇓ 0  <2, σ1> ⇓ 2  <((!(ret <= 0)) && ((2 * x) <= arg0)), σ2> ⇓ false  <Skip, σ2> ⇓ σ1[x->2]

<(arg0 <= 1), σ0> ⇓ true  <ret := 0, σ0> ⇓ σ0[ret->0]  <x := 2, σ1> ⇓ σ1[x->2]  <if ((!(ret <= 0)) && ((2 * x) <= arg0)) then (y := x; while ((!(ret <= 0)) && (y <= arg0)) do (if (arg0 <= y) then (ret := 0) else (y := (y + x))); x := (x + 1); while ((!(ret <= 0)) && ((2 * x) <= arg0)) do (y := x; while ((!(ret <= 0)) && (y <= arg0)) do (if (arg0 <= y) then (ret := 0) else (y := (y + x))); x := (x + 1))) else (Skip), σ2> ⇓ σ1[x->2]

<if (arg0 <= 1) then (ret := 0) else (ret := 1), σ0> ⇓ σ0[ret->0]  <x := 2; while ((!(ret <= 0)) && ((2 * x) <= arg0)) do (y := x; while ((!(ret <= 0)) && (y <= arg0)) do (if (arg0 <= y) then (ret := 0) else (y := (y + x))); x := (x + 1)), σ1> ⇓ σ1[x->2]

<if (arg0 <= 1) then (ret := 0) else (ret := 1); x := 2; while ((!(ret <= 0)) && ((2 * x) <= arg0)) do (y := x; while ((!(ret <= 0)) && (y <= arg0)) do (if (arg0 <= y) then (ret := 0) else (y := (y + x))); x := (x + 1)), σ0> ⇓ σ1[x->2]

Ret: 0
```

## Typed Simpl

A typechecked dialect of Simpl with support for both integers and booleans.

The following is the example of a fibonacci finding algorithm in typed simpl:

```
int ret;
int a;
int b;
ret := 1;
a := 0;
b := 1;
while !(arg0 <= 0) do (
  int tmp;
  arg0 := arg0 - 1;
  tmp := a;
  a := b;
  b := tmp + b;
  ret := a
)
```
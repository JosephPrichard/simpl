# Simpl

Simpl is a simple imperative language designed for teaching programming languages theory. This project implements Simpl as both an untyped dialect with only ints and a typed dialect allowing for both bools and ints. These assignments were done at UTD under [Professor Kevin Hamlen](https://personal.utdallas.edu/~hamlen/).

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
```

## Typed Simpl

A typechecked dialect of Simpl with support for both integers and booleans.

The following is an example of a fibonacci finding algorithm in typed Simpl:

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

## Functional Simpl

A functional dialect of Simpl with support for functional abstraction and application.

The following is an example of a program to count to a threshold using a functional abstraction to determine the next counter in the loop.
We set the return value of the function by assigning to the "ret" variable. Variable "ret" must be declared in the function body for a function to be valid.

```
int ret;
ret := 0;

fun(int * int * (fun(int->int)) -> int) count;

count := fun(int x, int until, fun(int->int) next) {
    while (x <= until) do (
       x := next(x)
    );
    int ret;
    ret := x
};

ret := count(1, arg0, fun(int x) { int ret; ret := x * 2 })
```

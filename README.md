# OCaml-MPST-Light

A lightweight implementation of [ocaml-mpst](https://github.com/keigoi/ocaml-mpst).


## Try OCaml-MPST [Online](https://keigoi.github.io/ocaml-mpst-light/index.html)!

* An interactive programming interface is available at:
  * https://keigoi.github.io/ocaml-mpst-light/index.html

![Try OCaml-MPST Screenshot](https://keigoi.github.io/ocaml-mpst-light/screenshot.png)

[Try OCaml-MPST Online](https://keigoi.github.io/ocaml-mpst-light/index.html)


## Source Code

* For better understanding of implementation code, we prepared [Mpst_no_lin_check](mpst_no_lin_check.ml) (no linearity checks) with comments.

* Linearity checking:
  * [Mpst_light](mpst_light.ml) The body of implementation (dynamic linearity checking)
  * [Mpst_static](static/mpst_no_lin_check.ml): Static linearity checking

* Other modules and sub-packages:
  * [Base](base.ml): Utility types and modules
  * [concur-shims](packages/concur-shims): Rough adjustment of Lwt to OCaml's threads package
  * [linocaml-light](packages/linocaml-light): 

* Examples: See [examples/](examples/).


## Try Offline

```sh
$ ./compile_without_dune.sh
```

Or, if you have dune installed:

```sh
$ dune utop
```

Then you can play ocaml-mpst-light within OCaml toplevel:

```ocaml
# open Mpst_light;;

# (a --> b) msg finish;;
- : < role_B : < msg : ('_weak1, unit lin) out lin > > local *
    < role_A : _[> `msg of '_weak1 * unit lin ] inp lin > local *
    unit lin local
= (<abstr>, <abstr>, <abstr>)

# fix (fun t -> choice_at a (to_b left_or_right) (a, (a-->b) left t) (a, (a-->b) right finish));;
- : (< role_B : < left : ('_weak2, 'a) out lin;
                  right : ('_weak3, unit lin) out lin > >
     as 'a)
    local *
    (< role_A : _[> `left of '_weak2 * 'b | `right of '_weak3 * unit lin ]
                inp lin >
     as 'b)
    local * unit lin local
= (<abstr>, <abstr>, <abstr>)

# 
```


## Install (Experimental)

```sh
$ git clone https://github.com/keigoi/ocaml-mpst-light.git
$ cd ocaml-mpst-light
$ opam install ocaml-mpst-light
$ opam install ocaml-mpst-light.static
```
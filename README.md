# OCaml-MPST-Light

An even-more lightweight implementation of [ocaml-mpst](https://github.com/keigoi/ocaml-mpst)

* [Mpst_light](mpst_light.ml) The body of implementation
  * [Base](base.ml): Utility types and modules
  * [concur-shims](packages/concur-shims): Rough adjustment of Lwt to OCaml's threads package
* [Mpst_no_lin_check](mpst_no_lin_check.ml): Yet another implementation without linearity, for better understanding of implementation
* [Mpst_static](static/mpst_no_lin_check.ml): Static linearity checking
  * [linocaml-light](packages/linocaml-light): 
* [examples/](examples/): Examples

## Try

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

Note that if you have installed `lwt` via opam, `dune` automatically selects `lwt`-enabled version of ocaml-mpst-light.

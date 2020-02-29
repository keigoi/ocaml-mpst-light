open Migrate_parsetree

let init () =
  let module Converter =
    Migrate_parsetree.Versions.Convert
      (Migrate_parsetree.OCaml_408)
      (Migrate_parsetree.OCaml_current)
  in
  let mapper = Converter.copy_mapper Ppx_linocaml.mapper in
  Compiler_libs.Ast_mapper.register "ppx_linocaml" (fun _ -> mapper)

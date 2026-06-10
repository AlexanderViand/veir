// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<17 : i32>) -> i16, sym_name = "main"}> ({
    ^bb0(%0 : !mod_arith.int<17 : i32>):
      %r = "mod_arith.extract"(%0) : (!mod_arith.int<17 : i32>) -> i16
      "func.return"(%r) : (i16) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: mod_arith.extract: Expected the result bitwidth to match the modulus storage bitwidth

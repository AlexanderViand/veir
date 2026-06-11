// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i16) -> !mod_arith.int<17 : i32>, sym_name = "main"}> ({
    ^bb0(%0 : i16):
      %r = "mod_arith.encapsulate"(%0) : (i16) -> !mod_arith.int<17 : i32>
      "func.return"(%r) : (!mod_arith.int<17 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: mod_arith.encapsulate: Expected the operand bitwidth to match the modulus storage bitwidth

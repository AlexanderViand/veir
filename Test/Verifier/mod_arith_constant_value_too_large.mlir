// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> !mod_arith.int<17 : i32>, sym_name = "main"}> ({
    %c = "mod_arith.constant"() <{"value" = 17 : i32}> : () -> !mod_arith.int<17 : i32>
    "func.return"(%c) : (!mod_arith.int<17 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: mod_arith.constant: Expected the value to be in the canonical range [0, modulus)

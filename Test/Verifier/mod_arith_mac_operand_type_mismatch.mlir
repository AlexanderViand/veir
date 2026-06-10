// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>, !mod_arith.int<13 : i32>) -> !mod_arith.int<17 : i32>, sym_name = "main"}> ({
    ^bb0(%0 : !mod_arith.int<17 : i32>, %1 : !mod_arith.int<17 : i32>, %2 : !mod_arith.int<13 : i32>):
      %r = "mod_arith.mac"(%0, %1, %2) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>, !mod_arith.int<13 : i32>) -> !mod_arith.int<17 : i32>
      "func.return"(%r) : (!mod_arith.int<17 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: mod_arith.mac: Expected operands to have the same type

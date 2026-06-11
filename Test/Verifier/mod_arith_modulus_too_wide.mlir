// RUN: not veir-opt %s 2>&1 | filecheck %s

// The storage type must be at least one bit wider than the modulus: 200 does not
// fit into 7 bits, so i8 storage is rejected (following HEIR's mod_arith rules).

"builtin.module"() ({
  "func.func"() <{function_type = () -> !mod_arith.int<200 : i8>, sym_name = "main"}> ({
    %c = "mod_arith.constant"() <{"value" = 3 : i8}> : () -> !mod_arith.int<200 : i8>
    "func.return"(%c) : (!mod_arith.int<200 : i8>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: mod_arith.constant: Expected the storage type to be at least one bit wider than the modulus

// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !mod_arith.int<251 : i16>}> ({
    %lhs = "mod_arith.constant"() <{ "value" = 250 : i16 }> : () -> !mod_arith.int<251 : i16>
    %rhs = "mod_arith.constant"() <{ "value" = 10 : i16 }> : () -> !mod_arith.int<251 : i16>
    %sum = "mod_arith.add"(%lhs, %rhs) : (!mod_arith.int<251 : i16>, !mod_arith.int<251 : i16>) -> !mod_arith.int<251 : i16>
    "func.return"(%sum) : (!mod_arith.int<251 : i16>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0009#16]

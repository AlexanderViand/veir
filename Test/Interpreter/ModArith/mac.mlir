// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !mod_arith.int<251 : i16>}> ({
    %lhs = "mod_arith.constant"() <{ "value" = 250 : i16 }> : () -> !mod_arith.int<251 : i16>
    %rhs = "mod_arith.constant"() <{ "value" = 10 : i16 }> : () -> !mod_arith.int<251 : i16>
    %acc = "mod_arith.constant"() <{ "value" = 3 : i16 }> : () -> !mod_arith.int<251 : i16>
    // (250 * 10 + 3) mod 251 = 2503 mod 251 = 244
    %res = "mod_arith.mac"(%lhs, %rhs, %acc) : (!mod_arith.int<251 : i16>, !mod_arith.int<251 : i16>, !mod_arith.int<251 : i16>) -> !mod_arith.int<251 : i16>
    "func.return"(%res) : (!mod_arith.int<251 : i16>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00f4#16]

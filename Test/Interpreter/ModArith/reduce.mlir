// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !mod_arith.int<251 : i16>}> ({
    %c250 = "mod_arith.constant"() <{ "value" = 250 : i16 }> : () -> !mod_arith.int<251 : i16>
    %red = "mod_arith.reduce"(%c250) : (!mod_arith.int<251 : i16>) -> !mod_arith.int<251 : i16>
    "func.return"(%red) : (!mod_arith.int<251 : i16>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00fa#16]

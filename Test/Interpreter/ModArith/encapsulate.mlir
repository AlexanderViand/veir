// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !mod_arith.int<251 : i16>}> ({
    %c243 = "arith.constant"() <{ "value" = 243 : i16 }> : () -> i16
    %enc = "mod_arith.encapsulate"(%c243) : (i16) -> !mod_arith.int<251 : i16>
    "func.return"(%enc) : (!mod_arith.int<251 : i16>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00f3#16]

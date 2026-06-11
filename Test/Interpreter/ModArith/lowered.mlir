// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s -p=mod-arith-to-arith > %t.lowered.mlir && veir-interpret %t.lowered.mlir | filecheck %s
// RUN: veir-opt %s -p="mod-arith-to-arith,reconcile-cast" > %t.reconciled.mlir && veir-interpret %t.reconciled.mlir | filecheck %s

// Differential test: interpreting the program before lowering, after lowering, and after
// lowering + cast reconciliation must produce the same output.
//
// Computes ((250 + 10) * 250 - 250) mod 251 = (9 * 250 - 250) mod 251 = (242 - 250) mod 251 = 243.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !mod_arith.int<251 : i16>}> ({
    %c250 = "mod_arith.constant"() <{ "value" = 250 : i16 }> : () -> !mod_arith.int<251 : i16>
    %c10 = "mod_arith.constant"() <{ "value" = 10 : i16 }> : () -> !mod_arith.int<251 : i16>
    %a = "mod_arith.add"(%c250, %c10) : (!mod_arith.int<251 : i16>, !mod_arith.int<251 : i16>) -> !mod_arith.int<251 : i16>
    %b = "mod_arith.mul"(%a, %c250) : (!mod_arith.int<251 : i16>, !mod_arith.int<251 : i16>) -> !mod_arith.int<251 : i16>
    %c = "mod_arith.sub"(%b, %c250) : (!mod_arith.int<251 : i16>, !mod_arith.int<251 : i16>) -> !mod_arith.int<251 : i16>
    "func.return"(%c) : (!mod_arith.int<251 : i16>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00f3#16]

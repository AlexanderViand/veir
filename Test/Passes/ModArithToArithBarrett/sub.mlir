// RUN: veir-opt %s -p=mod-arith-to-arith-barrett | filecheck %s

// Efficient lowering of mod_arith.sub: x + q - y of canonical operands lies in (0, 2q),
// fits in the storage type without widening, and a single conditional subtraction
// (instead of arith.remui) canonicalizes the result.

"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>, sym_name = "main"}> ({
    ^bb0(%0 : !mod_arith.int<7 : i32>, %1 : !mod_arith.int<7 : i32>):
      %r = "mod_arith.sub"(%0, %1) : (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>
      "func.return"(%r) : (!mod_arith.int<7 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}([[ARG0:%.*]] : !mod_arith.int<7 : i32>, [[ARG1:%.*]] : !mod_arith.int<7 : i32>):
// CHECK-NEXT:   [[C0:%.*]] = "builtin.unrealized_conversion_cast"([[ARG0]]) : (!mod_arith.int<7 : i32>) -> i32
// CHECK-NEXT:   [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[ARG1]]) : (!mod_arith.int<7 : i32>) -> i32
// CHECK-NEXT:   [[Q:%.*]] = "arith.constant"() <{"value" = 7 : i32}> : () -> i32
// CHECK-NEXT:   [[XQ:%.*]] = "arith.addi"([[C0]], [[Q]]) : (i32, i32) -> i32
// CHECK-NEXT:   [[T:%.*]] = "arith.subi"([[XQ]], [[C1]]) : (i32, i32) -> i32
// CHECK-NEXT:   [[GE:%.*]] = "arith.cmpi"([[T]], [[Q]]) <{"predicate" = 9 : i64}> : (i32, i32) -> i1
// CHECK-NEXT:   [[DIFF:%.*]] = "arith.subi"([[T]], [[Q]]) : (i32, i32) -> i32
// CHECK-NEXT:   [[RES:%.*]] = "arith.select"([[GE]], [[DIFF]], [[T]]) : (i1, i32, i32) -> i32
// CHECK-NEXT:   [[OUT:%.*]] = "builtin.unrealized_conversion_cast"([[RES]]) : (i32) -> !mod_arith.int<7 : i32>
// CHECK-NEXT:   "func.return"([[OUT]]) : (!mod_arith.int<7 : i32>) -> ()

// RUN: veir-opt %s -p=mod-arith-to-arith-barrett | filecheck %s

// Efficient lowering of mod_arith.mul via Barrett reduction at width 4N: the quotient of
// the exact product p is estimated as (p * ratio) >> 2N with the compile-time constant
// ratio = floor(2^(2N) / q) (here floor(2^64 / 7)), the corresponding multiple of q is
// subtracted, and a final conditional subtraction canonicalizes. No division is emitted.

"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>, sym_name = "main"}> ({
    ^bb0(%0 : !mod_arith.int<7 : i32>, %1 : !mod_arith.int<7 : i32>):
      %r = "mod_arith.mul"(%0, %1) : (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>
      "func.return"(%r) : (!mod_arith.int<7 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}([[ARG0:%.*]] : !mod_arith.int<7 : i32>, [[ARG1:%.*]] : !mod_arith.int<7 : i32>):
// CHECK-NEXT:   [[C0:%.*]] = "builtin.unrealized_conversion_cast"([[ARG0]]) : (!mod_arith.int<7 : i32>) -> i32
// CHECK-NEXT:   [[E0:%.*]] = "arith.extui"([[C0]]) : (i32) -> i128
// CHECK-NEXT:   [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[ARG1]]) : (!mod_arith.int<7 : i32>) -> i32
// CHECK-NEXT:   [[E1:%.*]] = "arith.extui"([[C1]]) : (i32) -> i128
// CHECK-NEXT:   [[P:%.*]] = "arith.muli"([[E0]], [[E1]]) : (i128, i128) -> i128
// CHECK-NEXT:   [[RATIO:%.*]] = "arith.constant"() <{"value" = 2635249153387078802 : i128}> : () -> i128
// CHECK-NEXT:   [[PR:%.*]] = "arith.muli"([[P]], [[RATIO]]) : (i128, i128) -> i128
// CHECK-NEXT:   [[SHIFT:%.*]] = "arith.constant"() <{"value" = 64 : i128}> : () -> i128
// CHECK-NEXT:   [[S:%.*]] = "arith.shrui"([[PR]], [[SHIFT]]) : (i128, i128) -> i128
// CHECK-NEXT:   [[Q:%.*]] = "arith.constant"() <{"value" = 7 : i128}> : () -> i128
// CHECK-NEXT:   [[SQ:%.*]] = "arith.muli"([[S]], [[Q]]) : (i128, i128) -> i128
// CHECK-NEXT:   [[T:%.*]] = "arith.subi"([[P]], [[SQ]]) : (i128, i128) -> i128
// CHECK-NEXT:   [[GE:%.*]] = "arith.cmpi"([[T]], [[Q]]) <{"predicate" = 9 : i64}> : (i128, i128) -> i1
// CHECK-NEXT:   [[DIFF:%.*]] = "arith.subi"([[T]], [[Q]]) : (i128, i128) -> i128
// CHECK-NEXT:   [[RES:%.*]] = "arith.select"([[GE]], [[DIFF]], [[T]]) : (i1, i128, i128) -> i128
// CHECK-NEXT:   [[TR:%.*]] = "arith.trunci"([[RES]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i128) -> i32
// CHECK-NEXT:   [[OUT:%.*]] = "builtin.unrealized_conversion_cast"([[TR]]) : (i32) -> !mod_arith.int<7 : i32>
// CHECK-NEXT:   "func.return"([[OUT]]) : (!mod_arith.int<7 : i32>) -> ()

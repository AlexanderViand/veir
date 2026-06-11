// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// Round-trip of the MLIR-compatible `#arith.overflow<...>` attribute on the
// `NswNuwProperties` operations of the arith dialect. The default flags
// (`none`) are not printed.

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i32) -> i32, sym_name = "main"}> ({
  ^bb0(%a : i32, %b : i32):
    %addi = "arith.addi"(%a, %b) <{"overflowFlags" = #arith.overflow<none>}> : (i32, i32) -> i32
    %addi_nsw = "arith.addi"(%a, %b) <{"overflowFlags" = #arith.overflow<nsw>}> : (i32, i32) -> i32
    %addi_nuw = "arith.addi"(%a, %b) <{"overflowFlags" = #arith.overflow<nuw>}> : (i32, i32) -> i32
    %addi_nsw_nuw = "arith.addi"(%a, %b) <{"overflowFlags" = #arith.overflow<nsw, nuw>}> : (i32, i32) -> i32
    %trunci = "arith.trunci"(%a) <{"overflowFlags" = #arith.overflow<none>}> : (i32) -> i16
    %trunci_nsw = "arith.trunci"(%a) <{"overflowFlags" = #arith.overflow<nsw>}> : (i32) -> i16
    %trunci_nuw = "arith.trunci"(%a) <{"overflowFlags" = #arith.overflow<nuw>}> : (i32) -> i16
    %trunci_nsw_nuw = "arith.trunci"(%a) <{"overflowFlags" = #arith.overflow<nsw, nuw>}> : (i32) -> i16
    "func.return"(%addi) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      %{{.*}} = "arith.addi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT: %{{.*}} = "arith.addi"(%{{.*}}, %{{.*}}) <{"overflowFlags" = #arith.overflow<nsw>}> : (i32, i32) -> i32
// CHECK-NEXT: %{{.*}} = "arith.addi"(%{{.*}}, %{{.*}}) <{"overflowFlags" = #arith.overflow<nuw>}> : (i32, i32) -> i32
// CHECK-NEXT: %{{.*}} = "arith.addi"(%{{.*}}, %{{.*}}) <{"overflowFlags" = #arith.overflow<nsw, nuw>}> : (i32, i32) -> i32
// CHECK-NEXT: %{{.*}} = "arith.trunci"(%{{.*}}) : (i32) -> i16
// CHECK-NEXT: %{{.*}} = "arith.trunci"(%{{.*}}) <{"overflowFlags" = #arith.overflow<nsw>}> : (i32) -> i16
// CHECK-NEXT: %{{.*}} = "arith.trunci"(%{{.*}}) <{"overflowFlags" = #arith.overflow<nuw>}> : (i32) -> i16
// CHECK-NEXT: %{{.*}} = "arith.trunci"(%{{.*}}) <{"overflowFlags" = #arith.overflow<nsw, nuw>}> : (i32) -> i16

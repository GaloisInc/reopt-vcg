; ModuleID = 'test_fib.bc'
source_filename = "test_fib.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-none-elf"

@digits = internal global [17 x i8] c"0123456789abcdef\00", align 16

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i64 @fib(i64) #0 {
  %2 = alloca i64, align 8
  %3 = alloca i64, align 8
  store i64 %0, i64* %3, align 8
  %4 = load i64, i64* %3, align 8
  %5 = icmp ule i64 %4, 1
  br i1 %5, label %6, label %8

; <label>:6:                                      ; preds = %1
  %7 = load i64, i64* %3, align 8
  store i64 %7, i64* %2, align 8
  br label %16

; <label>:8:                                      ; preds = %1
  %9 = load i64, i64* %3, align 8
  %10 = sub i64 %9, 1
  %11 = call i64 @fib(i64 %10)
  %12 = load i64, i64* %3, align 8
  %13 = sub i64 %12, 2
  %14 = call i64 @fib(i64 %13)
  %15 = add i64 %11, %14
  store i64 %15, i64* %2, align 8
  br label %16

; <label>:16:                                     ; preds = %8, %6
  %17 = load i64, i64* %2, align 8
  ret i64 %17
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @write_hex_number_to_stdout(i64) #0 {
  %2 = alloca i64, align 8
  %3 = alloca i32, align 4
  store i64 %0, i64* %2, align 8
  store i32 15, i32* %3, align 4
  br label %4

; <label>:4:                                      ; preds = %18, %1
  %5 = load i32, i32* %3, align 4
  %6 = icmp sge i32 %5, 0
  br i1 %6, label %7, label %21

; <label>:7:                                      ; preds = %4
  %8 = load i64, i64* %2, align 8
  %9 = load i32, i32* %3, align 4
  %10 = mul nsw i32 %9, 4
  %11 = zext i32 %10 to i64
  %12 = lshr i64 %8, %11
  %13 = and i64 %12, 15
  %14 = getelementptr inbounds [17 x i8], [17 x i8]* @digits, i64 0, i64 %13
  %15 = load i8, i8* %14, align 1
  %16 = sext i8 %15 to i32
  %17 = call i32 @putchar(i32 %16)
  br label %18

; <label>:18:                                     ; preds = %7
  %19 = load i32, i32* %3, align 4
  %20 = add nsw i32 %19, -1
  store i32 %20, i32* %3, align 4
  br label %4

; <label>:21:                                     ; preds = %4
  %22 = call i32 @putchar(i32 10)
  ret void
}

declare dso_local i32 @putchar(i32) #1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i64, align 8
  store i32 0, i32* %1, align 4
  %3 = call i64 @fib(i64 5)
  store i64 %3, i64* %2, align 8
  %4 = load i64, i64* %2, align 8
  call void @write_hex_number_to_stdout(i64 %4)
  %5 = load i64, i64* %2, align 8
  %6 = trunc i64 %5 to i32
  ret i32 %6
}

attributes #0 = { noinline nounwind optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 8.0.0-3~ubuntu18.04.1 (tags/RELEASE_800/final)"}

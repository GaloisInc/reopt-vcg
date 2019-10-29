; ModuleID = 'test_sort.bc'
source_filename = "test_sort.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-none-elf"

@arr = dso_local global [10 x i64] [i64 20307, i64 3714, i64 12422, i64 16382, i64 29230, i64 18967, i64 22962, i64 27145, i64 12275, i64 4617], align 16
@digits = internal global [17 x i8] c"0123456789abcdef\00", align 16

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @partition(i32, i32) #0 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i64, align 8
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca i64, align 8
  store i32 %0, i32* %3, align 4
  store i32 %1, i32* %4, align 4
  %9 = load i32, i32* %3, align 4
  %10 = zext i32 %9 to i64
  %11 = getelementptr inbounds [10 x i64], [10 x i64]* @arr, i64 0, i64 %10
  %12 = load i64, i64* %11, align 8
  store i64 %12, i64* %5, align 8
  %13 = load i32, i32* %3, align 4
  store i32 %13, i32* %6, align 4
  %14 = load i32, i32* %3, align 4
  %15 = add i32 %14, 1
  store i32 %15, i32* %7, align 4
  br label %16

; <label>:16:                                     ; preds = %43, %2
  %17 = load i32, i32* %7, align 4
  %18 = load i32, i32* %4, align 4
  %19 = icmp ule i32 %17, %18
  br i1 %19, label %20, label %46

; <label>:20:                                     ; preds = %16
  %21 = load i32, i32* %7, align 4
  %22 = zext i32 %21 to i64
  %23 = getelementptr inbounds [10 x i64], [10 x i64]* @arr, i64 0, i64 %22
  %24 = load i64, i64* %23, align 8
  store i64 %24, i64* %8, align 8
  %25 = load i64, i64* %8, align 8
  %26 = load i64, i64* %5, align 8
  %27 = icmp ult i64 %25, %26
  br i1 %27, label %28, label %42

; <label>:28:                                     ; preds = %20
  %29 = load i32, i32* %6, align 4
  %30 = add i32 %29, 1
  store i32 %30, i32* %6, align 4
  %31 = load i32, i32* %6, align 4
  %32 = zext i32 %31 to i64
  %33 = getelementptr inbounds [10 x i64], [10 x i64]* @arr, i64 0, i64 %32
  %34 = load i64, i64* %33, align 8
  %35 = load i32, i32* %7, align 4
  %36 = zext i32 %35 to i64
  %37 = getelementptr inbounds [10 x i64], [10 x i64]* @arr, i64 0, i64 %36
  store i64 %34, i64* %37, align 8
  %38 = load i64, i64* %8, align 8
  %39 = load i32, i32* %6, align 4
  %40 = zext i32 %39 to i64
  %41 = getelementptr inbounds [10 x i64], [10 x i64]* @arr, i64 0, i64 %40
  store i64 %38, i64* %41, align 8
  br label %42

; <label>:42:                                     ; preds = %28, %20
  br label %43

; <label>:43:                                     ; preds = %42
  %44 = load i32, i32* %7, align 4
  %45 = add i32 %44, 1
  store i32 %45, i32* %7, align 4
  br label %16

; <label>:46:                                     ; preds = %16
  %47 = load i32, i32* %6, align 4
  %48 = zext i32 %47 to i64
  %49 = getelementptr inbounds [10 x i64], [10 x i64]* @arr, i64 0, i64 %48
  %50 = load i64, i64* %49, align 8
  %51 = load i32, i32* %3, align 4
  %52 = zext i32 %51 to i64
  %53 = getelementptr inbounds [10 x i64], [10 x i64]* @arr, i64 0, i64 %52
  store i64 %50, i64* %53, align 8
  %54 = load i64, i64* %5, align 8
  %55 = load i32, i32* %6, align 4
  %56 = zext i32 %55 to i64
  %57 = getelementptr inbounds [10 x i64], [10 x i64]* @arr, i64 0, i64 %56
  store i64 %54, i64* %57, align 8
  %58 = load i32, i32* %6, align 4
  ret i32 %58
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @quicksort(i32, i32) #0 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  store i32 %0, i32* %3, align 4
  store i32 %1, i32* %4, align 4
  %6 = load i32, i32* %3, align 4
  %7 = load i32, i32* %4, align 4
  %8 = icmp ult i32 %6, %7
  br i1 %8, label %9, label %19

; <label>:9:                                      ; preds = %2
  %10 = load i32, i32* %3, align 4
  %11 = load i32, i32* %4, align 4
  %12 = call i32 @partition(i32 %10, i32 %11)
  store i32 %12, i32* %5, align 4
  %13 = load i32, i32* %3, align 4
  %14 = load i32, i32* %5, align 4
  %15 = sub i32 %14, 1
  call void @quicksort(i32 %13, i32 %15)
  %16 = load i32, i32* %5, align 4
  %17 = add i32 %16, 1
  %18 = load i32, i32* %4, align 4
  call void @quicksort(i32 %17, i32 %18)
  br label %19

; <label>:19:                                     ; preds = %9, %2
  ret void
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
define dso_local void @run_test() #0 {
  call void @quicksort(i32 0, i32 9)
  ret void
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 0, i32* %1, align 4
  call void @run_test()
  store i32 0, i32* %2, align 4
  br label %3

; <label>:3:                                      ; preds = %11, %0
  %4 = load i32, i32* %2, align 4
  %5 = icmp ult i32 %4, 10
  br i1 %5, label %6, label %14

; <label>:6:                                      ; preds = %3
  %7 = load i32, i32* %2, align 4
  %8 = zext i32 %7 to i64
  %9 = getelementptr inbounds [10 x i64], [10 x i64]* @arr, i64 0, i64 %8
  %10 = load i64, i64* %9, align 8
  call void @write_hex_number_to_stdout(i64 %10)
  br label %11

; <label>:11:                                     ; preds = %6
  %12 = load i32, i32* %2, align 4
  %13 = add i32 %12, 1
  store i32 %13, i32* %2, align 4
  br label %3

; <label>:14:                                     ; preds = %3
  ret i32 0
}

attributes #0 = { noinline nounwind optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 8.0.0-3~ubuntu18.04.1 (tags/RELEASE_800/final)"}

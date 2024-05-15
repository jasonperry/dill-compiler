; ModuleID = 'dill-stdio.c'
source_filename = "dill-stdio.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.byte_array = type { i64, ptr }
%struct.int_array = type { i64, ptr }
%struct.nullstr = type { i8, ptr }

@.str = private unnamed_addr constant [25 x i8] c"Runtime error (openFile)\00", align 1
@stderr = external global ptr, align 8
@.str.1 = private unnamed_addr constant [67 x i8] c"Runtime Error(readFile): tried to read %lu bytes, got %lu instead\0A\00", align 1
@.str.2 = private unnamed_addr constant [4 x i8] c"%d\0A\00", align 1
@.str.3 = private unnamed_addr constant [4 x i8] c"%f\0A\00", align 1
@stdout = external global ptr, align 8
@stdin = external global ptr, align 8

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local ptr @openFile(ptr noundef %0, ptr noundef %1) #0 {
  %3 = alloca ptr, align 8
  %4 = alloca ptr, align 8
  %5 = alloca ptr, align 8
  store ptr %0, ptr %3, align 8
  store ptr %1, ptr %4, align 8
  %6 = load ptr, ptr %3, align 8
  %7 = load ptr, ptr %4, align 8
  %8 = call noalias ptr @fopen(ptr noundef %6, ptr noundef %7)
  store ptr %8, ptr %5, align 8
  %9 = load ptr, ptr %5, align 8
  %10 = icmp eq ptr %9, null
  br i1 %10, label %11, label %12

11:                                               ; preds = %2
  call void @perror(ptr noundef @.str) #5
  call void @exit(i32 noundef 1) #6
  unreachable

12:                                               ; preds = %2
  %13 = load ptr, ptr %5, align 8
  ret ptr %13
}

declare noalias ptr @fopen(ptr noundef, ptr noundef) #1

; Function Attrs: cold
declare void @perror(ptr noundef) #2

; Function Attrs: noreturn nounwind
declare void @exit(i32 noundef) #3

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local void @closeFile(ptr noundef %0) #0 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
  %3 = load ptr, ptr %2, align 8
  %4 = load ptr, ptr %3, align 8
  %5 = call i32 @fclose(ptr noundef %4)
  ret void
}

declare i32 @fclose(ptr noundef) #1

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local { i64, ptr } @readFile(ptr noundef %0) #0 {
  %2 = alloca %struct.byte_array, align 8
  %3 = alloca ptr, align 8
  %4 = alloca ptr, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store ptr %0, ptr %3, align 8
  %7 = load ptr, ptr %3, align 8
  %8 = load ptr, ptr %7, align 8
  store ptr %8, ptr %4, align 8
  %9 = load ptr, ptr %4, align 8
  %10 = call i32 @fseek(ptr noundef %9, i64 noundef 0, i32 noundef 2)
  %11 = load ptr, ptr %4, align 8
  %12 = call i64 @ftell(ptr noundef %11)
  store i64 %12, ptr %5, align 8
  %13 = load ptr, ptr %4, align 8
  %14 = call i32 @fseek(ptr noundef %13, i64 noundef 0, i32 noundef 0)
  %15 = load i64, ptr %5, align 8
  %16 = getelementptr inbounds %struct.byte_array, ptr %2, i32 0, i32 0
  store i64 %15, ptr %16, align 8
  %17 = load i64, ptr %5, align 8
  %18 = call noalias ptr @GC_malloc(i64 noundef %17) #7
  %19 = getelementptr inbounds %struct.byte_array, ptr %2, i32 0, i32 1
  store ptr %18, ptr %19, align 8
  %20 = getelementptr inbounds %struct.byte_array, ptr %2, i32 0, i32 1
  %21 = load ptr, ptr %20, align 8
  %22 = load i64, ptr %5, align 8
  %23 = load ptr, ptr %4, align 8
  %24 = call i64 @fread(ptr noundef %21, i64 noundef 1, i64 noundef %22, ptr noundef %23)
  store i64 %24, ptr %6, align 8
  %25 = load i64, ptr %6, align 8
  %26 = load i64, ptr %5, align 8
  %27 = icmp ne i64 %25, %26
  br i1 %27, label %28, label %33

28:                                               ; preds = %1
  %29 = load ptr, ptr @stderr, align 8
  %30 = load i64, ptr %5, align 8
  %31 = load i64, ptr %6, align 8
  %32 = call i32 (ptr, ptr, ...) @fprintf(ptr noundef %29, ptr noundef @.str.1, i64 noundef %30, i64 noundef %31)
  call void @exit(i32 noundef 1) #6
  unreachable

33:                                               ; preds = %1
  %34 = load { i64, ptr }, ptr %2, align 8
  ret { i64, ptr } %34
}

declare i32 @fseek(ptr noundef, i64 noundef, i32 noundef) #1

declare i64 @ftell(ptr noundef) #1

; Function Attrs: allocsize(0)
declare noalias ptr @GC_malloc(i64 noundef) #4

declare i64 @fread(ptr noundef, i64 noundef, i64 noundef, ptr noundef) #1

declare i32 @fprintf(ptr noundef, ptr noundef, ...) #1

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local { i64, ptr } @initIntArray(i64 noundef %0, i32 noundef %1) #0 {
  %3 = alloca %struct.int_array, align 8
  %4 = alloca i64, align 8
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  store i64 %0, ptr %4, align 8
  store i32 %1, ptr %5, align 4
  %7 = load i64, ptr %4, align 8
  %8 = getelementptr inbounds %struct.int_array, ptr %3, i32 0, i32 0
  store i64 %7, ptr %8, align 8
  %9 = load i64, ptr %4, align 8
  %10 = mul i64 %9, 4
  %11 = call noalias ptr @GC_malloc(i64 noundef %10) #7
  %12 = getelementptr inbounds %struct.int_array, ptr %3, i32 0, i32 1
  store ptr %11, ptr %12, align 8
  store i32 0, ptr %6, align 4
  br label %13

13:                                               ; preds = %25, %2
  %14 = load i32, ptr %6, align 4
  %15 = sext i32 %14 to i64
  %16 = load i64, ptr %4, align 8
  %17 = icmp slt i64 %15, %16
  br i1 %17, label %18, label %28

18:                                               ; preds = %13
  %19 = load i32, ptr %5, align 4
  %20 = getelementptr inbounds %struct.int_array, ptr %3, i32 0, i32 1
  %21 = load ptr, ptr %20, align 8
  %22 = load i32, ptr %6, align 4
  %23 = sext i32 %22 to i64
  %24 = getelementptr inbounds i32, ptr %21, i64 %23
  store i32 %19, ptr %24, align 4
  br label %25

25:                                               ; preds = %18
  %26 = load i32, ptr %6, align 4
  %27 = add nsw i32 %26, 1
  store i32 %27, ptr %6, align 4
  br label %13, !llvm.loop !6

28:                                               ; preds = %13
  %29 = load { i64, ptr }, ptr %3, align 8
  ret { i64, ptr } %29
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local void @printInt(i32 noundef %0) #0 {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
  %3 = load i32, ptr %2, align 4
  %4 = call i32 (ptr, ...) @printf(ptr noundef @.str.2, i32 noundef %3)
  ret void
}

declare i32 @printf(ptr noundef, ...) #1

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local void @printFloat(double noundef %0) #0 {
  %2 = alloca double, align 8
  store double %0, ptr %2, align 8
  %3 = load double, ptr %2, align 8
  %4 = call i32 (ptr, ...) @printf(ptr noundef @.str.3, double noundef %3)
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local void @printBytes(i64 %0, ptr %1) #0 {
  %3 = alloca %struct.byte_array, align 8
  %4 = getelementptr inbounds { i64, ptr }, ptr %3, i32 0, i32 0
  store i64 %0, ptr %4, align 8
  %5 = getelementptr inbounds { i64, ptr }, ptr %3, i32 0, i32 1
  store ptr %1, ptr %5, align 8
  %6 = getelementptr inbounds %struct.byte_array, ptr %3, i32 0, i32 1
  %7 = load ptr, ptr %6, align 8
  %8 = getelementptr inbounds %struct.byte_array, ptr %3, i32 0, i32 0
  %9 = load i64, ptr %8, align 8
  %10 = load ptr, ptr @stdout, align 8
  %11 = call i64 @fwrite(ptr noundef %7, i64 noundef 1, i64 noundef %9, ptr noundef %10)
  ret void
}

declare i64 @fwrite(ptr noundef, i64 noundef, i64 noundef, ptr noundef) #1

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local void @printString(ptr noundef %0) #0 {
  %2 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
  %3 = load ptr, ptr %2, align 8
  %4 = call i32 @puts(ptr noundef %3)
  ret void
}

declare i32 @puts(ptr noundef) #1

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local { i8, ptr } @getLineStdin() #0 {
  %1 = alloca %struct.nullstr, align 8
  %2 = alloca ptr, align 8
  %3 = alloca i64, align 8
  %4 = alloca i64, align 8
  store i64 0, ptr %3, align 8
  %5 = getelementptr inbounds %struct.nullstr, ptr %1, i32 0, i32 1
  store ptr null, ptr %5, align 8
  %6 = getelementptr inbounds %struct.nullstr, ptr %1, i32 0, i32 1
  %7 = load ptr, ptr @stdin, align 8
  %8 = call i64 @getline(ptr noundef %6, ptr noundef %3, ptr noundef %7)
  store i64 %8, ptr %4, align 8
  %9 = load i64, ptr %4, align 8
  %10 = icmp eq i64 %9, -1
  br i1 %10, label %11, label %13

11:                                               ; preds = %0
  %12 = getelementptr inbounds %struct.nullstr, ptr %1, i32 0, i32 0
  store i8 0, ptr %12, align 8
  br label %15

13:                                               ; preds = %0
  %14 = getelementptr inbounds %struct.nullstr, ptr %1, i32 0, i32 0
  store i8 1, ptr %14, align 8
  br label %15

15:                                               ; preds = %13, %11
  %16 = load { i8, ptr }, ptr %1, align 8
  ret { i8, ptr } %16
}

declare i64 @getline(ptr noundef, ptr noundef, ptr noundef) #1

attributes #0 = { noinline nounwind optnone sspstrong uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { cold "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { allocsize(0) "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #5 = { cold }
attributes #6 = { noreturn nounwind }
attributes #7 = { allocsize(0) }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.ident = !{!5}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 2}
!5 = !{!"clang version 17.0.6"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}

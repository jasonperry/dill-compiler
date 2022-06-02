; ModuleID = 'dill-stdio.c'
source_filename = "dill-stdio.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct._IO_FILE = type { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, %struct._IO_marker*, %struct._IO_FILE*, i32, i32, i64, i16, i8, [1 x i8], i8*, i64, %struct._IO_codecvt*, %struct._IO_wide_data*, %struct._IO_FILE*, i8*, i64, i32, [20 x i8] }
%struct._IO_marker = type opaque
%struct._IO_codecvt = type opaque
%struct._IO_wide_data = type opaque
%struct.byte_array = type { i64, i8* }
%struct.int_array = type { i64, i64* }
%struct.nullstr = type { i8, i8* }

@.str = private unnamed_addr constant [25 x i8] c"Runtime error (openFile)\00", align 1
@stderr = external global %struct._IO_FILE*, align 8
@.str.1 = private unnamed_addr constant [67 x i8] c"Runtime Error(readFile): tried to read %lu bytes, got %lu instead\0A\00", align 1
@.str.2 = private unnamed_addr constant [5 x i8] c"%ld\0A\00", align 1
@.str.3 = private unnamed_addr constant [4 x i8] c"%f\0A\00", align 1
@stdout = external global %struct._IO_FILE*, align 8
@stdin = external global %struct._IO_FILE*, align 8

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local %struct._IO_FILE* @"stdio::openFile"(i8* %0, i8* %1) #0 {
  %3 = alloca i8*, align 8
  %4 = alloca i8*, align 8
  %5 = alloca %struct._IO_FILE*, align 8
  store i8* %0, i8** %3, align 8
  store i8* %1, i8** %4, align 8
  %6 = load i8*, i8** %3, align 8
  %7 = load i8*, i8** %4, align 8
  %8 = call noalias %struct._IO_FILE* @fopen(i8* %6, i8* %7)
  store %struct._IO_FILE* %8, %struct._IO_FILE** %5, align 8
  %9 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 8
  %10 = icmp eq %struct._IO_FILE* %9, null
  br i1 %10, label %11, label %12

11:                                               ; preds = %2
  call void @perror(i8* getelementptr inbounds ([25 x i8], [25 x i8]* @.str, i64 0, i64 0))
  call void @exit(i32 1) #4
  unreachable

12:                                               ; preds = %2
  %13 = load %struct._IO_FILE*, %struct._IO_FILE** %5, align 8
  ret %struct._IO_FILE* %13
}

declare noalias %struct._IO_FILE* @fopen(i8*, i8*) #1

declare void @perror(i8*) #1

; Function Attrs: noreturn nounwind
declare void @exit(i32) #2

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local void @"stdio::closeFile"(%struct._IO_FILE** %0) #0 {
  %2 = alloca %struct._IO_FILE**, align 8
  store %struct._IO_FILE** %0, %struct._IO_FILE*** %2, align 8
  %3 = load %struct._IO_FILE**, %struct._IO_FILE*** %2, align 8
  %4 = load %struct._IO_FILE*, %struct._IO_FILE** %3, align 8
  %5 = call i32 @fclose(%struct._IO_FILE* %4)
  ret void
}

declare i32 @fclose(%struct._IO_FILE*) #1

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local { i64, i8* } @"stdio::readFile"(%struct._IO_FILE** %0) #0 {
  %2 = alloca %struct.byte_array, align 8
  %3 = alloca %struct._IO_FILE**, align 8
  %4 = alloca %struct._IO_FILE*, align 8
  %5 = alloca i64, align 8
  %6 = alloca i64, align 8
  store %struct._IO_FILE** %0, %struct._IO_FILE*** %3, align 8
  %7 = load %struct._IO_FILE**, %struct._IO_FILE*** %3, align 8
  %8 = load %struct._IO_FILE*, %struct._IO_FILE** %7, align 8
  store %struct._IO_FILE* %8, %struct._IO_FILE** %4, align 8
  %9 = load %struct._IO_FILE*, %struct._IO_FILE** %4, align 8
  %10 = call i32 @fseek(%struct._IO_FILE* %9, i64 0, i32 2)
  %11 = load %struct._IO_FILE*, %struct._IO_FILE** %4, align 8
  %12 = call i64 @ftell(%struct._IO_FILE* %11)
  store i64 %12, i64* %5, align 8
  %13 = load %struct._IO_FILE*, %struct._IO_FILE** %4, align 8
  %14 = call i32 @fseek(%struct._IO_FILE* %13, i64 0, i32 0)
  %15 = load i64, i64* %5, align 8
  %16 = getelementptr inbounds %struct.byte_array, %struct.byte_array* %2, i32 0, i32 0
  store i64 %15, i64* %16, align 8
  %17 = load i64, i64* %5, align 8
  %18 = call noalias i8* @GC_malloc(i64 %17) #5
  %19 = getelementptr inbounds %struct.byte_array, %struct.byte_array* %2, i32 0, i32 1
  store i8* %18, i8** %19, align 8
  %20 = getelementptr inbounds %struct.byte_array, %struct.byte_array* %2, i32 0, i32 1
  %21 = load i8*, i8** %20, align 8
  %22 = load i64, i64* %5, align 8
  %23 = load %struct._IO_FILE*, %struct._IO_FILE** %4, align 8
  %24 = call i64 @fread(i8* %21, i64 1, i64 %22, %struct._IO_FILE* %23)
  store i64 %24, i64* %6, align 8
  %25 = load i64, i64* %6, align 8
  %26 = load i64, i64* %5, align 8
  %27 = icmp ne i64 %25, %26
  br i1 %27, label %28, label %33

28:                                               ; preds = %1
  %29 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 8
  %30 = load i64, i64* %5, align 8
  %31 = load i64, i64* %6, align 8
  %32 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %29, i8* getelementptr inbounds ([67 x i8], [67 x i8]* @.str.1, i64 0, i64 0), i64 %30, i64 %31)
  call void @exit(i32 1) #4
  unreachable

33:                                               ; preds = %1
  %34 = bitcast %struct.byte_array* %2 to { i64, i8* }*
  %35 = load { i64, i8* }, { i64, i8* }* %34, align 8
  ret { i64, i8* } %35
}

declare i32 @fseek(%struct._IO_FILE*, i64, i32) #1

declare i64 @ftell(%struct._IO_FILE*) #1

; Function Attrs: allocsize(0)
declare noalias i8* @GC_malloc(i64) #3

declare i64 @fread(i8*, i64, i64, %struct._IO_FILE*) #1

declare i32 @fprintf(%struct._IO_FILE*, i8*, ...) #1

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local { i64, i64* } @"stdio::initIntArray"(i64 %0, i64 %1) #0 {
  %3 = alloca %struct.int_array, align 8
  %4 = alloca i64, align 8
  %5 = alloca i64, align 8
  %6 = alloca i32, align 4
  store i64 %0, i64* %4, align 8
  store i64 %1, i64* %5, align 8
  %7 = load i64, i64* %4, align 8
  %8 = getelementptr inbounds %struct.int_array, %struct.int_array* %3, i32 0, i32 0
  store i64 %7, i64* %8, align 8
  %9 = load i64, i64* %4, align 8
  %10 = mul i64 %9, 8
  %11 = call noalias i8* @GC_malloc(i64 %10) #5
  %12 = bitcast i8* %11 to i64*
  %13 = getelementptr inbounds %struct.int_array, %struct.int_array* %3, i32 0, i32 1
  store i64* %12, i64** %13, align 8
  store i32 0, i32* %6, align 4
  br label %14

14:                                               ; preds = %26, %2
  %15 = load i32, i32* %6, align 4
  %16 = sext i32 %15 to i64
  %17 = load i64, i64* %4, align 8
  %18 = icmp slt i64 %16, %17
  br i1 %18, label %19, label %29

19:                                               ; preds = %14
  %20 = load i64, i64* %5, align 8
  %21 = getelementptr inbounds %struct.int_array, %struct.int_array* %3, i32 0, i32 1
  %22 = load i64*, i64** %21, align 8
  %23 = load i32, i32* %6, align 4
  %24 = sext i32 %23 to i64
  %25 = getelementptr inbounds i64, i64* %22, i64 %24
  store i64 %20, i64* %25, align 8
  br label %26

26:                                               ; preds = %19
  %27 = load i32, i32* %6, align 4
  %28 = add nsw i32 %27, 1
  store i32 %28, i32* %6, align 4
  br label %14, !llvm.loop !6

29:                                               ; preds = %14
  %30 = bitcast %struct.int_array* %3 to { i64, i64* }*
  %31 = load { i64, i64* }, { i64, i64* }* %30, align 8
  ret { i64, i64* } %31
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local void @"stdio::printInt"(i64 %0) #0 {
  %2 = alloca i64, align 8
  store i64 %0, i64* %2, align 8
  %3 = load i64, i64* %2, align 8
  %4 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @.str.2, i64 0, i64 0), i64 %3)
  ret void
}

declare i32 @printf(i8*, ...) #1

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local void @"stdio::printFloat"(double %0) #0 {
  %2 = alloca double, align 8
  store double %0, double* %2, align 8
  %3 = load double, double* %2, align 8
  %4 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.3, i64 0, i64 0), double %3)
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local void @"stdio::printBytes"(i64 %0, i8* %1) #0 {
  %3 = alloca %struct.byte_array, align 8
  %4 = bitcast %struct.byte_array* %3 to { i64, i8* }*
  %5 = getelementptr inbounds { i64, i8* }, { i64, i8* }* %4, i32 0, i32 0
  store i64 %0, i64* %5, align 8
  %6 = getelementptr inbounds { i64, i8* }, { i64, i8* }* %4, i32 0, i32 1
  store i8* %1, i8** %6, align 8
  %7 = getelementptr inbounds %struct.byte_array, %struct.byte_array* %3, i32 0, i32 1
  %8 = load i8*, i8** %7, align 8
  %9 = getelementptr inbounds %struct.byte_array, %struct.byte_array* %3, i32 0, i32 0
  %10 = load i64, i64* %9, align 8
  %11 = load %struct._IO_FILE*, %struct._IO_FILE** @stdout, align 8
  %12 = call i64 @fwrite(i8* %8, i64 1, i64 %10, %struct._IO_FILE* %11)
  ret void
}

declare i64 @fwrite(i8*, i64, i64, %struct._IO_FILE*) #1

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local void @"stdio::printString"(i8* %0) #0 {
  %2 = alloca i8*, align 8
  store i8* %0, i8** %2, align 8
  %3 = load i8*, i8** %2, align 8
  %4 = call i32 @puts(i8* %3)
  ret void
}

declare i32 @puts(i8*) #1

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local { i8, i8* } @"stdio::getLineStdin"() #0 {
  %1 = alloca %struct.nullstr, align 8
  %2 = alloca i8*, align 8
  %3 = alloca i64, align 8
  %4 = alloca i64, align 8
  store i64 0, i64* %3, align 8
  %5 = getelementptr inbounds %struct.nullstr, %struct.nullstr* %1, i32 0, i32 1
  store i8* null, i8** %5, align 8
  %6 = getelementptr inbounds %struct.nullstr, %struct.nullstr* %1, i32 0, i32 1
  %7 = load %struct._IO_FILE*, %struct._IO_FILE** @stdin, align 8
  %8 = call i64 @getline(i8** %6, i64* %3, %struct._IO_FILE* %7)
  store i64 %8, i64* %4, align 8
  %9 = load i64, i64* %4, align 8
  %10 = icmp eq i64 %9, -1
  br i1 %10, label %11, label %13

11:                                               ; preds = %0
  %12 = getelementptr inbounds %struct.nullstr, %struct.nullstr* %1, i32 0, i32 0
  store i8 0, i8* %12, align 8
  br label %15

13:                                               ; preds = %0
  %14 = getelementptr inbounds %struct.nullstr, %struct.nullstr* %1, i32 0, i32 0
  store i8 1, i8* %14, align 8
  br label %15

15:                                               ; preds = %13, %11
  %16 = bitcast %struct.nullstr* %1 to { i8, i8* }*
  %17 = load { i8, i8* }, { i8, i8* }* %16, align 8
  ret { i8, i8* } %17
}

declare i64 @getline(i8**, i64*, %struct._IO_FILE*) #1

attributes #0 = { noinline nounwind optnone sspstrong uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { allocsize(0) "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { noreturn nounwind }
attributes #5 = { allocsize(0) }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.ident = !{!5}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 1}
!4 = !{i32 7, !"frame-pointer", i32 2}
!5 = !{!"clang version 13.0.1"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}

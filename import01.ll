; ModuleID = 'dillout.ll'
source_filename = "dillout.ll"
target triple = "x86_64-pc-linux-gnu"

declare i32 @Collatz.collatz(i32)

declare void @printFloat(double)

declare void @printInt(i32)

define void @main() {
entry:
  %calltmp = call i32 @Collatz.collatz(i32 6171)
  call void @printInt(i32 %calltmp)
  ret void
}

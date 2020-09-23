; ModuleID = 'dillout.ll'
source_filename = "dillout.ll"
target triple = "x86_64-pc-linux-gnu"

declare void @printFloat(double)

declare void @printInt(i32)

define i32 @triple(i32 %0) {
entry:
  %y = alloca i32
  %x = alloca i32
  store i32 %0, i32* %x
  store i32 3, i32* %y
  %x1 = load i32, i32* %x
  %y2 = load i32, i32* %y
  %imultemp = mul i32 %x1, %y2
  ret i32 %imultemp
}

define void @main() {
entry:
  %calltmp = call i32 @triple(i32 14)
  call void @printInt(i32 %calltmp)
  ret void
}

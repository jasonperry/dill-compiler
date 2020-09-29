; ModuleID = 'dillout.ll'
source_filename = "dillout.ll"
target triple = "x86_64-pc-linux-gnu"

declare void @printFloat(double)

declare void @printInt(i32)

define void @main() {
entry:
  %y = alloca i1
  %x = alloca i32
  store i32 100, i32* %x
  store i1 false, i1* %y
  %x1 = load i32, i32* %x
  %igttemp = icmp sgt i32 %x1, 30
  br i1 %igttemp, label %then, label %else

then:                                             ; preds = %entry
  store i1 true, i1* %y
  br label %ifcont

else:                                             ; preds = %entry
  br label %ifcont

ifcont:                                           ; preds = %else, %then
  %x2 = load i32, i32* %x
  %ilttemp = icmp slt i32 %x2, 50
  %y3 = load i1, i1* %y
  %bandtemp = and i1 %ilttemp, %y3
  br i1 %bandtemp, label %then4, label %elsifcond

then4:                                            ; preds = %ifcont
  %y5 = load i1, i1* %y
  %boolnottemp = xor i1 %y5, true
  store i1 %boolnottemp, i1* %y
  %x6 = load i32, i32* %x
  %iaddtemp = add i32 %x6, 2
  store i32 %iaddtemp, i32* %x
  br label %ifcont13

elsifcond:                                        ; preds = %ifcont
  %x7 = load i32, i32* %x
  %ieqtemp = icmp eq i32 %x7, 2
  %boolnottemp8 = xor i1 %ieqtemp, true
  br i1 %boolnottemp8, label %elsifthen, label %else12

elsifthen:                                        ; preds = %elsifcond
  %x9 = load i32, i32* %x
  %iaddtemp10 = add i32 %x9, 3
  store i32 %iaddtemp10, i32* %x
  %x11 = load i32, i32* %x
  %modtemp = srem i32 %x11, 23
  store i32 %modtemp, i32* %x
  br label %ifcont13

else12:                                           ; preds = %elsifcond
  br label %ifcont13

ifcont13:                                         ; preds = %else12, %elsifthen, %then4
  %x14 = load i32, i32* %x
  call void @printInt(i32 %x14)
  ret void
}

(* autogenerated from semantics *)
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.

(* comparisons.go *)

Definition testCompareAll: val :=
  rec: "testCompareAll" <> :=
    let: "ok" := ref #true in
    let: "nok" := ref #false in
    "ok" <-[boolT] ![boolT] "ok" && #1 < #2;;
    "nok" <-[boolT] ![boolT] "ok" && #2 < #1;;
    "ok" <-[boolT] ![boolT] "ok" && #1 ≤ #2;;
    "ok" <-[boolT] ![boolT] "ok" && #2 ≤ #2;;
    "nok" <-[boolT] ![boolT] "ok" && #2 ≤ #1;;
    (if: ![boolT] "nok"
    then #false
    else ![boolT] "ok").
Theorem testCompareAll_t: ⊢ testCompareAll : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testCompareAll_t : types.

Definition testCompareGT: val :=
  rec: "testCompareGT" <> :=
    let: "x" := ref #4 in
    let: "y" := ref #5 in
    let: "ok" := ref #true in
    "ok" <-[boolT] ![boolT] "ok" && ![uint64T] "y" > #4;;
    "ok" <-[boolT] ![boolT] "ok" && ![uint64T] "y" > ![uint64T] "x";;
    ![boolT] "ok".
Theorem testCompareGT_t: ⊢ testCompareGT : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testCompareGT_t : types.

Definition testCompareGE: val :=
  rec: "testCompareGE" <> :=
    let: "x" := ref #4 in
    let: "y" := ref #5 in
    let: "ok" := ref #true in
    "ok" <-[boolT] ![boolT] "ok" && ![uint64T] "y" ≥ #4;;
    "ok" <-[boolT] ![boolT] "ok" && ![uint64T] "y" ≥ #5;;
    "ok" <-[boolT] ![boolT] "ok" && ![uint64T] "y" ≥ ![uint64T] "x";;
    (if: ![uint64T] "y" > #5
    then #false
    else ![boolT] "ok").
Theorem testCompareGE_t: ⊢ testCompareGE : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testCompareGE_t : types.

Definition testCompareLT: val :=
  rec: "testCompareLT" <> :=
    let: "x" := ref #4 in
    let: "y" := ref #5 in
    let: "ok" := ref #true in
    "ok" <-[boolT] ![boolT] "ok" && ![uint64T] "y" < #6;;
    "ok" <-[boolT] ![boolT] "ok" && ![uint64T] "x" < ![uint64T] "y";;
    ![boolT] "ok".
Theorem testCompareLT_t: ⊢ testCompareLT : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testCompareLT_t : types.

Definition testCompareLE: val :=
  rec: "testCompareLE" <> :=
    let: "x" := ref #4 in
    let: "y" := ref #5 in
    let: "ok" := ref #true in
    "ok" <-[boolT] ![boolT] "ok" && ![uint64T] "y" ≤ #6;;
    "ok" <-[boolT] ![boolT] "ok" && ![uint64T] "y" ≤ #5;;
    "ok" <-[boolT] ![boolT] "ok" && ![uint64T] "x" ≤ ![uint64T] "y";;
    (if: ![uint64T] "y" < #5
    then #false
    else ![boolT] "ok").
Theorem testCompareLE_t: ⊢ testCompareLE : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testCompareLE_t : types.

(* conversions.go *)

Definition literalCast: val :=
  rec: "literalCast" <> :=
    let: "x" := #2 in
    "x" + #2.
Theorem literalCast_t: ⊢ literalCast : (unitT -> uint64T).
Proof. typecheck. Qed.
Hint Resolve literalCast_t : types.

Definition stringToByteSlice: val :=
  rec: "stringToByteSlice" "s" :=
    let: "p" := Data.stringToBytes "s" in
    "p".
Theorem stringToByteSlice_t: ⊢ stringToByteSlice : (stringT -> slice.T byteT).
Proof. typecheck. Qed.
Hint Resolve stringToByteSlice_t : types.

Definition byteSliceToString: val :=
  rec: "byteSliceToString" "p" :=
    Data.bytesToString "p".
Theorem byteSliceToString_t: ⊢ byteSliceToString : (slice.T byteT -> stringT).
Proof. typecheck. Qed.
Hint Resolve byteSliceToString_t : types.

(* tests *)
Definition testByteSliceToString: val :=
  rec: "testByteSliceToString" <> :=
    let: "x" := NewSlice byteT #3 in
    SliceSet byteT "x" #0 (#(U8 65));;
    SliceSet byteT "x" #1 (#(U8 66));;
    SliceSet byteT "x" #2 (#(U8 67));;
    (byteSliceToString "x" = #(str"ABC")).
Theorem testByteSliceToString_t: ⊢ testByteSliceToString : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testByteSliceToString_t : types.

(* copy.go *)

Definition failing_testCopySimple: val :=
  rec: "failing_testCopySimple" <> :=
    let: "x" := NewSlice byteT #10 in
    SliceSet byteT "x" #3 (#(U8 1));;
    let: "y" := NewSlice byteT #10 in
    SliceCopy byteT "y" "x";;
    (SliceGet byteT "y" #3 = #(U8 1)).
Theorem failing_testCopySimple_t: ⊢ failing_testCopySimple : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve failing_testCopySimple_t : types.

Definition failing_testCopyDifferentLengths: val :=
  rec: "failing_testCopyDifferentLengths" <> :=
    let: "x" := NewSlice byteT #15 in
    SliceSet byteT "x" #3 (#(U8 1));;
    SliceSet byteT "x" #12 (#(U8 2));;
    let: "y" := NewSlice byteT #10 in
    let: "n" := SliceCopy byteT "y" "x" in
    ("n" = #10) && (SliceGet byteT "y" #3 = #(U8 1)).
Theorem failing_testCopyDifferentLengths_t: ⊢ failing_testCopyDifferentLengths : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve failing_testCopyDifferentLengths_t : types.

(* encoding.go *)

(* helpers *)
Module Enc.
  Definition S := struct.decl [
    "p" :: slice.T byteT
  ].
End Enc.

Definition Enc__consume: val :=
  rec: "Enc__consume" "e" "n" :=
    let: "b" := SliceTake (struct.loadF Enc.S "p" "e") "n" in
    struct.storeF Enc.S "p" "e" (SliceSkip byteT (struct.loadF Enc.S "p" "e") "n");;
    "b".
Theorem Enc__consume_t: ⊢ Enc__consume : (struct.ptrT Enc.S -> uint64T -> slice.T byteT).
Proof. typecheck. Qed.
Hint Resolve Enc__consume_t : types.

Module Dec.
  Definition S := struct.decl [
    "p" :: slice.T byteT
  ].
End Dec.

Definition Dec__consume: val :=
  rec: "Dec__consume" "d" "n" :=
    let: "b" := SliceTake (struct.loadF Dec.S "p" "d") "n" in
    struct.storeF Dec.S "p" "d" (SliceSkip byteT (struct.loadF Dec.S "p" "d") "n");;
    "b".
Theorem Dec__consume_t: ⊢ Dec__consume : (struct.ptrT Dec.S -> uint64T -> slice.T byteT).
Proof. typecheck. Qed.
Hint Resolve Dec__consume_t : types.

Definition roundtripEncDec32: val :=
  rec: "roundtripEncDec32" "x" :=
    let: "r" := NewSlice byteT #4 in
    let: "e" := struct.new Enc.S [
      "p" ::= "r"
    ] in
    let: "d" := struct.new Dec.S [
      "p" ::= "r"
    ] in
    UInt32Put (Enc__consume "e" #4) "x";;
    UInt32Get (Dec__consume "d" #4).
Theorem roundtripEncDec32_t: ⊢ roundtripEncDec32 : (uint32T -> uint32T).
Proof. typecheck. Qed.
Hint Resolve roundtripEncDec32_t : types.

Definition roundtripEncDec64: val :=
  rec: "roundtripEncDec64" "x" :=
    let: "r" := NewSlice byteT #8 in
    let: "e" := struct.new Enc.S [
      "p" ::= "r"
    ] in
    let: "d" := struct.new Dec.S [
      "p" ::= "r"
    ] in
    UInt64Put (Enc__consume "e" #8) "x";;
    UInt64Get (Dec__consume "d" #8).
Theorem roundtripEncDec64_t: ⊢ roundtripEncDec64 : (uint64T -> uint64T).
Proof. typecheck. Qed.
Hint Resolve roundtripEncDec64_t : types.

(* tests *)
Definition testEncDec32Simple: val :=
  rec: "testEncDec32Simple" <> :=
    let: "ok" := ref #true in
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec32 (#(U32 0)) = #(U32 0));;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec32 (#(U32 1)) = #(U32 1));;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec32 (#(U32 1231234)) = #(U32 1231234));;
    ![boolT] "ok".
Theorem testEncDec32Simple_t: ⊢ testEncDec32Simple : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testEncDec32Simple_t : types.

Definition failing_testEncDec32: val :=
  rec: "failing_testEncDec32" <> :=
    let: "ok" := ref #true in
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec32 (#(U32 3434807466)) = #(U32 3434807466));;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec32 (#1 ≪ #20) = #1 ≪ #20);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec32 (#1 ≪ #18) = #1 ≪ #18);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec32 (#1 ≪ #10) = #1 ≪ #10);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec32 (#1 ≪ #0) = #1 ≪ #0);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec32 (#1 ≪ #32 - #1) = #1 ≪ #32 - #1);;
    ![boolT] "ok".
Theorem failing_testEncDec32_t: ⊢ failing_testEncDec32 : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve failing_testEncDec32_t : types.

Definition testEncDec64Simple: val :=
  rec: "testEncDec64Simple" <> :=
    let: "ok" := ref #true in
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 #0 = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 #1 = #1);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 #1231234 = #1231234);;
    ![boolT] "ok".
Theorem testEncDec64Simple_t: ⊢ testEncDec64Simple : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testEncDec64Simple_t : types.

Definition testEncDec64: val :=
  rec: "testEncDec64" <> :=
    let: "ok" := ref #true in
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 #62206846038638762 = #62206846038638762);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 (#1 ≪ #63) = #1 ≪ #63);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 (#1 ≪ #47) = #1 ≪ #47);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 (#1 ≪ #20) = #1 ≪ #20);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 (#1 ≪ #18) = #1 ≪ #18);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 (#1 ≪ #10) = #1 ≪ #10);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 (#1 ≪ #0) = #1 ≪ #0);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 (#1 ≪ #64 - #1) = #1 ≪ #64 - #1);;
    ![boolT] "ok".
Theorem testEncDec64_t: ⊢ testEncDec64 : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testEncDec64_t : types.

(* function_ordering.go *)

(* helpers *)
Module Editor.
  Definition S := struct.decl [
    "s" :: slice.T uint64T;
    "next_val" :: uint64T
  ].
End Editor.

(* advances the array editor, and returns the value it wrote, storing
   "next" in next_val *)
Definition Editor__AdvanceReturn: val :=
  rec: "Editor__AdvanceReturn" "e" "next" :=
    let: "tmp" := ref (struct.loadF Editor.S "next_val" "e") in
    SliceSet uint64T (struct.loadF Editor.S "s" "e") #0 (![uint64T] "tmp");;
    struct.storeF Editor.S "next_val" "e" "next";;
    struct.storeF Editor.S "s" "e" (SliceSkip uint64T (struct.loadF Editor.S "s" "e") #1);;
    ![uint64T] "tmp".
Theorem Editor__AdvanceReturn_t: ⊢ Editor__AdvanceReturn : (struct.ptrT Editor.S -> uint64T -> uint64T).
Proof. typecheck. Qed.
Hint Resolve Editor__AdvanceReturn_t : types.

(* we call this function with side-effectful function calls as arguments,
   its implementation is unimportant *)
Definition addFour64: val :=
  rec: "addFour64" "a" "b" "c" "d" :=
    "a" + "b" + "c" + "d".
Theorem addFour64_t: ⊢ addFour64 : (uint64T -> uint64T -> uint64T -> uint64T -> uint64T).
Proof. typecheck. Qed.
Hint Resolve addFour64_t : types.

Module Pair.
  Definition S := struct.decl [
    "x" :: uint64T;
    "y" :: uint64T
  ].
End Pair.

(* tests *)
Definition failing_testFunctionOrdering: val :=
  rec: "failing_testFunctionOrdering" <> :=
    let: "arr" := ref (NewSlice uint64T #5) in
    let: "e1" := struct.mk Editor.S [
      "s" ::= SliceSkip uint64T (![slice.T uint64T] "arr") #0;
      "next_val" ::= #1
    ] in
    let: "e2" := struct.mk Editor.S [
      "s" ::= SliceSkip uint64T (![slice.T uint64T] "arr") #0;
      "next_val" ::= #101
    ] in
    (if: Editor__AdvanceReturn "e1" #2 + Editor__AdvanceReturn "e2" #102 ≠ #102
    then #false
    else
      (if: SliceGet uint64T (![slice.T uint64T] "arr") #0 ≠ #101
      then #false
      else
        (if: addFour64 (Editor__AdvanceReturn "e1" #3) (Editor__AdvanceReturn "e2" #103) (Editor__AdvanceReturn "e2" #104) (Editor__AdvanceReturn "e1" #4) ≠ #210
        then #false
        else
          (if: SliceGet uint64T (![slice.T uint64T] "arr") #1 ≠ #102
          then #false
          else
            (if: SliceGet uint64T (![slice.T uint64T] "arr") #2 ≠ #3
            then #false
            else
              let: "p" := struct.mk Pair.S [
                "x" ::= Editor__AdvanceReturn "e1" #5;
                "y" ::= Editor__AdvanceReturn "e2" #105
              ] in
              (if: SliceGet uint64T (![slice.T uint64T] "arr") #3 ≠ #104
              then #false
              else
                let: "q" := struct.mk Pair.S [
                  "y" ::= Editor__AdvanceReturn "e1" #6;
                  "x" ::= Editor__AdvanceReturn "e2" #106
                ] in
                (if: SliceGet uint64T (![slice.T uint64T] "arr") #4 ≠ #105
                then #false
                else (struct.get Pair.S "x" "p" + struct.get Pair.S "x" "q" = #109)))))))).
Theorem failing_testFunctionOrdering_t: ⊢ failing_testFunctionOrdering : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve failing_testFunctionOrdering_t : types.

(* loops.go *)

(* helpers *)
Definition standardForLoop: val :=
  rec: "standardForLoop" "s" :=
    let: "sumPtr" := ref (zero_val uint64T) in
    let: "i" := ref #0 in
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: ![uint64T] "i" < slice.len "s"
      then
        let: "sum" := ![uint64T] "sumPtr" in
        let: "x" := SliceGet uint64T "s" (![uint64T] "i") in
        "sumPtr" <-[refT uint64T] "sum" + "x";;
        "i" <-[uint64T] ![uint64T] "i" + #1;;
        Continue
      else Break));;
    let: "sum" := ![uint64T] "sumPtr" in
    "sum".
Theorem standardForLoop_t: ⊢ standardForLoop : (slice.T uint64T -> uint64T).
Proof. typecheck. Qed.
Hint Resolve standardForLoop_t : types.

(* based off diskAppendWait loop pattern in logging2 *)
Module LoopStruct.
  Definition S := struct.decl [
    "loopNext" :: refT uint64T
  ].
End LoopStruct.

Definition LoopStruct__forLoopWait: val :=
  rec: "LoopStruct__forLoopWait" "ls" "i" :=
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "nxt" := struct.get LoopStruct.S "loopNext" "ls" in
      (if: "i" < ![uint64T] "nxt"
      then Break
      else
        struct.get LoopStruct.S "loopNext" "ls" <-[refT uint64T] ![uint64T] (struct.get LoopStruct.S "loopNext" "ls") + #1;;
        Continue)).
Theorem LoopStruct__forLoopWait_t: ⊢ LoopStruct__forLoopWait : (struct.t LoopStruct.S -> uint64T -> unitT).
Proof. typecheck. Qed.
Hint Resolve LoopStruct__forLoopWait_t : types.

(* tests *)
Definition testStandardForLoop: val :=
  rec: "testStandardForLoop" <> :=
    let: "arr" := ref (NewSlice uint64T #4) in
    SliceSet uint64T (![slice.T uint64T] "arr") #0 (SliceGet uint64T (![slice.T uint64T] "arr") #0 + #1);;
    SliceSet uint64T (![slice.T uint64T] "arr") #1 (SliceGet uint64T (![slice.T uint64T] "arr") #1 + #3);;
    SliceSet uint64T (![slice.T uint64T] "arr") #2 (SliceGet uint64T (![slice.T uint64T] "arr") #2 + #5);;
    SliceSet uint64T (![slice.T uint64T] "arr") #3 (SliceGet uint64T (![slice.T uint64T] "arr") #3 + #7);;
    (standardForLoop (![slice.T uint64T] "arr") = #16).
Theorem testStandardForLoop_t: ⊢ testStandardForLoop : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testStandardForLoop_t : types.

Definition testForLoopWait: val :=
  rec: "testForLoopWait" <> :=
    let: "ls" := struct.mk LoopStruct.S [
      "loopNext" ::= ref (zero_val uint64T)
    ] in
    LoopStruct__forLoopWait "ls" #3;;
    (![uint64T] (struct.get LoopStruct.S "loopNext" "ls") = #4).
Theorem testForLoopWait_t: ⊢ testForLoopWait : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testForLoopWait_t : types.

(* maps.go *)

Definition IterateMapKeys: val :=
  rec: "IterateMapKeys" "m" :=
    let: "sum" := ref (zero_val uint64T) in
    MapIter "m" (λ: "k" <>,
      "sum" <-[uint64T] ![uint64T] "sum" + "k");;
    ![uint64T] "sum".
Theorem IterateMapKeys_t: ⊢ IterateMapKeys : (mapT uint64T -> uint64T).
Proof. typecheck. Qed.
Hint Resolve IterateMapKeys_t : types.

Definition IterateMapValues: val :=
  rec: "IterateMapValues" "m" :=
    let: "sum" := ref (zero_val uint64T) in
    MapIter "m" (λ: <> "v",
      "sum" <-[uint64T] ![uint64T] "sum" + "v");;
    ![uint64T] "sum".
Theorem IterateMapValues_t: ⊢ IterateMapValues : (mapT uint64T -> uint64T).
Proof. typecheck. Qed.
Hint Resolve IterateMapValues_t : types.

Definition testIterateMap: val :=
  rec: "testIterateMap" <> :=
    let: "ok" := ref #true in
    let: "m" := NewMap uint64T in
    MapInsert "m" #0 #1;;
    MapInsert "m" #1 #2;;
    MapInsert "m" #3 #4;;
    "ok" <-[boolT] ![boolT] "ok" && (IterateMapKeys "m" = #4);;
    "ok" <-[boolT] ![boolT] "ok" && (IterateMapValues "m" = #7);;
    ![boolT] "ok".
Theorem testIterateMap_t: ⊢ testIterateMap : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testIterateMap_t : types.

Definition testMapSize: val :=
  rec: "testMapSize" <> :=
    let: "ok" := ref #true in
    let: "m" := NewMap uint64T in
    "ok" <-[boolT] ![boolT] "ok" && (MapLen "m" = #0);;
    MapInsert "m" #0 #1;;
    MapInsert "m" #1 #2;;
    MapInsert "m" #3 #4;;
    "ok" <-[boolT] ![boolT] "ok" && (MapLen "m" = #3);;
    ![boolT] "ok".
Theorem testMapSize_t: ⊢ testMapSize : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testMapSize_t : types.

(* operations.go *)

(* helpers *)
Definition reverseAssignOps64: val :=
  rec: "reverseAssignOps64" "x" :=
    let: "y" := ref (zero_val uint64T) in
    "y" <-[uint64T] ![uint64T] "y" + "x";;
    "y" <-[uint64T] ![uint64T] "y" - "x";;
    "y" <-[uint64T] ![uint64T] "y" + #1;;
    "y" <-[uint64T] ![uint64T] "y" - #1;;
    ![uint64T] "y".
Theorem reverseAssignOps64_t: ⊢ reverseAssignOps64 : (uint64T -> uint64T).
Proof. typecheck. Qed.
Hint Resolve reverseAssignOps64_t : types.

Definition reverseAssignOps32: val :=
  rec: "reverseAssignOps32" "x" :=
    let: "y" := ref (zero_val uint32T) in
    "y" <-[uint32T] ![uint32T] "y" + "x";;
    "y" <-[uint32T] ![uint32T] "y" - "x";;
    "y" <-[uint32T] ![uint32T] "y" + #1;;
    "y" <-[uint32T] ![uint32T] "y" - #1;;
    ![uint32T] "y".
Theorem reverseAssignOps32_t: ⊢ reverseAssignOps32 : (uint32T -> uint32T).
Proof. typecheck. Qed.
Hint Resolve reverseAssignOps32_t : types.

Definition add64Equals: val :=
  rec: "add64Equals" "x" "y" "z" :=
    ("x" + "y" = "z").
Theorem add64Equals_t: ⊢ add64Equals : (uint64T -> uint64T -> uint64T -> boolT).
Proof. typecheck. Qed.
Hint Resolve add64Equals_t : types.

Definition sub64Equals: val :=
  rec: "sub64Equals" "x" "y" "z" :=
    ("x" - "y" = "z").
Theorem sub64Equals_t: ⊢ sub64Equals : (uint64T -> uint64T -> uint64T -> boolT).
Proof. typecheck. Qed.
Hint Resolve sub64Equals_t : types.

(* tests *)
Definition testReverseAssignOps64: val :=
  rec: "testReverseAssignOps64" <> :=
    let: "ok" := ref #true in
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 #0 = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 #1 = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 #1231234 = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 #62206846038638762 = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 (#1 ≪ #63) = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 (#1 ≪ #47) = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 (#1 ≪ #20) = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 (#1 ≪ #18) = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 (#1 ≪ #10) = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 (#1 ≪ #0) = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 (#1 ≪ #64 - #1) = #0);;
    ![boolT] "ok".
Theorem testReverseAssignOps64_t: ⊢ testReverseAssignOps64 : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testReverseAssignOps64_t : types.

Definition failing_testReverseAssignOps32: val :=
  rec: "failing_testReverseAssignOps32" <> :=
    let: "ok" := ref #true in
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps32 (#(U32 0)) = #(U32 0));;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps32 (#(U32 1)) = #(U32 0));;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps32 (#(U32 1231234)) = #(U32 0));;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps32 (#(U32 3434807466)) = #(U32 0));;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps32 (#1 ≪ #20) = #(U32 0));;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps32 (#1 ≪ #18) = #(U32 0));;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps32 (#1 ≪ #10) = #(U32 0));;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps32 (#1 ≪ #0) = #(U32 0));;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps32 (#1 ≪ #32 - #1) = #(U32 0));;
    ![boolT] "ok".
Theorem failing_testReverseAssignOps32_t: ⊢ failing_testReverseAssignOps32 : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve failing_testReverseAssignOps32_t : types.

Definition testAdd64Equals: val :=
  rec: "testAdd64Equals" <> :=
    let: "ok" := ref #true in
    "ok" <-[boolT] ![boolT] "ok" && add64Equals #2 #3 #5;;
    "ok" <-[boolT] ![boolT] "ok" && add64Equals (#1 ≪ #64 - #1) #1 #0;;
    ![boolT] "ok".
Theorem testAdd64Equals_t: ⊢ testAdd64Equals : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testAdd64Equals_t : types.

Definition testSub64Equals: val :=
  rec: "testSub64Equals" <> :=
    let: "ok" := ref #true in
    "ok" <-[boolT] ![boolT] "ok" && sub64Equals #2 #1 #1;;
    "ok" <-[boolT] ![boolT] "ok" && sub64Equals (#1 ≪ #64 - #1) (#1 ≪ #63) (#1 ≪ #63 - #1);;
    "ok" <-[boolT] ![boolT] "ok" && sub64Equals #2 #8 (#1 ≪ #64 - #6);;
    ![boolT] "ok".
Theorem testSub64Equals_t: ⊢ testSub64Equals : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testSub64Equals_t : types.

Definition failing_testDivisionPrecedence: val :=
  rec: "failing_testDivisionPrecedence" <> :=
    let: "blockSize" := #4096 in
    let: "hdrmeta" := #8 in
    let: "hdraddrs" := ("blockSize" - "hdrmeta") `quot` #8 in
    ("hdraddrs" = #511).
Theorem failing_testDivisionPrecedence_t: ⊢ failing_testDivisionPrecedence : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve failing_testDivisionPrecedence_t : types.

Definition failing_testModPrecedence: val :=
  rec: "failing_testModPrecedence" <> :=
    let: "x1" := #513 + #12 `rem` #8 in
    let: "x2" := (#513 + #12) `rem` #8 in
    ("x1" = #517) && ("x2" = #5).
Theorem failing_testModPrecedence_t: ⊢ failing_testModPrecedence : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve failing_testModPrecedence_t : types.

(* shortcircuiting.go *)

(* helpers *)
Module BoolTest.
  Definition S := struct.decl [
    "t" :: boolT;
    "f" :: boolT;
    "tc" :: uint64T;
    "fc" :: uint64T
  ].
End BoolTest.

Definition CheckTrue: val :=
  rec: "CheckTrue" "b" :=
    struct.storeF BoolTest.S "tc" "b" (struct.loadF BoolTest.S "tc" "b" + #1);;
    struct.loadF BoolTest.S "t" "b".
Theorem CheckTrue_t: ⊢ CheckTrue : (struct.ptrT BoolTest.S -> boolT).
Proof. typecheck. Qed.
Hint Resolve CheckTrue_t : types.

Definition CheckFalse: val :=
  rec: "CheckFalse" "b" :=
    struct.storeF BoolTest.S "fc" "b" (struct.loadF BoolTest.S "fc" "b" + #1);;
    struct.loadF BoolTest.S "f" "b".
Theorem CheckFalse_t: ⊢ CheckFalse : (struct.ptrT BoolTest.S -> boolT).
Proof. typecheck. Qed.
Hint Resolve CheckFalse_t : types.

(* tests *)
Definition testShortcircuitAndTF: val :=
  rec: "testShortcircuitAndTF" <> :=
    let: "b" := struct.new BoolTest.S [
      "t" ::= #true;
      "f" ::= #false;
      "tc" ::= #0;
      "fc" ::= #0
    ] in
    (if: CheckTrue "b" && CheckFalse "b"
    then #false
    else (struct.loadF BoolTest.S "tc" "b" = #1) && (struct.loadF BoolTest.S "fc" "b" = #1)).
Theorem testShortcircuitAndTF_t: ⊢ testShortcircuitAndTF : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testShortcircuitAndTF_t : types.

Definition testShortcircuitAndFT: val :=
  rec: "testShortcircuitAndFT" <> :=
    let: "b" := struct.new BoolTest.S [
      "t" ::= #true;
      "f" ::= #false;
      "tc" ::= #0;
      "fc" ::= #0
    ] in
    (if: CheckFalse "b" && CheckTrue "b"
    then #false
    else (struct.loadF BoolTest.S "tc" "b" = #0) && (struct.loadF BoolTest.S "fc" "b" = #1)).
Theorem testShortcircuitAndFT_t: ⊢ testShortcircuitAndFT : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testShortcircuitAndFT_t : types.

Definition testShortcircuitOrTF: val :=
  rec: "testShortcircuitOrTF" <> :=
    let: "b" := struct.new BoolTest.S [
      "t" ::= #true;
      "f" ::= #false;
      "tc" ::= #0;
      "fc" ::= #0
    ] in
    (if: CheckTrue "b" || CheckFalse "b"
    then (struct.loadF BoolTest.S "tc" "b" = #1) && (struct.loadF BoolTest.S "fc" "b" = #0)
    else #false).
Theorem testShortcircuitOrTF_t: ⊢ testShortcircuitOrTF : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testShortcircuitOrTF_t : types.

Definition testShortcircuitOrFT: val :=
  rec: "testShortcircuitOrFT" <> :=
    let: "b" := struct.new BoolTest.S [
      "t" ::= #true;
      "f" ::= #false;
      "tc" ::= #0;
      "fc" ::= #0
    ] in
    (if: CheckFalse "b" || CheckTrue "b"
    then (struct.loadF BoolTest.S "tc" "b" = #1) && (struct.loadF BoolTest.S "fc" "b" = #1)
    else #false).
Theorem testShortcircuitOrFT_t: ⊢ testShortcircuitOrFT : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testShortcircuitOrFT_t : types.

(* slices.go *)

(* helpers *)
Module ArrayEditor.
  Definition S := struct.decl [
    "s" :: slice.T uint64T;
    "next_val" :: uint64T
  ].
End ArrayEditor.

Definition ArrayEditor__Advance: val :=
  rec: "ArrayEditor__Advance" "ae" "arr" "next" :=
    SliceSet uint64T "arr" #0 (SliceGet uint64T "arr" #0 + #1);;
    SliceSet uint64T (struct.loadF ArrayEditor.S "s" "ae") #0 (struct.loadF ArrayEditor.S "next_val" "ae");;
    struct.storeF ArrayEditor.S "next_val" "ae" "next";;
    struct.storeF ArrayEditor.S "s" "ae" (SliceSkip uint64T (struct.loadF ArrayEditor.S "s" "ae") #1).
Theorem ArrayEditor__Advance_t: ⊢ ArrayEditor__Advance : (struct.ptrT ArrayEditor.S -> slice.T uint64T -> uint64T -> unitT).
Proof. typecheck. Qed.
Hint Resolve ArrayEditor__Advance_t : types.

(* tests *)
Definition testOverwriteArray: val :=
  rec: "testOverwriteArray" <> :=
    let: "arr" := ref (NewSlice uint64T #4) in
    let: "ae1" := struct.new ArrayEditor.S [
      "s" ::= SliceSkip uint64T (![slice.T uint64T] "arr") #0;
      "next_val" ::= #1
    ] in
    let: "ae2" := struct.new ArrayEditor.S [
      "s" ::= SliceSkip uint64T (![slice.T uint64T] "arr") #1;
      "next_val" ::= #102
    ] in
    ArrayEditor__Advance "ae2" (![slice.T uint64T] "arr") #103;;
    ArrayEditor__Advance "ae2" (![slice.T uint64T] "arr") #104;;
    ArrayEditor__Advance "ae2" (![slice.T uint64T] "arr") #105;;
    ArrayEditor__Advance "ae1" (![slice.T uint64T] "arr") #2;;
    ArrayEditor__Advance "ae1" (![slice.T uint64T] "arr") #3;;
    ArrayEditor__Advance "ae1" (![slice.T uint64T] "arr") #4;;
    ArrayEditor__Advance "ae1" (![slice.T uint64T] "arr") #5;;
    (if: SliceGet uint64T (![slice.T uint64T] "arr") #0 + SliceGet uint64T (![slice.T uint64T] "arr") #1 + SliceGet uint64T (![slice.T uint64T] "arr") #2 + SliceGet uint64T (![slice.T uint64T] "arr") #3 ≥ #100
    then #false
    else (SliceGet uint64T (![slice.T uint64T] "arr") #3 = #4) && (SliceGet uint64T (![slice.T uint64T] "arr") #0 = #4)).
Theorem testOverwriteArray_t: ⊢ testOverwriteArray : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve testOverwriteArray_t : types.

(* strings.go *)

(* helpers *)
Definition stringAppend: val :=
  rec: "stringAppend" "s" "x" :=
    "s" + uint64_to_string "x".
Theorem stringAppend_t: ⊢ stringAppend : (stringT -> uint64T -> stringT).
Proof. typecheck. Qed.
Hint Resolve stringAppend_t : types.

Definition stringLength: val :=
  rec: "stringLength" "s" :=
    strLen "s".
Theorem stringLength_t: ⊢ stringLength : (stringT -> uint64T).
Proof. typecheck. Qed.
Hint Resolve stringLength_t : types.

(* tests *)
Definition failing_testStringAppend: val :=
  rec: "failing_testStringAppend" <> :=
    let: "ok" := ref #true in
    let: "s" := ref #(str"123") in
    let: "y" := ref (stringAppend (![stringT] "s") #45) in
    ![boolT] "ok" && (![stringT] "y" = #(str"12345")).
Theorem failing_testStringAppend_t: ⊢ failing_testStringAppend : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve failing_testStringAppend_t : types.

Definition failing_testStringLength: val :=
  rec: "failing_testStringLength" <> :=
    let: "ok" := ref #true in
    let: "s" := ref #(str"") in
    "ok" <-[boolT] ![boolT] "ok" && (strLen (![stringT] "s") = #0);;
    "s" <-[stringT] stringAppend (![stringT] "s") #1;;
    "ok" <-[boolT] ![boolT] "ok" && (strLen (![stringT] "s") = #1);;
    "s" <-[stringT] stringAppend (![stringT] "s") #23;;
    ![boolT] "ok" && (strLen (![stringT] "s") = #3).
Theorem failing_testStringLength_t: ⊢ failing_testStringLength : (unitT -> boolT).
Proof. typecheck. Qed.
Hint Resolve failing_testStringLength_t : types.

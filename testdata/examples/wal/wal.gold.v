(* autogenerated from github.com/goose-lang/goose/testdata/examples/wal *)
From New.golang Require Import defn.
From New.code Require github_com.goose_lang.primitive.
From New.code Require github_com.goose_lang.primitive.disk.
From New.code Require sync.

From New Require Import disk_prelude.

(* 10 is completely arbitrary *)
Definition MaxTxnWrites : expr := #10.

Definition logLength : expr := #1 + (#2 * MaxTxnWrites).

Definition Log : go_type := structT [
  "d" :: disk.Disk;
  "l" :: ptrT;
  "cache" :: mapT uint64T (sliceT byteT);
  "length" :: ptrT
]%struct.

(* go: log.go:56:14 *)
Definition Log__unlock : val :=
  rec: "Log__unlock" "l" <> :=
    exception_do (let: "l" := (ref_ty Log "l") in
    do:  ((sync.Mutex__Unlock (![ptrT] (struct.field_ref Log "l" "l"))) #())).

(* go: log.go:25:6 *)
Definition intToBlock : val :=
  rec: "intToBlock" "a" :=
    exception_do (let: "a" := (ref_ty uint64T "a") in
    let: "b" := (ref_ty (sliceT byteT) (zero_val (sliceT byteT))) in
    let: "$r0" := (slice.make2 byteT disk.BlockSize) in
    do:  ("b" <-[sliceT byteT] "$r0");;;
    do:  (let: "$a0" := (![sliceT byteT] "b") in
    let: "$a1" := (![uint64T] "a") in
    primitive.UInt64Put "$a0" "$a1");;;
    return: (![sliceT byteT] "b")).

(* go: log.go:142:6 *)
Definition clearLog : val :=
  rec: "clearLog" "d" :=
    exception_do (let: "d" := (ref_ty disk.Disk "d") in
    let: "header" := (ref_ty (sliceT byteT) (zero_val (sliceT byteT))) in
    let: "$r0" := (let: "$a0" := #0 in
    intToBlock "$a0") in
    do:  ("header" <-[sliceT byteT] "$r0");;;
    do:  (let: "$a0" := #0 in
    let: "$a1" := (![sliceT byteT] "header") in
    (interface.get "Write" (![disk.Disk] "d")) "$a0" "$a1")).

(* go: log.go:31:6 *)
Definition blockToInt : val :=
  rec: "blockToInt" "v" :=
    exception_do (let: "v" := (ref_ty (sliceT byteT) "v") in
    let: "a" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (let: "$a0" := (![sliceT byteT] "v") in
    primitive.UInt64Get "$a0") in
    do:  ("a" <-[uint64T] "$r0");;;
    return: (![uint64T] "a")).

(* go: log.go:122:6 *)
Definition getLogEntry : val :=
  rec: "getLogEntry" "d" "logOffset" :=
    exception_do (let: "logOffset" := (ref_ty uint64T "logOffset") in
    let: "d" := (ref_ty disk.Disk "d") in
    let: "diskAddr" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (#1 + (#2 * (![uint64T] "logOffset"))) in
    do:  ("diskAddr" <-[uint64T] "$r0");;;
    let: "aBlock" := (ref_ty (sliceT byteT) (zero_val (sliceT byteT))) in
    let: "$r0" := (let: "$a0" := (![uint64T] "diskAddr") in
    (interface.get "Read" (![disk.Disk] "d")) "$a0") in
    do:  ("aBlock" <-[sliceT byteT] "$r0");;;
    let: "a" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (let: "$a0" := (![sliceT byteT] "aBlock") in
    blockToInt "$a0") in
    do:  ("a" <-[uint64T] "$r0");;;
    let: "v" := (ref_ty (sliceT byteT) (zero_val (sliceT byteT))) in
    let: "$r0" := (let: "$a0" := ((![uint64T] "diskAddr") + #1) in
    (interface.get "Read" (![disk.Disk] "d")) "$a0") in
    do:  ("v" <-[sliceT byteT] "$r0");;;
    return: (![uint64T] "a", ![sliceT byteT] "v")).

(* applyLog assumes we are running sequentially

   go: log.go:131:6 *)
Definition applyLog : val :=
  rec: "applyLog" "d" "length" :=
    exception_do (let: "length" := (ref_ty uint64T "length") in
    let: "d" := (ref_ty disk.Disk "d") in
    (let: "i" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := #0 in
    do:  ("i" <-[uint64T] "$r0");;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: (![uint64T] "i") < (![uint64T] "length")
      then
        let: "v" := (ref_ty (sliceT byteT) (zero_val (sliceT byteT))) in
        let: "a" := (ref_ty uint64T (zero_val uint64T)) in
        let: ("$ret0", "$ret1") := (let: "$a0" := (![disk.Disk] "d") in
        let: "$a1" := (![uint64T] "i") in
        getLogEntry "$a0" "$a1") in
        let: "$r0" := "$ret0" in
        let: "$r1" := "$ret1" in
        do:  ("a" <-[uint64T] "$r0");;;
        do:  ("v" <-[sliceT byteT] "$r1");;;
        do:  (let: "$a0" := (logLength + (![uint64T] "a")) in
        let: "$a1" := (![sliceT byteT] "v") in
        (interface.get "Write" (![disk.Disk] "d")) "$a0" "$a1");;;
        let: "$r0" := ((![uint64T] "i") + #1) in
        do:  ("i" <-[uint64T] "$r0");;;
        continue: #()
      else do:  #());;;
      break: #()))).

(* go: log.go:52:14 *)
Definition Log__lock : val :=
  rec: "Log__lock" "l" <> :=
    exception_do (let: "l" := (ref_ty Log "l") in
    do:  ((sync.Mutex__Lock (![ptrT] (struct.field_ref Log "l" "l"))) #())).

(* Apply all the committed transactions.

   Frees all the space in the log.

   go: log.go:150:14 *)
Definition Log__Apply : val :=
  rec: "Log__Apply" "l" <> :=
    exception_do (let: "l" := (ref_ty Log "l") in
    do:  ((Log__lock (![ptrT] "l")) #());;;
    let: "length" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (![uint64T] (![ptrT] (struct.field_ref Log "length" "l"))) in
    do:  ("length" <-[uint64T] "$r0");;;
    do:  (let: "$a0" := (![disk.Disk] (struct.field_ref Log "d" "l")) in
    let: "$a1" := (![uint64T] "length") in
    applyLog "$a0" "$a1");;;
    do:  (let: "$a0" := (![disk.Disk] (struct.field_ref Log "d" "l")) in
    clearLog "$a0");;;
    let: "$r0" := #0 in
    do:  ((![ptrT] (struct.field_ref Log "length" "l")) <-[uint64T] "$r0");;;
    do:  ((Log__unlock (![ptrT] "l")) #())).

(* BeginTxn allocates space for a new transaction in the log.

   Returns true if the allocation succeeded.

   go: log.go:63:14 *)
Definition Log__BeginTxn : val :=
  rec: "Log__BeginTxn" "l" <> :=
    exception_do (let: "l" := (ref_ty Log "l") in
    do:  ((Log__lock (![ptrT] "l")) #());;;
    let: "length" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (![uint64T] (![ptrT] (struct.field_ref Log "length" "l"))) in
    do:  ("length" <-[uint64T] "$r0");;;
    (if: (![uint64T] "length") = #0
    then
      do:  ((Log__unlock (![ptrT] "l")) #());;;
      return: (#true)
    else do:  #());;;
    do:  ((Log__unlock (![ptrT] "l")) #());;;
    return: (#false)).

(* Commit the current transaction.

   go: log.go:113:14 *)
Definition Log__Commit : val :=
  rec: "Log__Commit" "l" <> :=
    exception_do (let: "l" := (ref_ty Log "l") in
    do:  ((Log__lock (![ptrT] "l")) #());;;
    let: "length" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (![uint64T] (![ptrT] (struct.field_ref Log "length" "l"))) in
    do:  ("length" <-[uint64T] "$r0");;;
    do:  ((Log__unlock (![ptrT] "l")) #());;;
    let: "header" := (ref_ty (sliceT byteT) (zero_val (sliceT byteT))) in
    let: "$r0" := (let: "$a0" := (![uint64T] "length") in
    intToBlock "$a0") in
    do:  ("header" <-[sliceT byteT] "$r0");;;
    do:  (let: "$a0" := #0 in
    let: "$a1" := (![sliceT byteT] "header") in
    (interface.get "Write" (![disk.Disk] (struct.field_ref Log "d" "l"))) "$a0" "$a1")).

(* Read from the logical disk.

   Reads must go through the log to return committed but un-applied writes.

   go: log.go:77:14 *)
Definition Log__Read : val :=
  rec: "Log__Read" "l" "a" :=
    exception_do (let: "l" := (ref_ty Log "l") in
    let: "a" := (ref_ty uint64T "a") in
    do:  ((Log__lock (![ptrT] "l")) #());;;
    let: "ok" := (ref_ty boolT (zero_val boolT)) in
    let: "v" := (ref_ty (sliceT byteT) (zero_val (sliceT byteT))) in
    let: ("$ret0", "$ret1") := (map.get (![mapT uint64T (sliceT byteT)] (struct.field_ref Log "cache" "l")) (![uint64T] "a")) in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("v" <-[sliceT byteT] "$r0");;;
    do:  ("ok" <-[boolT] "$r1");;;
    (if: ![boolT] "ok"
    then
      do:  ((Log__unlock (![ptrT] "l")) #());;;
      return: (![sliceT byteT] "v")
    else do:  #());;;
    do:  ((Log__unlock (![ptrT] "l")) #());;;
    let: "dv" := (ref_ty (sliceT byteT) (zero_val (sliceT byteT))) in
    let: "$r0" := (let: "$a0" := (logLength + (![uint64T] "a")) in
    (interface.get "Read" (![disk.Disk] (struct.field_ref Log "d" "l"))) "$a0") in
    do:  ("dv" <-[sliceT byteT] "$r0");;;
    return: (![sliceT byteT] "dv")).

(* go: log.go:90:14 *)
Definition Log__Size : val :=
  rec: "Log__Size" "l" <> :=
    exception_do (let: "l" := (ref_ty Log "l") in
    let: "sz" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := ((interface.get "Size" (![disk.Disk] (struct.field_ref Log "d" "l"))) #()) in
    do:  ("sz" <-[uint64T] "$r0");;;
    return: ((![uint64T] "sz") - logLength)).

(* Write to the disk through the log.

   go: log.go:97:14 *)
Definition Log__Write : val :=
  rec: "Log__Write" "l" "a" "v" :=
    exception_do (let: "l" := (ref_ty Log "l") in
    let: "v" := (ref_ty (sliceT byteT) "v") in
    let: "a" := (ref_ty uint64T "a") in
    do:  ((Log__lock (![ptrT] "l")) #());;;
    let: "length" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (![uint64T] (![ptrT] (struct.field_ref Log "length" "l"))) in
    do:  ("length" <-[uint64T] "$r0");;;
    (if: (![uint64T] "length") ≥ MaxTxnWrites
    then
      do:  (let: "$a0" := (interface.make string__mset #(str "transaction is at capacity")) in
      Panic "$a0")
    else do:  #());;;
    let: "aBlock" := (ref_ty (sliceT byteT) (zero_val (sliceT byteT))) in
    let: "$r0" := (let: "$a0" := (![uint64T] "a") in
    intToBlock "$a0") in
    do:  ("aBlock" <-[sliceT byteT] "$r0");;;
    let: "nextAddr" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (#1 + (#2 * (![uint64T] "length"))) in
    do:  ("nextAddr" <-[uint64T] "$r0");;;
    do:  (let: "$a0" := (![uint64T] "nextAddr") in
    let: "$a1" := (![sliceT byteT] "aBlock") in
    (interface.get "Write" (![disk.Disk] (struct.field_ref Log "d" "l"))) "$a0" "$a1");;;
    do:  (let: "$a0" := ((![uint64T] "nextAddr") + #1) in
    let: "$a1" := (![sliceT byteT] "v") in
    (interface.get "Write" (![disk.Disk] (struct.field_ref Log "d" "l"))) "$a0" "$a1");;;
    let: "$r0" := (![sliceT byteT] "v") in
    do:  (map.insert (![mapT uint64T (sliceT byteT)] (struct.field_ref Log "cache" "l")) (![uint64T] "a") "$r0");;;
    let: "$r0" := ((![uint64T] "length") + #1) in
    do:  ((![ptrT] (struct.field_ref Log "length" "l")) <-[uint64T] "$r0");;;
    do:  ((Log__unlock (![ptrT] "l")) #())).

Definition Log__mset : list (string * val) := [
  ("Apply", Log__Apply);
  ("BeginTxn", Log__BeginTxn);
  ("Commit", Log__Commit);
  ("Read", Log__Read);
  ("Size", Log__Size);
  ("Write", Log__Write);
  ("lock", Log__lock);
  ("unlock", Log__unlock)
].

Definition Log__mset_ptr : list (string * val) := [
  ("Apply", (λ: "r", Log__Apply (![Log] "r"))%V);
  ("BeginTxn", (λ: "r", Log__BeginTxn (![Log] "r"))%V);
  ("Commit", (λ: "r", Log__Commit (![Log] "r"))%V);
  ("Read", (λ: "r", Log__Read (![Log] "r"))%V);
  ("Size", (λ: "r", Log__Size (![Log] "r"))%V);
  ("Write", (λ: "r", Log__Write (![Log] "r"))%V);
  ("lock", (λ: "r", Log__lock (![Log] "r"))%V);
  ("unlock", (λ: "r", Log__unlock (![Log] "r"))%V)
].

(* New initializes a fresh log

   go: log.go:37:6 *)
Definition New : val :=
  rec: "New" <> :=
    exception_do (let: "d" := (ref_ty disk.Disk (zero_val disk.Disk)) in
    let: "$r0" := (disk.Get #()) in
    do:  ("d" <-[disk.Disk] "$r0");;;
    let: "diskSize" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := ((interface.get "Size" (![disk.Disk] "d")) #()) in
    do:  ("diskSize" <-[uint64T] "$r0");;;
    (if: (![uint64T] "diskSize") ≤ logLength
    then
      do:  (let: "$a0" := (interface.make string__mset #(str "disk is too small to host log")) in
      Panic "$a0")
    else do:  #());;;
    let: "cache" := (ref_ty (mapT uint64T (sliceT byteT)) (zero_val (mapT uint64T (sliceT byteT)))) in
    let: "$r0" := (map.make uint64T (sliceT byteT) #()) in
    do:  ("cache" <-[mapT uint64T (sliceT byteT)] "$r0");;;
    let: "header" := (ref_ty (sliceT byteT) (zero_val (sliceT byteT))) in
    let: "$r0" := (let: "$a0" := #0 in
    intToBlock "$a0") in
    do:  ("header" <-[sliceT byteT] "$r0");;;
    do:  (let: "$a0" := #0 in
    let: "$a1" := (![sliceT byteT] "header") in
    (interface.get "Write" (![disk.Disk] "d")) "$a0" "$a1");;;
    let: "lengthPtr" := (ref_ty ptrT (zero_val ptrT)) in
    let: "$r0" := (ref_ty uint64T (zero_val uint64T)) in
    do:  ("lengthPtr" <-[ptrT] "$r0");;;
    let: "$r0" := #0 in
    do:  ((![ptrT] "lengthPtr") <-[uint64T] "$r0");;;
    let: "l" := (ref_ty ptrT (zero_val ptrT)) in
    let: "$r0" := (ref_ty sync.Mutex (zero_val sync.Mutex)) in
    do:  ("l" <-[ptrT] "$r0");;;
    return: (struct.make Log [{
       "d" ::= ![disk.Disk] "d";
       "cache" ::= ![mapT uint64T (sliceT byteT)] "cache";
       "length" ::= ![ptrT] "lengthPtr";
       "l" ::= ![ptrT] "l"
     }])).

(* Open recovers the log following a crash or shutdown

   go: log.go:163:6 *)
Definition Open : val :=
  rec: "Open" <> :=
    exception_do (let: "d" := (ref_ty disk.Disk (zero_val disk.Disk)) in
    let: "$r0" := (disk.Get #()) in
    do:  ("d" <-[disk.Disk] "$r0");;;
    let: "header" := (ref_ty (sliceT byteT) (zero_val (sliceT byteT))) in
    let: "$r0" := (let: "$a0" := #0 in
    (interface.get "Read" (![disk.Disk] "d")) "$a0") in
    do:  ("header" <-[sliceT byteT] "$r0");;;
    let: "length" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (let: "$a0" := (![sliceT byteT] "header") in
    blockToInt "$a0") in
    do:  ("length" <-[uint64T] "$r0");;;
    do:  (let: "$a0" := (![disk.Disk] "d") in
    let: "$a1" := (![uint64T] "length") in
    applyLog "$a0" "$a1");;;
    do:  (let: "$a0" := (![disk.Disk] "d") in
    clearLog "$a0");;;
    let: "cache" := (ref_ty (mapT uint64T (sliceT byteT)) (zero_val (mapT uint64T (sliceT byteT)))) in
    let: "$r0" := (map.make uint64T (sliceT byteT) #()) in
    do:  ("cache" <-[mapT uint64T (sliceT byteT)] "$r0");;;
    let: "lengthPtr" := (ref_ty ptrT (zero_val ptrT)) in
    let: "$r0" := (ref_ty uint64T (zero_val uint64T)) in
    do:  ("lengthPtr" <-[ptrT] "$r0");;;
    let: "$r0" := #0 in
    do:  ((![ptrT] "lengthPtr") <-[uint64T] "$r0");;;
    let: "l" := (ref_ty ptrT (zero_val ptrT)) in
    let: "$r0" := (ref_ty sync.Mutex (zero_val sync.Mutex)) in
    do:  ("l" <-[ptrT] "$r0");;;
    return: (struct.make Log [{
       "d" ::= ![disk.Disk] "d";
       "cache" ::= ![mapT uint64T (sliceT byteT)] "cache";
       "length" ::= ![ptrT] "lengthPtr";
       "l" ::= ![ptrT] "l"
     }])).

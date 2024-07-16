(* autogenerated from github.com/tchajed/goose/testdata/examples/wal *)
From New.golang Require Import defn.
From New.code Require github_com.tchajed.goose.machine.
From New.code Require github_com.tchajed.goose.machine.disk.
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
].

Definition intToBlock : val :=
  rec: "intToBlock" "a" :=
    exception_do (let: "a" := ref_ty uint64T "a" in
    let: "b" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := slice.make2 byteT disk.BlockSize in
    do:  "b" <-[sliceT byteT] "$a0";;;
    do:  machine.UInt64Put (![sliceT byteT] "b") (![uint64T] "a");;;
    return: (![sliceT byteT] "b");;;
    do:  #()).

Definition blockToInt : val :=
  rec: "blockToInt" "v" :=
    exception_do (let: "v" := ref_ty (sliceT byteT) "v" in
    let: "a" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := machine.UInt64Get (![sliceT byteT] "v") in
    do:  "a" <-[uint64T] "$a0";;;
    return: (![uint64T] "a");;;
    do:  #()).

(* New initializes a fresh log *)
Definition New : val :=
  rec: "New" <> :=
    exception_do (let: "d" := ref_ty disk.Disk (zero_val disk.Disk) in
    let: "$a0" := disk.Get #() in
    do:  "d" <-[disk.Disk] "$a0";;;
    let: "diskSize" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := (__Size (![disk.Disk] "d")) #() in
    do:  "diskSize" <-[uint64T] "$a0";;;
    (if: (![uint64T] "diskSize") ≤ logLength
    then
      do:  Panic "disk is too small to host log";;;
      do:  #()
    else do:  #());;;
    let: "cache" := ref_ty (mapT uint64T (sliceT byteT)) (zero_val (mapT uint64T (sliceT byteT))) in
    let: "$a0" := map.make uint64T (sliceT byteT) #() in
    do:  "cache" <-[mapT uint64T (sliceT byteT)] "$a0";;;
    let: "header" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := intToBlock #0 in
    do:  "header" <-[sliceT byteT] "$a0";;;
    do:  (__Write (![disk.Disk] "d")) #0 (![sliceT byteT] "header");;;
    let: "lengthPtr" := ref_ty ptrT (zero_val ptrT) in
    let: "$a0" := ref_ty uint64T (zero_val uint64T) in
    do:  "lengthPtr" <-[ptrT] "$a0";;;
    let: "$a0" := #0 in
    do:  (![ptrT] "lengthPtr") <-[uint64T] "$a0";;;
    let: "l" := ref_ty ptrT (zero_val ptrT) in
    let: "$a0" := ref_ty sync.Mutex (zero_val sync.Mutex) in
    do:  "l" <-[ptrT] "$a0";;;
    return: (struct.make Log {[
       #(str "d") := ![disk.Disk] "d";
       #(str "cache") := ![mapT uint64T (sliceT byteT)] "cache";
       #(str "length") := ![ptrT] "lengthPtr";
       #(str "l") := ![ptrT] "l"
     ]});;;
    do:  #()).

Definition Log__lock : val :=
  rec: "Log__lock" "l" :=
    exception_do (let: "l" := ref_ty Log "l" in
    do:  (sync.Mutex__Lock (![ptrT] (struct.field_ref Log "l" "l"))) #();;;
    do:  #()).

Definition Log__unlock : val :=
  rec: "Log__unlock" "l" :=
    exception_do (let: "l" := ref_ty Log "l" in
    do:  (sync.Mutex__Unlock (![ptrT] (struct.field_ref Log "l" "l"))) #();;;
    do:  #()).

(* BeginTxn allocates space for a new transaction in the log.

   Returns true if the allocation succeeded. *)
Definition Log__BeginTxn : val :=
  rec: "Log__BeginTxn" "l" :=
    exception_do (let: "l" := ref_ty Log "l" in
    do:  (Log__lock (![Log] "l")) #();;;
    let: "length" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := ![uint64T] (![ptrT] (struct.field_ref Log "length" "l")) in
    do:  "length" <-[uint64T] "$a0";;;
    (if: (![uint64T] "length") = #0
    then
      do:  (Log__unlock (![Log] "l")) #();;;
      return: (#true);;;
      do:  #()
    else do:  #());;;
    do:  (Log__unlock (![Log] "l")) #();;;
    return: (#false);;;
    do:  #()).

(* Read from the logical disk.

   Reads must go through the log to return committed but un-applied writes. *)
Definition Log__Read : val :=
  rec: "Log__Read" "l" "a" :=
    exception_do (let: "l" := ref_ty Log "l" in
    let: "a" := ref_ty uint64T "a" in
    do:  (Log__lock (![Log] "l")) #();;;
    let: "ok" := ref_ty boolT (zero_val boolT) in
    let: "v" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: ("$a0", "$a1") := Fst (map.get (![mapT uint64T (sliceT byteT)] (struct.field_ref Log "cache" "l")) (![uint64T] "a")) in
    do:  "ok" <-[boolT] "$a1";;;
    do:  "v" <-[sliceT byteT] "$a0";;;
    (if: ![boolT] "ok"
    then
      do:  (Log__unlock (![Log] "l")) #();;;
      return: (![sliceT byteT] "v");;;
      do:  #()
    else do:  #());;;
    do:  (Log__unlock (![Log] "l")) #();;;
    let: "dv" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := (__Read (![disk.Disk] (struct.field_ref Log "d" "l"))) (logLength + (![uint64T] "a")) in
    do:  "dv" <-[sliceT byteT] "$a0";;;
    return: (![sliceT byteT] "dv");;;
    do:  #()).

Definition Log__Size : val :=
  rec: "Log__Size" "l" :=
    exception_do (let: "l" := ref_ty Log "l" in
    let: "sz" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := (__Size (![disk.Disk] (struct.field_ref Log "d" "l"))) #() in
    do:  "sz" <-[uint64T] "$a0";;;
    return: ((![uint64T] "sz") - logLength);;;
    do:  #()).

(* Write to the disk through the log. *)
Definition Log__Write : val :=
  rec: "Log__Write" "l" "a" "v" :=
    exception_do (let: "l" := ref_ty Log "l" in
    let: "v" := ref_ty (sliceT byteT) "v" in
    let: "a" := ref_ty uint64T "a" in
    do:  (Log__lock (![Log] "l")) #();;;
    let: "length" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := ![uint64T] (![ptrT] (struct.field_ref Log "length" "l")) in
    do:  "length" <-[uint64T] "$a0";;;
    (if: (![uint64T] "length") ≥ MaxTxnWrites
    then
      do:  Panic "transaction is at capacity";;;
      do:  #()
    else do:  #());;;
    let: "aBlock" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := intToBlock (![uint64T] "a") in
    do:  "aBlock" <-[sliceT byteT] "$a0";;;
    let: "nextAddr" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := #1 + (#2 * (![uint64T] "length")) in
    do:  "nextAddr" <-[uint64T] "$a0";;;
    do:  (__Write (![disk.Disk] (struct.field_ref Log "d" "l"))) (![uint64T] "nextAddr") (![sliceT byteT] "aBlock");;;
    do:  (__Write (![disk.Disk] (struct.field_ref Log "d" "l"))) ((![uint64T] "nextAddr") + #1) (![sliceT byteT] "v");;;
    let: "$a0" := ![sliceT byteT] "v" in
    do:  map.insert (![mapT uint64T (sliceT byteT)] (struct.field_ref Log "cache" "l")) (![uint64T] "a") "$a0";;;
    let: "$a0" := (![uint64T] "length") + #1 in
    do:  (![ptrT] (struct.field_ref Log "length" "l")) <-[uint64T] "$a0";;;
    do:  (Log__unlock (![Log] "l")) #();;;
    do:  #()).

(* Commit the current transaction. *)
Definition Log__Commit : val :=
  rec: "Log__Commit" "l" :=
    exception_do (let: "l" := ref_ty Log "l" in
    do:  (Log__lock (![Log] "l")) #();;;
    let: "length" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := ![uint64T] (![ptrT] (struct.field_ref Log "length" "l")) in
    do:  "length" <-[uint64T] "$a0";;;
    do:  (Log__unlock (![Log] "l")) #();;;
    let: "header" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := intToBlock (![uint64T] "length") in
    do:  "header" <-[sliceT byteT] "$a0";;;
    do:  (__Write (![disk.Disk] (struct.field_ref Log "d" "l"))) #0 (![sliceT byteT] "header");;;
    do:  #()).

Definition getLogEntry : val :=
  rec: "getLogEntry" "d" "logOffset" :=
    exception_do (let: "logOffset" := ref_ty uint64T "logOffset" in
    let: "d" := ref_ty disk.Disk "d" in
    let: "diskAddr" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := #1 + (#2 * (![uint64T] "logOffset")) in
    do:  "diskAddr" <-[uint64T] "$a0";;;
    let: "aBlock" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := (__Read (![disk.Disk] "d")) (![uint64T] "diskAddr") in
    do:  "aBlock" <-[sliceT byteT] "$a0";;;
    let: "a" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := blockToInt (![sliceT byteT] "aBlock") in
    do:  "a" <-[uint64T] "$a0";;;
    let: "v" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := (__Read (![disk.Disk] "d")) ((![uint64T] "diskAddr") + #1) in
    do:  "v" <-[sliceT byteT] "$a0";;;
    return: (![uint64T] "a", ![sliceT byteT] "v");;;
    do:  #()).

(* applyLog assumes we are running sequentially *)
Definition applyLog : val :=
  rec: "applyLog" "d" "length" :=
    exception_do (let: "length" := ref_ty uint64T "length" in
    let: "d" := ref_ty disk.Disk "d" in
    (let: "i" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := #0 in
    do:  "i" <-[uint64T] "$a0";;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: (![uint64T] "i") < (![uint64T] "length")
      then
        let: "v" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
        let: "a" := ref_ty uint64T (zero_val uint64T) in
        let: ("$a0", "$a1") := getLogEntry (![disk.Disk] "d") (![uint64T] "i") in
        do:  "v" <-[sliceT byteT] "$a1";;;
        do:  "a" <-[uint64T] "$a0";;;
        do:  (__Write (![disk.Disk] "d")) (logLength + (![uint64T] "a")) (![sliceT byteT] "v");;;
        let: "$a0" := (![uint64T] "i") + #1 in
        do:  "i" <-[uint64T] "$a0";;;
        continue: #();;;
        do:  #()
      else do:  #());;;
      break: #();;;
      do:  #()));;;
    do:  #()).

Definition clearLog : val :=
  rec: "clearLog" "d" :=
    exception_do (let: "d" := ref_ty disk.Disk "d" in
    let: "header" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := intToBlock #0 in
    do:  "header" <-[sliceT byteT] "$a0";;;
    do:  (__Write (![disk.Disk] "d")) #0 (![sliceT byteT] "header");;;
    do:  #()).

(* Apply all the committed transactions.

   Frees all the space in the log. *)
Definition Log__Apply : val :=
  rec: "Log__Apply" "l" :=
    exception_do (let: "l" := ref_ty Log "l" in
    do:  (Log__lock (![Log] "l")) #();;;
    let: "length" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := ![uint64T] (![ptrT] (struct.field_ref Log "length" "l")) in
    do:  "length" <-[uint64T] "$a0";;;
    do:  applyLog (![disk.Disk] (struct.field_ref Log "d" "l")) (![uint64T] "length");;;
    do:  clearLog (![disk.Disk] (struct.field_ref Log "d" "l"));;;
    let: "$a0" := #0 in
    do:  (![ptrT] (struct.field_ref Log "length" "l")) <-[uint64T] "$a0";;;
    do:  (Log__unlock (![Log] "l")) #();;;
    do:  #()).

(* Open recovers the log following a crash or shutdown *)
Definition Open : val :=
  rec: "Open" <> :=
    exception_do (let: "d" := ref_ty disk.Disk (zero_val disk.Disk) in
    let: "$a0" := disk.Get #() in
    do:  "d" <-[disk.Disk] "$a0";;;
    let: "header" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := (__Read (![disk.Disk] "d")) #0 in
    do:  "header" <-[sliceT byteT] "$a0";;;
    let: "length" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := blockToInt (![sliceT byteT] "header") in
    do:  "length" <-[uint64T] "$a0";;;
    do:  applyLog (![disk.Disk] "d") (![uint64T] "length");;;
    do:  clearLog (![disk.Disk] "d");;;
    let: "cache" := ref_ty (mapT uint64T (sliceT byteT)) (zero_val (mapT uint64T (sliceT byteT))) in
    let: "$a0" := map.make uint64T (sliceT byteT) #() in
    do:  "cache" <-[mapT uint64T (sliceT byteT)] "$a0";;;
    let: "lengthPtr" := ref_ty ptrT (zero_val ptrT) in
    let: "$a0" := ref_ty uint64T (zero_val uint64T) in
    do:  "lengthPtr" <-[ptrT] "$a0";;;
    let: "$a0" := #0 in
    do:  (![ptrT] "lengthPtr") <-[uint64T] "$a0";;;
    let: "l" := ref_ty ptrT (zero_val ptrT) in
    let: "$a0" := ref_ty sync.Mutex (zero_val sync.Mutex) in
    do:  "l" <-[ptrT] "$a0";;;
    return: (struct.make Log {[
       #(str "d") := ![disk.Disk] "d";
       #(str "cache") := ![mapT uint64T (sliceT byteT)] "cache";
       #(str "length") := ![ptrT] "lengthPtr";
       #(str "l") := ![ptrT] "l"
     ]});;;
    do:  #()).

(* autogenerated from github.com/goose-lang/goose/testdata/examples/logging2 *)
From New.golang Require Import defn.
Require Import New.code.github_com.goose_lang.primitive.
Require Import New.code.github_com.goose_lang.primitive.disk.
Require Import New.code.sync.

From New Require Import disk_prelude.
Module logging2.
Section code.


Definition LOGCOMMIT : expr := #(W64 0).

Definition LOGSTART : expr := #(W64 1).

Definition LOGMAXBLK : expr := #(W64 510).

Definition LOGEND : expr := LOGMAXBLK + LOGSTART.

Definition Log : go_type := structT [
  "logLock" :: ptrT;
  "memLock" :: ptrT;
  "logSz" :: uint64T;
  "memLog" :: ptrT;
  "memLen" :: ptrT;
  "memTxnNxt" :: ptrT;
  "logTxnNxt" :: ptrT
].

(* go: logging2.go:25:16 *)
Definition Log__writeHdr : val :=
  rec: "Log__writeHdr" "log" "len" :=
    exception_do (let: "log" := (ref_ty Log "log") in
    let: "len" := (ref_ty uint64T "len") in
    let: "hdr" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (slice.make2 byteT #(W64 4096)) in
    do:  ("hdr" <-[sliceT] "$r0");;;
    do:  (let: "$a0" := (![sliceT] "hdr") in
    let: "$a1" := (![uint64T] "len") in
    (func_call #primitive.pkg_name' #"UInt64Put"%go) "$a0" "$a1");;;
    do:  (let: "$a0" := LOGCOMMIT in
    let: "$a1" := (![sliceT] "hdr") in
    (func_call #disk.pkg_name' #"Write"%go) "$a0" "$a1")).

Definition pkg_name' : go_string := "github.com/goose-lang/goose/testdata/examples/logging2".

(* go: logging2.go:31:6 *)
Definition Init : val :=
  rec: "Init" "logSz" :=
    exception_do (let: "logSz" := (ref_ty uint64T "logSz") in
    let: "log" := (ref_ty Log (zero_val Log)) in
    let: "$r0" := (let: "$logLock" := (ref_ty sync.Mutex (zero_val sync.Mutex)) in
    let: "$memLock" := (ref_ty sync.Mutex (zero_val sync.Mutex)) in
    let: "$logSz" := (![uint64T] "logSz") in
    let: "$memLog" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$memLen" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$memTxnNxt" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$logTxnNxt" := (ref_ty uint64T (zero_val uint64T)) in
    struct.make Log [{
      "logLock" ::= "$logLock";
      "memLock" ::= "$memLock";
      "logSz" ::= "$logSz";
      "memLog" ::= "$memLog";
      "memLen" ::= "$memLen";
      "memTxnNxt" ::= "$memTxnNxt";
      "logTxnNxt" ::= "$logTxnNxt"
    }]) in
    do:  ("log" <-[Log] "$r0");;;
    do:  (let: "$a0" := #(W64 0) in
    (method_call #pkg_name' #"Log" #"writeHdr" (![Log] "log")) "$a0");;;
    return: (![Log] "log")).

(* go: logging2.go:45:16 *)
Definition Log__readHdr : val :=
  rec: "Log__readHdr" "log" <> :=
    exception_do (let: "log" := (ref_ty Log "log") in
    let: "hdr" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (let: "$a0" := LOGCOMMIT in
    (func_call #disk.pkg_name' #"Read"%go) "$a0") in
    do:  ("hdr" <-[sliceT] "$r0");;;
    let: "disklen" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (let: "$a0" := (![sliceT] "hdr") in
    (func_call #primitive.pkg_name' #"UInt64Get"%go) "$a0") in
    do:  ("disklen" <-[uint64T] "$r0");;;
    return: (![uint64T] "disklen")).

(* go: logging2.go:51:16 *)
Definition Log__readBlocks : val :=
  rec: "Log__readBlocks" "log" "len" :=
    exception_do (let: "log" := (ref_ty Log "log") in
    let: "len" := (ref_ty uint64T "len") in
    let: "blks" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (slice.make2 sliceT #(W64 0)) in
    do:  ("blks" <-[sliceT] "$r0");;;
    (let: "i" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := #(W64 0) in
    do:  ("i" <-[uint64T] "$r0");;;
    (for: (λ: <>, (![uint64T] "i") < (![uint64T] "len")); (λ: <>, do:  ("i" <-[uint64T] ((![uint64T] "i") + #(W64 1)))) := λ: <>,
      let: "blk" := (ref_ty sliceT (zero_val sliceT)) in
      let: "$r0" := (let: "$a0" := (LOGSTART + (![uint64T] "i")) in
      (func_call #disk.pkg_name' #"Read"%go) "$a0") in
      do:  ("blk" <-[sliceT] "$r0");;;
      let: "$r0" := (let: "$a0" := (![sliceT] "blks") in
      let: "$a1" := ((let: "$sl0" := (![sliceT] "blk") in
      slice.literal sliceT ["$sl0"])) in
      (slice.append sliceT) "$a0" "$a1") in
      do:  ("blks" <-[sliceT] "$r0")));;;
    return: (![sliceT] "blks")).

(* go: logging2.go:60:16 *)
Definition Log__Read : val :=
  rec: "Log__Read" "log" <> :=
    exception_do (let: "log" := (ref_ty Log "log") in
    do:  ((method_call #sync.pkg_name' #"Mutex'ptr" #"Lock" (![ptrT] (struct.field_ref Log "logLock" "log"))) #());;;
    let: "disklen" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := ((method_call #pkg_name' #"Log" #"readHdr" (![Log] "log")) #()) in
    do:  ("disklen" <-[uint64T] "$r0");;;
    let: "blks" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (let: "$a0" := (![uint64T] "disklen") in
    (method_call #pkg_name' #"Log" #"readBlocks" (![Log] "log")) "$a0") in
    do:  ("blks" <-[sliceT] "$r0");;;
    do:  ((method_call #sync.pkg_name' #"Mutex'ptr" #"Unlock" (![ptrT] (struct.field_ref Log "logLock" "log"))) #());;;
    return: (![sliceT] "blks")).

(* go: logging2.go:68:16 *)
Definition Log__memWrite : val :=
  rec: "Log__memWrite" "log" "l" :=
    exception_do (let: "log" := (ref_ty Log "log") in
    let: "l" := (ref_ty sliceT "l") in
    let: "n" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (let: "$a0" := (![sliceT] "l") in
    slice.len "$a0") in
    do:  ("n" <-[uint64T] "$r0");;;
    (let: "i" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := #(W64 0) in
    do:  ("i" <-[uint64T] "$r0");;;
    (for: (λ: <>, (![uint64T] "i") < (![uint64T] "n")); (λ: <>, do:  ("i" <-[uint64T] ((![uint64T] "i") + #(W64 1)))) := λ: <>,
      let: "$r0" := (let: "$a0" := (![sliceT] (![ptrT] (struct.field_ref Log "memLog" "log"))) in
      let: "$a1" := ((let: "$sl0" := (![sliceT] (slice.elem_ref sliceT (![sliceT] "l") (![uint64T] "i"))) in
      slice.literal sliceT ["$sl0"])) in
      (slice.append sliceT) "$a0" "$a1") in
      do:  ((![ptrT] (struct.field_ref Log "memLog" "log")) <-[sliceT] "$r0")))).

(* go: logging2.go:75:16 *)
Definition Log__memAppend : val :=
  rec: "Log__memAppend" "log" "l" :=
    exception_do (let: "log" := (ref_ty Log "log") in
    let: "l" := (ref_ty sliceT "l") in
    do:  ((method_call #sync.pkg_name' #"Mutex'ptr" #"Lock" (![ptrT] (struct.field_ref Log "memLock" "log"))) #());;;
    (if: ((![uint64T] (![ptrT] (struct.field_ref Log "memLen" "log"))) + (let: "$a0" := (![sliceT] "l") in
    slice.len "$a0")) ≥ (![uint64T] (struct.field_ref Log "logSz" "log"))
    then
      do:  ((method_call #sync.pkg_name' #"Mutex'ptr" #"Unlock" (![ptrT] (struct.field_ref Log "memLock" "log"))) #());;;
      return: (#false, #(W64 0))
    else do:  #());;;
    let: "txn" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (![uint64T] (![ptrT] (struct.field_ref Log "memTxnNxt" "log"))) in
    do:  ("txn" <-[uint64T] "$r0");;;
    let: "n" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := ((![uint64T] (![ptrT] (struct.field_ref Log "memLen" "log"))) + (let: "$a0" := (![sliceT] "l") in
    slice.len "$a0")) in
    do:  ("n" <-[uint64T] "$r0");;;
    let: "$r0" := (![uint64T] "n") in
    do:  ((![ptrT] (struct.field_ref Log "memLen" "log")) <-[uint64T] "$r0");;;
    let: "$r0" := ((![uint64T] (![ptrT] (struct.field_ref Log "memTxnNxt" "log"))) + #(W64 1)) in
    do:  ((![ptrT] (struct.field_ref Log "memTxnNxt" "log")) <-[uint64T] "$r0");;;
    do:  ((method_call #sync.pkg_name' #"Mutex'ptr" #"Unlock" (![ptrT] (struct.field_ref Log "memLock" "log"))) #());;;
    return: (#true, ![uint64T] "txn")).

(* XXX just an atomic read?

   go: logging2.go:90:16 *)
Definition Log__readLogTxnNxt : val :=
  rec: "Log__readLogTxnNxt" "log" <> :=
    exception_do (let: "log" := (ref_ty Log "log") in
    do:  ((method_call #sync.pkg_name' #"Mutex'ptr" #"Lock" (![ptrT] (struct.field_ref Log "memLock" "log"))) #());;;
    let: "n" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (![uint64T] (![ptrT] (struct.field_ref Log "logTxnNxt" "log"))) in
    do:  ("n" <-[uint64T] "$r0");;;
    do:  ((method_call #sync.pkg_name' #"Mutex'ptr" #"Unlock" (![ptrT] (struct.field_ref Log "memLock" "log"))) #());;;
    return: (![uint64T] "n")).

(* go: logging2.go:97:16 *)
Definition Log__diskAppendWait : val :=
  rec: "Log__diskAppendWait" "log" "txn" :=
    exception_do (let: "log" := (ref_ty Log "log") in
    let: "txn" := (ref_ty uint64T "txn") in
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "logtxn" := (ref_ty uint64T (zero_val uint64T)) in
      let: "$r0" := ((method_call #pkg_name' #"Log" #"readLogTxnNxt" (![Log] "log")) #()) in
      do:  ("logtxn" <-[uint64T] "$r0");;;
      (if: (![uint64T] "txn") < (![uint64T] "logtxn")
      then break: #()
      else do:  #());;;
      continue: #())).

(* go: logging2.go:107:16 *)
Definition Log__Append : val :=
  rec: "Log__Append" "log" "l" :=
    exception_do (let: "log" := (ref_ty Log "log") in
    let: "l" := (ref_ty sliceT "l") in
    let: "txn" := (ref_ty uint64T (zero_val uint64T)) in
    let: "ok" := (ref_ty boolT (zero_val boolT)) in
    let: ("$ret0", "$ret1") := (let: "$a0" := (![sliceT] "l") in
    (method_call #pkg_name' #"Log" #"memAppend" (![Log] "log")) "$a0") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("ok" <-[boolT] "$r0");;;
    do:  ("txn" <-[uint64T] "$r1");;;
    (if: ![boolT] "ok"
    then
      do:  (let: "$a0" := (![uint64T] "txn") in
      (method_call #pkg_name' #"Log" #"diskAppendWait" (![Log] "log")) "$a0")
    else do:  #());;;
    return: (![boolT] "ok")).

(* go: logging2.go:115:16 *)
Definition Log__writeBlocks : val :=
  rec: "Log__writeBlocks" "log" "l" "pos" :=
    exception_do (let: "log" := (ref_ty Log "log") in
    let: "pos" := (ref_ty uint64T "pos") in
    let: "l" := (ref_ty sliceT "l") in
    let: "n" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (let: "$a0" := (![sliceT] "l") in
    slice.len "$a0") in
    do:  ("n" <-[uint64T] "$r0");;;
    (let: "i" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := #(W64 0) in
    do:  ("i" <-[uint64T] "$r0");;;
    (for: (λ: <>, (![uint64T] "i") < (![uint64T] "n")); (λ: <>, do:  ("i" <-[uint64T] ((![uint64T] "i") + #(W64 1)))) := λ: <>,
      let: "bk" := (ref_ty sliceT (zero_val sliceT)) in
      let: "$r0" := (![sliceT] (slice.elem_ref sliceT (![sliceT] "l") (![uint64T] "i"))) in
      do:  ("bk" <-[sliceT] "$r0");;;
      do:  (let: "$a0" := ((![uint64T] "pos") + (![uint64T] "i")) in
      let: "$a1" := (![sliceT] "bk") in
      (func_call #disk.pkg_name' #"Write"%go) "$a0" "$a1")))).

(* go: logging2.go:123:16 *)
Definition Log__diskAppend : val :=
  rec: "Log__diskAppend" "log" <> :=
    exception_do (let: "log" := (ref_ty Log "log") in
    do:  ((method_call #sync.pkg_name' #"Mutex'ptr" #"Lock" (![ptrT] (struct.field_ref Log "logLock" "log"))) #());;;
    let: "disklen" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := ((method_call #pkg_name' #"Log" #"readHdr" (![Log] "log")) #()) in
    do:  ("disklen" <-[uint64T] "$r0");;;
    do:  ((method_call #sync.pkg_name' #"Mutex'ptr" #"Lock" (![ptrT] (struct.field_ref Log "memLock" "log"))) #());;;
    let: "memlen" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (![uint64T] (![ptrT] (struct.field_ref Log "memLen" "log"))) in
    do:  ("memlen" <-[uint64T] "$r0");;;
    let: "allblks" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (![sliceT] (![ptrT] (struct.field_ref Log "memLog" "log"))) in
    do:  ("allblks" <-[sliceT] "$r0");;;
    let: "blks" := (ref_ty sliceT (zero_val sliceT)) in
    let: "$r0" := (let: "$s" := (![sliceT] "allblks") in
    slice.slice sliceT "$s" (![uint64T] "disklen") (slice.len "$s")) in
    do:  ("blks" <-[sliceT] "$r0");;;
    let: "memnxt" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (![uint64T] (![ptrT] (struct.field_ref Log "memTxnNxt" "log"))) in
    do:  ("memnxt" <-[uint64T] "$r0");;;
    do:  ((method_call #sync.pkg_name' #"Mutex'ptr" #"Unlock" (![ptrT] (struct.field_ref Log "memLock" "log"))) #());;;
    do:  (let: "$a0" := (![sliceT] "blks") in
    let: "$a1" := (![uint64T] "disklen") in
    (method_call #pkg_name' #"Log" #"writeBlocks" (![Log] "log")) "$a0" "$a1");;;
    do:  (let: "$a0" := (![uint64T] "memlen") in
    (method_call #pkg_name' #"Log" #"writeHdr" (![Log] "log")) "$a0");;;
    let: "$r0" := (![uint64T] "memnxt") in
    do:  ((![ptrT] (struct.field_ref Log "logTxnNxt" "log")) <-[uint64T] "$r0");;;
    do:  ((method_call #sync.pkg_name' #"Mutex'ptr" #"Unlock" (![ptrT] (struct.field_ref Log "logLock" "log"))) #())).

(* go: logging2.go:142:16 *)
Definition Log__Logger : val :=
  rec: "Log__Logger" "log" <> :=
    exception_do (let: "log" := (ref_ty Log "log") in
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      do:  ((method_call #pkg_name' #"Log" #"diskAppend" (![Log] "log")) #()))).

Definition Txn : go_type := structT [
  "log" :: ptrT;
  "blks" :: mapT uint64T sliceT
].

(* XXX wait if cannot reserve space in log

   go: txn.go:13:6 *)
Definition Begin : val :=
  rec: "Begin" "log" :=
    exception_do (let: "log" := (ref_ty ptrT "log") in
    let: "txn" := (ref_ty Txn (zero_val Txn)) in
    let: "$r0" := (let: "$log" := (![ptrT] "log") in
    let: "$blks" := (map.make uint64T sliceT #()) in
    struct.make Txn [{
      "log" ::= "$log";
      "blks" ::= "$blks"
    }]) in
    do:  ("txn" <-[Txn] "$r0");;;
    return: (![Txn] "txn")).

(* go: txn.go:21:16 *)
Definition Txn__Write : val :=
  rec: "Txn__Write" "txn" "addr" "blk" :=
    exception_do (let: "txn" := (ref_ty Txn "txn") in
    let: "blk" := (ref_ty ptrT "blk") in
    let: "addr" := (ref_ty uint64T "addr") in
    let: "ret" := (ref_ty boolT (zero_val boolT)) in
    let: "$r0" := #true in
    do:  ("ret" <-[boolT] "$r0");;;
    let: "ok" := (ref_ty boolT (zero_val boolT)) in
    let: ("$ret0", "$ret1") := (map.get (![mapT uint64T sliceT] (struct.field_ref Txn "blks" "txn")) (![uint64T] "addr")) in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  "$r0";;;
    do:  ("ok" <-[boolT] "$r1");;;
    (if: ![boolT] "ok"
    then
      let: "$r0" := (![sliceT] (![ptrT] "blk")) in
      do:  (map.insert (![mapT uint64T sliceT] (struct.field_ref Txn "blks" "txn")) (![uint64T] "addr") "$r0")
    else do:  #());;;
    (if: (~ (![boolT] "ok"))
    then
      (if: (![uint64T] "addr") = LOGMAXBLK
      then
        let: "$r0" := #false in
        do:  ("ret" <-[boolT] "$r0")
      else
        let: "$r0" := (![sliceT] (![ptrT] "blk")) in
        do:  (map.insert (![mapT uint64T sliceT] (struct.field_ref Txn "blks" "txn")) (![uint64T] "addr") "$r0"))
    else do:  #());;;
    return: (![boolT] "ret")).

(* go: txn.go:38:16 *)
Definition Txn__Read : val :=
  rec: "Txn__Read" "txn" "addr" :=
    exception_do (let: "txn" := (ref_ty Txn "txn") in
    let: "addr" := (ref_ty uint64T "addr") in
    let: "ok" := (ref_ty boolT (zero_val boolT)) in
    let: "v" := (ref_ty sliceT (zero_val sliceT)) in
    let: ("$ret0", "$ret1") := (map.get (![mapT uint64T sliceT] (struct.field_ref Txn "blks" "txn")) (![uint64T] "addr")) in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("v" <-[sliceT] "$r0");;;
    do:  ("ok" <-[boolT] "$r1");;;
    (if: ![boolT] "ok"
    then return: (![sliceT] "v")
    else
      return: (let: "$a0" := ((![uint64T] "addr") + LOGEND) in
       (func_call #disk.pkg_name' #"Read"%go) "$a0"))).

(* go: txn.go:47:16 *)
Definition Txn__Commit : val :=
  rec: "Txn__Commit" "txn" <> :=
    exception_do (let: "txn" := (ref_ty Txn "txn") in
    let: "blks" := (ref_ty ptrT (zero_val ptrT)) in
    let: "$r0" := (ref_ty sliceT (zero_val sliceT)) in
    do:  ("blks" <-[ptrT] "$r0");;;
    (let: "v" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$range" := (![mapT uint64T sliceT] (struct.field_ref Txn "blks" "txn")) in
    map.for_range "$range" (λ: "$key" "value",
      do:  ("v" <-[sliceT] "$value");;;
      do:  "$key";;;
      let: "$r0" := (let: "$a0" := (![sliceT] (![ptrT] "blks")) in
      let: "$a1" := ((let: "$sl0" := (![sliceT] "v") in
      slice.literal sliceT ["$sl0"])) in
      (slice.append sliceT) "$a0" "$a1") in
      do:  ((![ptrT] "blks") <-[sliceT] "$r0")));;;
    let: "ok" := (ref_ty boolT (zero_val boolT)) in
    let: "$r0" := (let: "$a0" := (![sliceT] (![ptrT] "blks")) in
    (method_call #pkg_name' #"Log" #"Append" (![Log] (![ptrT] (struct.field_ref Txn "log" "txn")))) "$a0") in
    do:  ("ok" <-[boolT] "$r0");;;
    return: (![boolT] "ok")).

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [("Init"%go, Init); ("Begin"%go, Begin)].

Definition msets' : list (go_string * (list (go_string * val))) := [("Log"%go, [("Append"%go, Log__Append); ("Logger"%go, Log__Logger); ("Read"%go, Log__Read); ("diskAppend"%go, Log__diskAppend); ("diskAppendWait"%go, Log__diskAppendWait); ("memAppend"%go, Log__memAppend); ("memWrite"%go, Log__memWrite); ("readBlocks"%go, Log__readBlocks); ("readHdr"%go, Log__readHdr); ("readLogTxnNxt"%go, Log__readLogTxnNxt); ("writeBlocks"%go, Log__writeBlocks); ("writeHdr"%go, Log__writeHdr)]); ("Log'ptr"%go, [("Append"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"Log" #"Append" (![Log] "$recvAddr")
                 )%V); ("Logger"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"Log" #"Logger" (![Log] "$recvAddr")
                 )%V); ("Read"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"Log" #"Read" (![Log] "$recvAddr")
                 )%V); ("diskAppend"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"Log" #"diskAppend" (![Log] "$recvAddr")
                 )%V); ("diskAppendWait"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"Log" #"diskAppendWait" (![Log] "$recvAddr")
                 )%V); ("memAppend"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"Log" #"memAppend" (![Log] "$recvAddr")
                 )%V); ("memWrite"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"Log" #"memWrite" (![Log] "$recvAddr")
                 )%V); ("readBlocks"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"Log" #"readBlocks" (![Log] "$recvAddr")
                 )%V); ("readHdr"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"Log" #"readHdr" (![Log] "$recvAddr")
                 )%V); ("readLogTxnNxt"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"Log" #"readLogTxnNxt" (![Log] "$recvAddr")
                 )%V); ("writeBlocks"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"Log" #"writeBlocks" (![Log] "$recvAddr")
                 )%V); ("writeHdr"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"Log" #"writeHdr" (![Log] "$recvAddr")
                 )%V)]); ("Txn"%go, [("Commit"%go, Txn__Commit); ("Read"%go, Txn__Read); ("Write"%go, Txn__Write)]); ("Txn'ptr"%go, [("Commit"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"Txn" #"Commit" (![Txn] "$recvAddr")
                 )%V); ("Read"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"Txn" #"Read" (![Txn] "$recvAddr")
                 )%V); ("Write"%go, (λ: "$recvAddr",
                 method_call #pkg_name' #"Txn" #"Write" (![Txn] "$recvAddr")
                 )%V)])].

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init pkg_name' vars' functions' msets' (λ: <>,
      exception_do (do:  sync.initialize';;;
      do:  disk.initialize';;;
      do:  primitive.initialize')
      ).

End code.
End logging2.

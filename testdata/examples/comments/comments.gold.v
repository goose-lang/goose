(* autogenerated from github.com/goose-lang/goose/testdata/examples/comments *)
From New.golang Require Import defn.

Module comments.
Section code.
Context `{ffi_syntax}.


Definition ONE : expr := #(W64 1).

Definition TWO : expr := #(W64 2).

Definition Foo : go_type := structT [
  "a" :: boolT
].

Definition pkg_name' : go_string := "github.com/goose-lang/goose/testdata/examples/comments".

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [].

Definition msets' : list (go_string * (list (go_string * val))) := [("Foo"%go, []); ("Foo'ptr"%go, [])].

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init pkg_name' vars' functions' msets' (λ: <>,
      exception_do (do:  #())
      ).

End code.
End comments.

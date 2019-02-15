From RecoveryRefinement Require Import Database.CodeSetup.

Definition Empty  : proc unit :=
  Ret tt.

Definition EmptyReturn  : proc unit :=
  Ret tt.

Definition DoSomeLocking (l:LockRef) : proc unit :=
  _ <- Data.lockAcquire Writer l;
  _ <- Data.lockRelease Writer l;
  _ <- Data.lockAcquire Reader l;
  _ <- Data.lockAcquire Reader l;
  _ <- Data.lockRelease Reader l;
  Data.lockRelease Reader l.

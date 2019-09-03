def cltd1 : instruction :=
  definst "cltd" $ do
    pattern fun => do
      v_7101 <- getRegister rax;
      setRegister edx (extract (leanSignExtend (extract v_7101 32 64) 64) 0 32);
      pure ()
    pat_end

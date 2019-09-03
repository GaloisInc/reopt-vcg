def cltq1 : instruction :=
  definst "cltq" $ do
    pattern fun => do
      v_7106 <- getRegister rax;
      setRegister rax (leanSignExtend (extract v_7106 32 64) 64);
      pure ()
    pat_end

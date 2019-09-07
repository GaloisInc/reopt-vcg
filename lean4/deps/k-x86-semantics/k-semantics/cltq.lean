def cltq1 : instruction :=
  definst "cltq" $ do
    pattern fun => do
      v_0 <- getRegister rax;
      setRegister rax (sext (extract v_0 32 64) 64);
      pure ()
    pat_end

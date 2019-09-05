def cltq1 : instruction :=
  definst "cltq" $ do
    pattern fun => do
      v_6805 <- getRegister rax;
      setRegister rax (sext (extract v_6805 32 64) 64);
      pure ()
    pat_end

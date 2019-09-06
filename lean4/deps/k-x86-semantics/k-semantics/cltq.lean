def cltq1 : instruction :=
  definst "cltq" $ do
    pattern fun => do
      v_6686 <- getRegister rax;
      setRegister rax (sext (extract v_6686 32 64) 64);
      pure ()
    pat_end

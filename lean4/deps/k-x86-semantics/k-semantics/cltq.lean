def cltq : instruction :=
  definst "cltq" $ do
    pattern do
      v_0 <- getRegister rax;
      setRegister rax (sext (extract v_0 32 64) 64);
      pure ()
    pat_end

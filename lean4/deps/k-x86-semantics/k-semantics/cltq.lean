def cltq : instruction :=
  definst "cltq" $ do
    pattern do
      v_0 <- getRegister rax;
      (v_1 : expression (bv 32)) <- eval (extract v_0 32 64);
      setRegister rax (sext v_1 64);
      pure ()
    pat_end

def cltq1 : instruction :=
  definst "cltq" $ do
    pattern fun => do
      v_6965 <- getRegister rax;
      setRegister rax (mi 64 (svalueMInt (extract v_6965 32 64)));
      pure ()
    pat_end

def cwtl1 : instruction :=
  definst "cwtl" $ do
    pattern fun => do
      v_4351 <- getRegister rax;
      setRegister eax (mi 32 (svalueMInt (extract v_4351 48 64)));
      pure ()
    pat_end

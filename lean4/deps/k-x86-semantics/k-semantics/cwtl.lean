def cwtl1 : instruction :=
  definst "cwtl" $ do
    pattern fun => do
      v_4360 <- getRegister rax;
      setRegister eax (sext (extract v_4360 48 64) 32);
      pure ()
    pat_end

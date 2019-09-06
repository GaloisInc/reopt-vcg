def cwtl1 : instruction :=
  definst "cwtl" $ do
    pattern fun => do
      v_4381 <- getRegister rax;
      setRegister eax (sext (extract v_4381 48 64) 32);
      pure ()
    pat_end

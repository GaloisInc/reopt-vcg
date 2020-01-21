def cwtl : instruction :=
  definst "cwtl" $ do
    pattern fun => do
      v_0 <- getRegister rax;
      setRegister eax (sext (extract v_0 48 64) 32);
      pure ()
    pat_end

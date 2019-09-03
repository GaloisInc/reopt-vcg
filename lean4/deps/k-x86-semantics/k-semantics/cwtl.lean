def cwtl1 : instruction :=
  definst "cwtl" $ do
    pattern fun => do
      v_4372 <- getRegister rax;
      setRegister eax (leanSignExtend (extract v_4372 48 64) 32);
      pure ()
    pat_end

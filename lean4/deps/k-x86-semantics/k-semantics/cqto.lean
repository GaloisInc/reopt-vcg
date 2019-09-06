def cqto1 : instruction :=
  definst "cqto" $ do
    pattern fun => do
      v_4094 <- getRegister rax;
      setRegister rdx (extract (sext v_4094 128) 0 64);
      pure ()
    pat_end

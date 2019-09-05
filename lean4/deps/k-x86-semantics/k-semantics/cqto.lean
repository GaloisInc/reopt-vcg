def cqto1 : instruction :=
  definst "cqto" $ do
    pattern fun => do
      v_4073 <- getRegister rax;
      setRegister rdx (extract (sext v_4073 128) 0 64);
      pure ()
    pat_end

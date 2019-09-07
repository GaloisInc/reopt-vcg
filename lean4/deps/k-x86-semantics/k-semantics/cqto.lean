def cqto1 : instruction :=
  definst "cqto" $ do
    pattern fun => do
      v_0 <- getRegister rax;
      setRegister rdx (extract (sext v_0 128) 0 64);
      pure ()
    pat_end

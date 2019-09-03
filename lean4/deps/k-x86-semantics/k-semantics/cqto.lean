def cqto1 : instruction :=
  definst "cqto" $ do
    pattern fun => do
      v_4049 <- getRegister rax;
      setRegister rdx (extract (leanSignExtend v_4049 128) 0 64);
      pure ()
    pat_end

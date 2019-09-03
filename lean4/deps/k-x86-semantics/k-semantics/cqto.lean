def cqto1 : instruction :=
  definst "cqto" $ do
    pattern fun => do
      v_4062 <- getRegister rax;
      setRegister rdx (extract (mi 128 (svalueMInt v_4062)) 0 64);
      pure ()
    pat_end

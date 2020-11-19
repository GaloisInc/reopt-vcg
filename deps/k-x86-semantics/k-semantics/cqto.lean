def cqto : instruction :=
  definst "cqto" $ do
    pattern do
      v_0 <- getRegister rax;
      (v_1 : expression (bv 64)) <- eval (extract (sext v_0 128) 0 64);
      setRegister rdx v_1;
      pure ()
    pat_end

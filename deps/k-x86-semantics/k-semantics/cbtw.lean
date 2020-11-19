def cbtw : instruction :=
  definst "cbtw" $ do
    pattern do
      v_0 <- getRegister rax;
      (v_1 : expression (bv 48)) <- eval (extract v_0 0 48);
      (v_2 : expression (bv 8)) <- eval (extract v_0 56 64);
      setRegister rax (concat v_1 (sext v_2 16));
      pure ()
    pat_end

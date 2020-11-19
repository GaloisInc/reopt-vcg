def cwtl : instruction :=
  definst "cwtl" $ do
    pattern do
      v_0 <- getRegister rax;
      (v_1 : expression (bv 16)) <- eval (extract v_0 48 64);
      setRegister eax (sext v_1 32);
      pure ()
    pat_end

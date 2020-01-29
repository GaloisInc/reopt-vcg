def cwtd : instruction :=
  definst "cwtd" $ do
    pattern do
      v_0 <- getRegister rdx;
      (v_1 : expression (bv 48)) <- eval (extract v_0 0 48);
      v_2 <- getRegister rax;
      (v_3 : expression (bv 16)) <- eval (extract v_2 48 64);
      (v_4 : expression (bv 16)) <- eval (extract (sext v_3 32) 0 16);
      setRegister rdx (concat v_1 v_4);
      pure ()
    pat_end

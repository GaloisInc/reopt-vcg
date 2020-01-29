def cltd : instruction :=
  definst "cltd" $ do
    pattern do
      v_0 <- getRegister rax;
      (v_1 : expression (bv 32)) <- eval (extract v_0 32 64);
      (v_2 : expression (bv 32)) <- eval (extract (sext v_1 64) 0 32);
      setRegister edx v_2;
      pure ()
    pat_end

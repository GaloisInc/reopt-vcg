def cwtd : instruction :=
  definst "cwtd" $ do
    pattern do
      v_0 <- getRegister rdx;
      v_1 <- getRegister rax;
      setRegister rdx (concat (extract v_0 0 48) (extract (sext (extract v_1 48 64) 32) 0 16));
      pure ()
    pat_end

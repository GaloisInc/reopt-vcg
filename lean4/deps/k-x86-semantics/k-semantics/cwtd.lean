def cwtd1 : instruction :=
  definst "cwtd" $ do
    pattern fun => do
      v_4352 <- getRegister rdx;
      v_4354 <- getRegister rax;
      setRegister rdx (concat (extract v_4352 0 48) (extract (sext (extract v_4354 48 64) 32) 0 16));
      pure ()
    pat_end

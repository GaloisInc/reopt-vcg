def cltd : instruction :=
  definst "cltd" $ do
    pattern fun => do
      v_0 <- getRegister rax;
      setRegister edx (extract (sext (extract v_0 32 64) 64) 0 32);
      pure ()
    pat_end

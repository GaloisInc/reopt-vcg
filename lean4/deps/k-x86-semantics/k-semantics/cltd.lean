def cltd1 : instruction :=
  definst "cltd" $ do
    pattern fun => do
      v_6959 <- getRegister rax;
      setRegister edx (extract (mi 64 (svalueMInt (extract v_6959 32 64))) 0 32);
      pure ()
    pat_end

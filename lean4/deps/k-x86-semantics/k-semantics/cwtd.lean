def cwtd1 : instruction :=
  definst "cwtd" $ do
    pattern fun => do
      v_4342 <- getRegister rdx;
      v_4344 <- getRegister rax;
      setRegister rdx (concat (extract v_4342 0 48) (extract (mi 32 (svalueMInt (extract v_4344 48 64))) 0 16));
      pure ()
    pat_end

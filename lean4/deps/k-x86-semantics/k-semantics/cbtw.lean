def cbtw1 : instruction :=
  definst "cbtw" $ do
    pattern fun => do
      v_6950 <- getRegister rax;
      setRegister rax (concat (extract v_6950 0 48) (mi 16 (svalueMInt (extract v_6950 56 64))));
      pure ()
    pat_end

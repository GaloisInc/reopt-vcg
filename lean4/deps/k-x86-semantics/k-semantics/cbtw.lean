def cbtw1 : instruction :=
  definst "cbtw" $ do
    pattern fun => do
      v_0 <- getRegister rax;
      setRegister rax (concat (extract v_0 0 48) (sext (extract v_0 56 64) 16));
      pure ()
    pat_end

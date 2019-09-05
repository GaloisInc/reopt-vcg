def cbtw1 : instruction :=
  definst "cbtw" $ do
    pattern fun => do
      v_6792 <- getRegister rax;
      setRegister rax (concat (extract v_6792 0 48) (sext (extract v_6792 56 64) 16));
      pure ()
    pat_end

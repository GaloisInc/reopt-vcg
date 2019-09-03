def cbtw1 : instruction :=
  definst "cbtw" $ do
    pattern fun => do
      v_7093 <- getRegister rax;
      setRegister rax (concat (extract v_7093 0 48) (leanSignExtend (extract v_7093 56 64) 16));
      pure ()
    pat_end

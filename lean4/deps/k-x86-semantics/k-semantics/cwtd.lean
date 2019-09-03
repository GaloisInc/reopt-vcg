def cwtd1 : instruction :=
  definst "cwtd" $ do
    pattern fun => do
      v_4364 <- getRegister rdx;
      v_4366 <- getRegister rax;
      setRegister rdx (concat (extract v_4364 0 48) (extract (leanSignExtend (extract v_4366 48 64) 32) 0 16));
      pure ()
    pat_end

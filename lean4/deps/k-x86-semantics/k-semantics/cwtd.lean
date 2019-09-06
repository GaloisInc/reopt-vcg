def cwtd1 : instruction :=
  definst "cwtd" $ do
    pattern fun => do
      v_4373 <- getRegister rdx;
      v_4375 <- getRegister rax;
      setRegister rdx (concat (extract v_4373 0 48) (extract (sext (extract v_4375 48 64) 32) 0 16));
      pure ()
    pat_end

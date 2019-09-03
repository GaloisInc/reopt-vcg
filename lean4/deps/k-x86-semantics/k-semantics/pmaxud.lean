def pmaxud1 : instruction :=
  definst "pmaxud" $ do
    pattern fun (v_2598 : reg (bv 128)) (v_2599 : reg (bv 128)) => do
      v_4945 <- getRegister v_2599;
      v_4946 <- eval (extract v_4945 0 32);
      v_4947 <- getRegister v_2598;
      v_4948 <- eval (extract v_4947 0 32);
      v_4951 <- eval (extract v_4945 32 64);
      v_4952 <- eval (extract v_4947 32 64);
      v_4955 <- eval (extract v_4945 64 96);
      v_4956 <- eval (extract v_4947 64 96);
      v_4959 <- eval (extract v_4945 96 128);
      v_4960 <- eval (extract v_4947 96 128);
      setRegister (lhs.of_reg v_2599) (concat (mux (ugt v_4946 v_4948) v_4946 v_4948) (concat (mux (ugt v_4951 v_4952) v_4951 v_4952) (concat (mux (ugt v_4955 v_4956) v_4955 v_4956) (mux (ugt v_4959 v_4960) v_4959 v_4960))));
      pure ()
    pat_end;
    pattern fun (v_2594 : Mem) (v_2595 : reg (bv 128)) => do
      v_12010 <- getRegister v_2595;
      v_12011 <- eval (extract v_12010 0 32);
      v_12012 <- evaluateAddress v_2594;
      v_12013 <- load v_12012 16;
      v_12014 <- eval (extract v_12013 0 32);
      v_12017 <- eval (extract v_12010 32 64);
      v_12018 <- eval (extract v_12013 32 64);
      v_12021 <- eval (extract v_12010 64 96);
      v_12022 <- eval (extract v_12013 64 96);
      v_12025 <- eval (extract v_12010 96 128);
      v_12026 <- eval (extract v_12013 96 128);
      setRegister (lhs.of_reg v_2595) (concat (mux (ugt v_12011 v_12014) v_12011 v_12014) (concat (mux (ugt v_12017 v_12018) v_12017 v_12018) (concat (mux (ugt v_12021 v_12022) v_12021 v_12022) (mux (ugt v_12025 v_12026) v_12025 v_12026))));
      pure ()
    pat_end

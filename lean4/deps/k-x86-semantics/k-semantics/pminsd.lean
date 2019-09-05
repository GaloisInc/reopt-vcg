def pminsd1 : instruction :=
  definst "pminsd" $ do
    pattern fun (v_2674 : reg (bv 128)) (v_2675 : reg (bv 128)) => do
      v_5134 <- getRegister v_2675;
      v_5135 <- eval (extract v_5134 0 32);
      v_5136 <- getRegister v_2674;
      v_5137 <- eval (extract v_5136 0 32);
      v_5140 <- eval (extract v_5134 32 64);
      v_5141 <- eval (extract v_5136 32 64);
      v_5144 <- eval (extract v_5134 64 96);
      v_5145 <- eval (extract v_5136 64 96);
      v_5148 <- eval (extract v_5134 96 128);
      v_5149 <- eval (extract v_5136 96 128);
      setRegister (lhs.of_reg v_2675) (concat (mux (slt v_5135 v_5137) v_5135 v_5137) (concat (mux (slt v_5140 v_5141) v_5140 v_5141) (concat (mux (slt v_5144 v_5145) v_5144 v_5145) (mux (slt v_5148 v_5149) v_5148 v_5149))));
      pure ()
    pat_end;
    pattern fun (v_2671 : Mem) (v_2670 : reg (bv 128)) => do
      v_12017 <- getRegister v_2670;
      v_12018 <- eval (extract v_12017 0 32);
      v_12019 <- evaluateAddress v_2671;
      v_12020 <- load v_12019 16;
      v_12021 <- eval (extract v_12020 0 32);
      v_12024 <- eval (extract v_12017 32 64);
      v_12025 <- eval (extract v_12020 32 64);
      v_12028 <- eval (extract v_12017 64 96);
      v_12029 <- eval (extract v_12020 64 96);
      v_12032 <- eval (extract v_12017 96 128);
      v_12033 <- eval (extract v_12020 96 128);
      setRegister (lhs.of_reg v_2670) (concat (mux (slt v_12018 v_12021) v_12018 v_12021) (concat (mux (slt v_12024 v_12025) v_12024 v_12025) (concat (mux (slt v_12028 v_12029) v_12028 v_12029) (mux (slt v_12032 v_12033) v_12032 v_12033))));
      pure ()
    pat_end

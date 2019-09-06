def pminud1 : instruction :=
  definst "pminud" $ do
    pattern fun (v_2729 : reg (bv 128)) (v_2730 : reg (bv 128)) => do
      v_5319 <- getRegister v_2730;
      v_5320 <- eval (extract v_5319 0 32);
      v_5321 <- getRegister v_2729;
      v_5322 <- eval (extract v_5321 0 32);
      v_5325 <- eval (extract v_5319 32 64);
      v_5326 <- eval (extract v_5321 32 64);
      v_5329 <- eval (extract v_5319 64 96);
      v_5330 <- eval (extract v_5321 64 96);
      v_5333 <- eval (extract v_5319 96 128);
      v_5334 <- eval (extract v_5321 96 128);
      setRegister (lhs.of_reg v_2730) (concat (mux (ult v_5320 v_5322) v_5320 v_5322) (concat (mux (ult v_5325 v_5326) v_5325 v_5326) (concat (mux (ult v_5329 v_5330) v_5329 v_5330) (mux (ult v_5333 v_5334) v_5333 v_5334))));
      pure ()
    pat_end;
    pattern fun (v_2725 : Mem) (v_2726 : reg (bv 128)) => do
      v_12142 <- getRegister v_2726;
      v_12143 <- eval (extract v_12142 0 32);
      v_12144 <- evaluateAddress v_2725;
      v_12145 <- load v_12144 16;
      v_12146 <- eval (extract v_12145 0 32);
      v_12149 <- eval (extract v_12142 32 64);
      v_12150 <- eval (extract v_12145 32 64);
      v_12153 <- eval (extract v_12142 64 96);
      v_12154 <- eval (extract v_12145 64 96);
      v_12157 <- eval (extract v_12142 96 128);
      v_12158 <- eval (extract v_12145 96 128);
      setRegister (lhs.of_reg v_2726) (concat (mux (ult v_12143 v_12146) v_12143 v_12146) (concat (mux (ult v_12149 v_12150) v_12149 v_12150) (concat (mux (ult v_12153 v_12154) v_12153 v_12154) (mux (ult v_12157 v_12158) v_12157 v_12158))));
      pure ()
    pat_end

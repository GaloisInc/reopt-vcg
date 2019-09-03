def pminsd1 : instruction :=
  definst "pminsd" $ do
    pattern fun (v_2625 : reg (bv 128)) (v_2626 : reg (bv 128)) => do
      v_5103 <- getRegister v_2626;
      v_5104 <- eval (extract v_5103 0 32);
      v_5105 <- getRegister v_2625;
      v_5106 <- eval (extract v_5105 0 32);
      v_5109 <- eval (extract v_5103 32 64);
      v_5110 <- eval (extract v_5105 32 64);
      v_5113 <- eval (extract v_5103 64 96);
      v_5114 <- eval (extract v_5105 64 96);
      v_5117 <- eval (extract v_5103 96 128);
      v_5118 <- eval (extract v_5105 96 128);
      setRegister (lhs.of_reg v_2626) (concat (mux (slt v_5104 v_5106) v_5104 v_5106) (concat (mux (slt v_5109 v_5110) v_5109 v_5110) (concat (mux (slt v_5113 v_5114) v_5113 v_5114) (mux (slt v_5117 v_5118) v_5117 v_5118))));
      pure ()
    pat_end;
    pattern fun (v_2621 : Mem) (v_2622 : reg (bv 128)) => do
      v_12159 <- getRegister v_2622;
      v_12160 <- eval (extract v_12159 0 32);
      v_12161 <- evaluateAddress v_2621;
      v_12162 <- load v_12161 16;
      v_12163 <- eval (extract v_12162 0 32);
      v_12166 <- eval (extract v_12159 32 64);
      v_12167 <- eval (extract v_12162 32 64);
      v_12170 <- eval (extract v_12159 64 96);
      v_12171 <- eval (extract v_12162 64 96);
      v_12174 <- eval (extract v_12159 96 128);
      v_12175 <- eval (extract v_12162 96 128);
      setRegister (lhs.of_reg v_2622) (concat (mux (slt v_12160 v_12163) v_12160 v_12163) (concat (mux (slt v_12166 v_12167) v_12166 v_12167) (concat (mux (slt v_12170 v_12171) v_12170 v_12171) (mux (slt v_12174 v_12175) v_12174 v_12175))));
      pure ()
    pat_end

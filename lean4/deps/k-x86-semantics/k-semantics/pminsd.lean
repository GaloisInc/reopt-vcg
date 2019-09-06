def pminsd1 : instruction :=
  definst "pminsd" $ do
    pattern fun (v_2702 : reg (bv 128)) (v_2703 : reg (bv 128)) => do
      v_5161 <- getRegister v_2703;
      v_5162 <- eval (extract v_5161 0 32);
      v_5163 <- getRegister v_2702;
      v_5164 <- eval (extract v_5163 0 32);
      v_5167 <- eval (extract v_5161 32 64);
      v_5168 <- eval (extract v_5163 32 64);
      v_5171 <- eval (extract v_5161 64 96);
      v_5172 <- eval (extract v_5163 64 96);
      v_5175 <- eval (extract v_5161 96 128);
      v_5176 <- eval (extract v_5163 96 128);
      setRegister (lhs.of_reg v_2703) (concat (mux (slt v_5162 v_5164) v_5162 v_5164) (concat (mux (slt v_5167 v_5168) v_5167 v_5168) (concat (mux (slt v_5171 v_5172) v_5171 v_5172) (mux (slt v_5175 v_5176) v_5175 v_5176))));
      pure ()
    pat_end;
    pattern fun (v_2698 : Mem) (v_2699 : reg (bv 128)) => do
      v_11993 <- getRegister v_2699;
      v_11994 <- eval (extract v_11993 0 32);
      v_11995 <- evaluateAddress v_2698;
      v_11996 <- load v_11995 16;
      v_11997 <- eval (extract v_11996 0 32);
      v_12000 <- eval (extract v_11993 32 64);
      v_12001 <- eval (extract v_11996 32 64);
      v_12004 <- eval (extract v_11993 64 96);
      v_12005 <- eval (extract v_11996 64 96);
      v_12008 <- eval (extract v_11993 96 128);
      v_12009 <- eval (extract v_11996 96 128);
      setRegister (lhs.of_reg v_2699) (concat (mux (slt v_11994 v_11997) v_11994 v_11997) (concat (mux (slt v_12000 v_12001) v_12000 v_12001) (concat (mux (slt v_12004 v_12005) v_12004 v_12005) (mux (slt v_12008 v_12009) v_12008 v_12009))));
      pure ()
    pat_end

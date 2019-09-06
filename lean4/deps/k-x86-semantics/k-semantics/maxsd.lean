def maxsd1 : instruction :=
  definst "maxsd" $ do
    pattern fun (v_3160 : reg (bv 128)) (v_3161 : reg (bv 128)) => do
      v_5625 <- getRegister v_3161;
      v_5627 <- eval (extract v_5625 64 128);
      v_5628 <- getRegister v_3160;
      v_5629 <- eval (extract v_5628 64 128);
      setRegister (lhs.of_reg v_3161) (concat (extract v_5625 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_5627 v_5629) (expression.bv_nat 1 1)) v_5627 v_5629));
      pure ()
    pat_end;
    pattern fun (v_3156 : Mem) (v_3157 : reg (bv 128)) => do
      v_8874 <- getRegister v_3157;
      v_8876 <- eval (extract v_8874 64 128);
      v_8877 <- evaluateAddress v_3156;
      v_8878 <- load v_8877 8;
      setRegister (lhs.of_reg v_3157) (concat (extract v_8874 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_8876 v_8878) (expression.bv_nat 1 1)) v_8876 v_8878));
      pure ()
    pat_end

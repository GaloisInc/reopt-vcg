def minsd1 : instruction :=
  definst "minsd" $ do
    pattern fun (v_3105 : reg (bv 128)) (v_3106 : reg (bv 128)) => do
      v_5853 <- getRegister v_3106;
      v_5855 <- eval (extract v_5853 64 128);
      v_5856 <- getRegister v_3105;
      v_5857 <- eval (extract v_5856 64 128);
      setRegister (lhs.of_reg v_3106) (concat (extract v_5853 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_5855 v_5857) (expression.bv_nat 1 1)) v_5855 v_5857));
      pure ()
    pat_end;
    pattern fun (v_3101 : Mem) (v_3102 : reg (bv 128)) => do
      v_9286 <- getRegister v_3102;
      v_9288 <- eval (extract v_9286 64 128);
      v_9289 <- evaluateAddress v_3101;
      v_9290 <- load v_9289 8;
      setRegister (lhs.of_reg v_3102) (concat (extract v_9286 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_9288 v_9290) (expression.bv_nat 1 1)) v_9288 v_9290));
      pure ()
    pat_end

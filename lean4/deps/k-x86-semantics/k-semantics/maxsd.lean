def maxsd1 : instruction :=
  definst "maxsd" $ do
    pattern fun (v_3069 : reg (bv 128)) (v_3070 : reg (bv 128)) => do
      v_5777 <- getRegister v_3070;
      v_5779 <- eval (extract v_5777 64 128);
      v_5780 <- getRegister v_3069;
      v_5781 <- eval (extract v_5780 64 128);
      setRegister (lhs.of_reg v_3070) (concat (extract v_5777 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_5779 v_5781) (expression.bv_nat 1 1)) v_5779 v_5781));
      pure ()
    pat_end;
    pattern fun (v_3065 : Mem) (v_3066 : reg (bv 128)) => do
      v_9224 <- getRegister v_3066;
      v_9226 <- eval (extract v_9224 64 128);
      v_9227 <- evaluateAddress v_3065;
      v_9228 <- load v_9227 8;
      setRegister (lhs.of_reg v_3066) (concat (extract v_9224 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9226 v_9228) (expression.bv_nat 1 1)) v_9226 v_9228));
      pure ()
    pat_end

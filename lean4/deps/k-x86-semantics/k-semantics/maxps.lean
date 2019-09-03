def maxps1 : instruction :=
  definst "maxps" $ do
    pattern fun (v_3073 : reg (bv 128)) (v_3074 : reg (bv 128)) => do
      v_6044 <- getRegister v_3074;
      v_6045 <- eval (extract v_6044 0 32);
      v_6046 <- getRegister v_3073;
      v_6047 <- eval (extract v_6046 0 32);
      v_6051 <- eval (extract v_6044 32 64);
      v_6052 <- eval (extract v_6046 32 64);
      v_6056 <- eval (extract v_6044 64 96);
      v_6057 <- eval (extract v_6046 64 96);
      v_6061 <- eval (extract v_6044 96 128);
      v_6062 <- eval (extract v_6046 96 128);
      setRegister (lhs.of_reg v_3074) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_6045 v_6047) (expression.bv_nat 1 1)) v_6045 v_6047) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_6051 v_6052) (expression.bv_nat 1 1)) v_6051 v_6052) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_6056 v_6057) (expression.bv_nat 1 1)) v_6056 v_6057) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_6061 v_6062) (expression.bv_nat 1 1)) v_6061 v_6062))));
      pure ()
    pat_end;
    pattern fun (v_3067 : Mem) (v_3069 : reg (bv 128)) => do
      v_9787 <- getRegister v_3069;
      v_9788 <- eval (extract v_9787 0 32);
      v_9789 <- evaluateAddress v_3067;
      v_9790 <- load v_9789 16;
      v_9791 <- eval (extract v_9790 0 32);
      v_9795 <- eval (extract v_9787 32 64);
      v_9796 <- eval (extract v_9790 32 64);
      v_9800 <- eval (extract v_9787 64 96);
      v_9801 <- eval (extract v_9790 64 96);
      v_9805 <- eval (extract v_9787 96 128);
      v_9806 <- eval (extract v_9790 96 128);
      setRegister (lhs.of_reg v_3069) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9788 v_9791) (expression.bv_nat 1 1)) v_9788 v_9791) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9795 v_9796) (expression.bv_nat 1 1)) v_9795 v_9796) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9800 v_9801) (expression.bv_nat 1 1)) v_9800 v_9801) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9805 v_9806) (expression.bv_nat 1 1)) v_9805 v_9806))));
      pure ()
    pat_end

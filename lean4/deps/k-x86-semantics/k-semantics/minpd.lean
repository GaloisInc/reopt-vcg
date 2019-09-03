def minpd1 : instruction :=
  definst "minpd" $ do
    pattern fun (v_3100 : reg (bv 128)) (v_3101 : reg (bv 128)) => do
      v_6102 <- getRegister v_3101;
      v_6103 <- eval (extract v_6102 0 64);
      v_6104 <- getRegister v_3100;
      v_6105 <- eval (extract v_6104 0 64);
      v_6109 <- eval (extract v_6102 64 128);
      v_6110 <- eval (extract v_6104 64 128);
      setRegister (lhs.of_reg v_3101) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_6103 v_6105) (expression.bv_nat 1 1)) v_6103 v_6105) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_6109 v_6110) (expression.bv_nat 1 1)) v_6109 v_6110));
      pure ()
    pat_end;
    pattern fun (v_3094 : Mem) (v_3096 : reg (bv 128)) => do
      v_9834 <- getRegister v_3096;
      v_9835 <- eval (extract v_9834 0 64);
      v_9836 <- evaluateAddress v_3094;
      v_9837 <- load v_9836 16;
      v_9838 <- eval (extract v_9837 0 64);
      v_9842 <- eval (extract v_9834 64 128);
      v_9843 <- eval (extract v_9837 64 128);
      setRegister (lhs.of_reg v_3096) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_9835 v_9838) (expression.bv_nat 1 1)) v_9835 v_9838) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_9842 v_9843) (expression.bv_nat 1 1)) v_9842 v_9843));
      pure ()
    pat_end

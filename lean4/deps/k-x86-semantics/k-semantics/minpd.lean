def minpd1 : instruction :=
  definst "minpd" $ do
    pattern fun (v_3152 : reg (bv 128)) (v_3153 : reg (bv 128)) => do
      v_5637 <- getRegister v_3153;
      v_5638 <- eval (extract v_5637 0 64);
      v_5639 <- getRegister v_3152;
      v_5640 <- eval (extract v_5639 0 64);
      v_5644 <- eval (extract v_5637 64 128);
      v_5645 <- eval (extract v_5639 64 128);
      setRegister (lhs.of_reg v_3153) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_5638 v_5640) (expression.bv_nat 1 1)) v_5638 v_5640) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_5644 v_5645) (expression.bv_nat 1 1)) v_5644 v_5645));
      pure ()
    pat_end;
    pattern fun (v_3147 : Mem) (v_3148 : reg (bv 128)) => do
      v_8884 <- getRegister v_3148;
      v_8885 <- eval (extract v_8884 0 64);
      v_8886 <- evaluateAddress v_3147;
      v_8887 <- load v_8886 16;
      v_8888 <- eval (extract v_8887 0 64);
      v_8892 <- eval (extract v_8884 64 128);
      v_8893 <- eval (extract v_8887 64 128);
      setRegister (lhs.of_reg v_3148) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_8885 v_8888) (expression.bv_nat 1 1)) v_8885 v_8888) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_8892 v_8893) (expression.bv_nat 1 1)) v_8892 v_8893));
      pure ()
    pat_end

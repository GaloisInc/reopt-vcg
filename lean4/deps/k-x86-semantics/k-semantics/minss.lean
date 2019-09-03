def minss1 : instruction :=
  definst "minss" $ do
    pattern fun (v_3127 : reg (bv 128)) (v_3128 : reg (bv 128)) => do
      v_6164 <- getRegister v_3128;
      v_6166 <- eval (extract v_6164 96 128);
      v_6167 <- getRegister v_3127;
      v_6168 <- eval (extract v_6167 96 128);
      setRegister (lhs.of_reg v_3128) (concat (extract v_6164 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_6166 v_6168) (expression.bv_nat 1 1)) v_6166 v_6168));
      pure ()
    pat_end;
    pattern fun (v_3121 : Mem) (v_3123 : reg (bv 128)) => do
      v_9886 <- getRegister v_3123;
      v_9888 <- eval (extract v_9886 96 128);
      v_9889 <- evaluateAddress v_3121;
      v_9890 <- load v_9889 4;
      setRegister (lhs.of_reg v_3123) (concat (extract v_9886 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_9888 v_9890) (expression.bv_nat 1 1)) v_9888 v_9890));
      pure ()
    pat_end

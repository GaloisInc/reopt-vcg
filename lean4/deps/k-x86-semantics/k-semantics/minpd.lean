def minpd1 : instruction :=
  definst "minpd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- eval (extract v_2 0 64);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      v_6 <- eval (extract v_5 0 64);
      v_7 <- eval (extract v_2 64 128);
      v_8 <- eval (extract v_5 64 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_3 v_6) (expression.bv_nat 1 1)) v_3 v_6) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_7 v_8) (expression.bv_nat 1 1)) v_7 v_8));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- eval (extract v_2 0 64);
      v_4 <- getRegister xmm_0;
      v_5 <- eval (extract v_4 0 64);
      v_6 <- eval (extract v_2 64 128);
      v_7 <- eval (extract v_4 64 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_3 v_5) (expression.bv_nat 1 1)) v_3 v_5) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_6 v_7) (expression.bv_nat 1 1)) v_6 v_7));
      pure ()
    pat_end

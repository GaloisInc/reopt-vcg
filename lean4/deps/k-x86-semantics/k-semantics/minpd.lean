def minpd1 : instruction :=
  definst "minpd" $ do
    pattern fun (v_3087 : reg (bv 128)) (v_3088 : reg (bv 128)) => do
      v_5805 <- getRegister v_3088;
      v_5806 <- eval (extract v_5805 0 64);
      v_5807 <- getRegister v_3087;
      v_5808 <- eval (extract v_5807 0 64);
      v_5812 <- eval (extract v_5805 64 128);
      v_5813 <- eval (extract v_5807 64 128);
      setRegister (lhs.of_reg v_3088) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_5806 v_5808) (expression.bv_nat 1 1)) v_5806 v_5808) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_5812 v_5813) (expression.bv_nat 1 1)) v_5812 v_5813));
      pure ()
    pat_end;
    pattern fun (v_3083 : Mem) (v_3084 : reg (bv 128)) => do
      v_9244 <- getRegister v_3084;
      v_9245 <- eval (extract v_9244 0 64);
      v_9246 <- evaluateAddress v_3083;
      v_9247 <- load v_9246 16;
      v_9248 <- eval (extract v_9247 0 64);
      v_9252 <- eval (extract v_9244 64 128);
      v_9253 <- eval (extract v_9247 64 128);
      setRegister (lhs.of_reg v_3084) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_9245 v_9248) (expression.bv_nat 1 1)) v_9245 v_9248) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_9252 v_9253) (expression.bv_nat 1 1)) v_9252 v_9253));
      pure ()
    pat_end

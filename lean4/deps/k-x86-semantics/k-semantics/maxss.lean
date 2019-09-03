def maxss1 : instruction :=
  definst "maxss" $ do
    pattern fun (v_3091 : reg (bv 128)) (v_3092 : reg (bv 128)) => do
      v_6088 <- getRegister v_3092;
      v_6090 <- eval (extract v_6088 96 128);
      v_6091 <- getRegister v_3091;
      v_6092 <- eval (extract v_6091 96 128);
      setRegister (lhs.of_reg v_3092) (concat (extract v_6088 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_6090 v_6092) (expression.bv_nat 1 1)) v_6090 v_6092));
      pure ()
    pat_end;
    pattern fun (v_3085 : Mem) (v_3087 : reg (bv 128)) => do
      v_9824 <- getRegister v_3087;
      v_9826 <- eval (extract v_9824 96 128);
      v_9827 <- evaluateAddress v_3085;
      v_9828 <- load v_9827 4;
      setRegister (lhs.of_reg v_3087) (concat (extract v_9824 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9826 v_9828) (expression.bv_nat 1 1)) v_9826 v_9828));
      pure ()
    pat_end

def minps1 : instruction :=
  definst "minps" $ do
    pattern fun (v_3109 : reg (bv 128)) (v_3110 : reg (bv 128)) => do
      v_6120 <- getRegister v_3110;
      v_6121 <- eval (extract v_6120 0 32);
      v_6122 <- getRegister v_3109;
      v_6123 <- eval (extract v_6122 0 32);
      v_6127 <- eval (extract v_6120 32 64);
      v_6128 <- eval (extract v_6122 32 64);
      v_6132 <- eval (extract v_6120 64 96);
      v_6133 <- eval (extract v_6122 64 96);
      v_6137 <- eval (extract v_6120 96 128);
      v_6138 <- eval (extract v_6122 96 128);
      setRegister (lhs.of_reg v_3110) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_6121 v_6123) (expression.bv_nat 1 1)) v_6121 v_6123) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_6127 v_6128) (expression.bv_nat 1 1)) v_6127 v_6128) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_6132 v_6133) (expression.bv_nat 1 1)) v_6132 v_6133) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_6137 v_6138) (expression.bv_nat 1 1)) v_6137 v_6138))));
      pure ()
    pat_end;
    pattern fun (v_3103 : Mem) (v_3105 : reg (bv 128)) => do
      v_9849 <- getRegister v_3105;
      v_9850 <- eval (extract v_9849 0 32);
      v_9851 <- evaluateAddress v_3103;
      v_9852 <- load v_9851 16;
      v_9853 <- eval (extract v_9852 0 32);
      v_9857 <- eval (extract v_9849 32 64);
      v_9858 <- eval (extract v_9852 32 64);
      v_9862 <- eval (extract v_9849 64 96);
      v_9863 <- eval (extract v_9852 64 96);
      v_9867 <- eval (extract v_9849 96 128);
      v_9868 <- eval (extract v_9852 96 128);
      setRegister (lhs.of_reg v_3105) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_9850 v_9853) (expression.bv_nat 1 1)) v_9850 v_9853) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_9857 v_9858) (expression.bv_nat 1 1)) v_9857 v_9858) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_9862 v_9863) (expression.bv_nat 1 1)) v_9862 v_9863) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_9867 v_9868) (expression.bv_nat 1 1)) v_9867 v_9868))));
      pure ()
    pat_end

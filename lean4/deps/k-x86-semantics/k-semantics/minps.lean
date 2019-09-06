def minps1 : instruction :=
  definst "minps" $ do
    pattern fun (v_3187 : reg (bv 128)) (v_3188 : reg (bv 128)) => do
      v_5671 <- getRegister v_3188;
      v_5672 <- eval (extract v_5671 0 32);
      v_5673 <- getRegister v_3187;
      v_5674 <- eval (extract v_5673 0 32);
      v_5678 <- eval (extract v_5671 32 64);
      v_5679 <- eval (extract v_5673 32 64);
      v_5683 <- eval (extract v_5671 64 96);
      v_5684 <- eval (extract v_5673 64 96);
      v_5688 <- eval (extract v_5671 96 128);
      v_5689 <- eval (extract v_5673 96 128);
      setRegister (lhs.of_reg v_3188) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_5672 v_5674) (expression.bv_nat 1 1)) v_5672 v_5674) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_5678 v_5679) (expression.bv_nat 1 1)) v_5678 v_5679) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_5683 v_5684) (expression.bv_nat 1 1)) v_5683 v_5684) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_5688 v_5689) (expression.bv_nat 1 1)) v_5688 v_5689))));
      pure ()
    pat_end;
    pattern fun (v_3183 : Mem) (v_3184 : reg (bv 128)) => do
      v_8909 <- getRegister v_3184;
      v_8910 <- eval (extract v_8909 0 32);
      v_8911 <- evaluateAddress v_3183;
      v_8912 <- load v_8911 16;
      v_8913 <- eval (extract v_8912 0 32);
      v_8917 <- eval (extract v_8909 32 64);
      v_8918 <- eval (extract v_8912 32 64);
      v_8922 <- eval (extract v_8909 64 96);
      v_8923 <- eval (extract v_8912 64 96);
      v_8927 <- eval (extract v_8909 96 128);
      v_8928 <- eval (extract v_8912 96 128);
      setRegister (lhs.of_reg v_3184) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_8910 v_8913) (expression.bv_nat 1 1)) v_8910 v_8913) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_8917 v_8918) (expression.bv_nat 1 1)) v_8917 v_8918) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_8922 v_8923) (expression.bv_nat 1 1)) v_8922 v_8923) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_8927 v_8928) (expression.bv_nat 1 1)) v_8927 v_8928))));
      pure ()
    pat_end

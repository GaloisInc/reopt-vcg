def minps1 : instruction :=
  definst "minps" $ do
    pattern fun (v_3161 : reg (bv 128)) (v_3162 : reg (bv 128)) => do
      v_5655 <- getRegister v_3162;
      v_5656 <- eval (extract v_5655 0 32);
      v_5657 <- getRegister v_3161;
      v_5658 <- eval (extract v_5657 0 32);
      v_5662 <- eval (extract v_5655 32 64);
      v_5663 <- eval (extract v_5657 32 64);
      v_5667 <- eval (extract v_5655 64 96);
      v_5668 <- eval (extract v_5657 64 96);
      v_5672 <- eval (extract v_5655 96 128);
      v_5673 <- eval (extract v_5657 96 128);
      setRegister (lhs.of_reg v_3162) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_5656 v_5658) (expression.bv_nat 1 1)) v_5656 v_5658) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_5662 v_5663) (expression.bv_nat 1 1)) v_5662 v_5663) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_5667 v_5668) (expression.bv_nat 1 1)) v_5667 v_5668) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_5672 v_5673) (expression.bv_nat 1 1)) v_5672 v_5673))));
      pure ()
    pat_end;
    pattern fun (v_3156 : Mem) (v_3157 : reg (bv 128)) => do
      v_8899 <- getRegister v_3157;
      v_8900 <- eval (extract v_8899 0 32);
      v_8901 <- evaluateAddress v_3156;
      v_8902 <- load v_8901 16;
      v_8903 <- eval (extract v_8902 0 32);
      v_8907 <- eval (extract v_8899 32 64);
      v_8908 <- eval (extract v_8902 32 64);
      v_8912 <- eval (extract v_8899 64 96);
      v_8913 <- eval (extract v_8902 64 96);
      v_8917 <- eval (extract v_8899 96 128);
      v_8918 <- eval (extract v_8902 96 128);
      setRegister (lhs.of_reg v_3157) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_8900 v_8903) (expression.bv_nat 1 1)) v_8900 v_8903) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_8907 v_8908) (expression.bv_nat 1 1)) v_8907 v_8908) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_8912 v_8913) (expression.bv_nat 1 1)) v_8912 v_8913) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_8917 v_8918) (expression.bv_nat 1 1)) v_8917 v_8918))));
      pure ()
    pat_end

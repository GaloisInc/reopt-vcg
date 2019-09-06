def minpd1 : instruction :=
  definst "minpd" $ do
    pattern fun (v_3178 : reg (bv 128)) (v_3179 : reg (bv 128)) => do
      v_5653 <- getRegister v_3179;
      v_5654 <- eval (extract v_5653 0 64);
      v_5655 <- getRegister v_3178;
      v_5656 <- eval (extract v_5655 0 64);
      v_5660 <- eval (extract v_5653 64 128);
      v_5661 <- eval (extract v_5655 64 128);
      setRegister (lhs.of_reg v_3179) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_5654 v_5656) (expression.bv_nat 1 1)) v_5654 v_5656) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_5660 v_5661) (expression.bv_nat 1 1)) v_5660 v_5661));
      pure ()
    pat_end;
    pattern fun (v_3174 : Mem) (v_3175 : reg (bv 128)) => do
      v_8894 <- getRegister v_3175;
      v_8895 <- eval (extract v_8894 0 64);
      v_8896 <- evaluateAddress v_3174;
      v_8897 <- load v_8896 16;
      v_8898 <- eval (extract v_8897 0 64);
      v_8902 <- eval (extract v_8894 64 128);
      v_8903 <- eval (extract v_8897 64 128);
      setRegister (lhs.of_reg v_3175) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_8895 v_8898) (expression.bv_nat 1 1)) v_8895 v_8898) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_8902 v_8903) (expression.bv_nat 1 1)) v_8902 v_8903));
      pure ()
    pat_end

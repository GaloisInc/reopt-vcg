def minss1 : instruction :=
  definst "minss" $ do
    pattern fun (v_3179 : reg (bv 128)) (v_3180 : reg (bv 128)) => do
      v_5699 <- getRegister v_3180;
      v_5701 <- eval (extract v_5699 96 128);
      v_5702 <- getRegister v_3179;
      v_5703 <- eval (extract v_5702 96 128);
      setRegister (lhs.of_reg v_3180) (concat (extract v_5699 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_5701 v_5703) (expression.bv_nat 1 1)) v_5701 v_5703));
      pure ()
    pat_end;
    pattern fun (v_3174 : Mem) (v_3175 : reg (bv 128)) => do
      v_8936 <- getRegister v_3175;
      v_8938 <- eval (extract v_8936 96 128);
      v_8939 <- evaluateAddress v_3174;
      v_8940 <- load v_8939 4;
      setRegister (lhs.of_reg v_3175) (concat (extract v_8936 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_8938 v_8940) (expression.bv_nat 1 1)) v_8938 v_8940));
      pure ()
    pat_end
